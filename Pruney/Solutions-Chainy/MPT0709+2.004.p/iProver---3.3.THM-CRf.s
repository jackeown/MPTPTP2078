%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:35 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 480 expanded)
%              Number of clauses        :   63 ( 158 expanded)
%              Number of leaves         :   13 (  97 expanded)
%              Depth                    :   25
%              Number of atoms          :  235 (1499 expanded)
%              Number of equality atoms :  102 ( 448 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f32])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f50,f40])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f33])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_593,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_585,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_587,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_847,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_585,c_587])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_596,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_594,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1670,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_596,c_594])).

cnf(c_2727,plain,
    ( k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = k10_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_847,c_1670])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_590,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_943,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_585,c_590])).

cnf(c_5,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1196,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK1,X0),X1)) = k10_relat_1(k7_relat_1(sK1,X1),X0) ),
    inference(superposition,[status(thm)],[c_5,c_847])).

cnf(c_1210,plain,
    ( k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0)),X1) = k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1196,c_847])).

cnf(c_1416,plain,
    ( k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0)),k2_relat_1(sK1)) = k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) ),
    inference(superposition,[status(thm)],[c_943,c_1210])).

cnf(c_2918,plain,
    ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_2727,c_1416])).

cnf(c_2920,plain,
    ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_2918,c_943])).

cnf(c_10,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_589,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2945,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2920,c_589])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_592,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1869,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_585,c_592])).

cnf(c_16,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_209,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_210,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_214,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_210,c_21,c_18])).

cnf(c_584,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_1673,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) = k10_relat_1(sK1,k9_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_584,c_594])).

cnf(c_2211,plain,
    ( k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))),X0) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_1673,c_847])).

cnf(c_2354,plain,
    ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))) ),
    inference(superposition,[status(thm)],[c_2211,c_1416])).

cnf(c_2356,plain,
    ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(light_normalisation,[status(thm)],[c_2354,c_943])).

cnf(c_2951,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2945,c_1869,c_2356])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_586,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_595,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2522,plain,
    ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_595])).

cnf(c_3310,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2951,c_2522])).

cnf(c_3339,plain,
    ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))) = sK0
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3310,c_594])).

cnf(c_3342,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) = sK0
    | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3339,c_847])).

cnf(c_3427,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_3342])).

cnf(c_22,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6161,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3427,c_22])).

cnf(c_6165,plain,
    ( r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0)))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6161,c_589])).

cnf(c_2212,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k10_relat_1(sK1,k9_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1673,c_1196])).

cnf(c_6174,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6165,c_1869,c_2212])).

cnf(c_17,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_693,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_694,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_708,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_709,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_7931,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6174,c_17,c_694,c_709])).

cnf(c_7936,plain,
    ( v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_7931])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7936,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.61/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.61/1.05  
% 0.61/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.61/1.05  
% 0.61/1.05  ------  iProver source info
% 0.61/1.05  
% 0.61/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.61/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.61/1.05  git: non_committed_changes: false
% 0.61/1.05  git: last_make_outside_of_git: false
% 0.61/1.05  
% 0.61/1.05  ------ 
% 0.61/1.05  
% 0.61/1.05  ------ Input Options
% 0.61/1.05  
% 0.61/1.05  --out_options                           all
% 0.61/1.05  --tptp_safe_out                         true
% 0.61/1.05  --problem_path                          ""
% 0.61/1.05  --include_path                          ""
% 0.61/1.05  --clausifier                            res/vclausify_rel
% 0.61/1.05  --clausifier_options                    --mode clausify
% 0.61/1.05  --stdin                                 false
% 0.61/1.05  --stats_out                             all
% 0.61/1.05  
% 0.61/1.05  ------ General Options
% 0.61/1.05  
% 0.61/1.05  --fof                                   false
% 0.61/1.05  --time_out_real                         305.
% 0.61/1.05  --time_out_virtual                      -1.
% 0.61/1.05  --symbol_type_check                     false
% 0.61/1.05  --clausify_out                          false
% 0.61/1.05  --sig_cnt_out                           false
% 0.61/1.05  --trig_cnt_out                          false
% 0.61/1.05  --trig_cnt_out_tolerance                1.
% 0.61/1.05  --trig_cnt_out_sk_spl                   false
% 0.61/1.05  --abstr_cl_out                          false
% 0.61/1.05  
% 0.61/1.05  ------ Global Options
% 0.61/1.05  
% 0.61/1.05  --schedule                              default
% 0.61/1.05  --add_important_lit                     false
% 0.61/1.05  --prop_solver_per_cl                    1000
% 0.61/1.05  --min_unsat_core                        false
% 0.61/1.05  --soft_assumptions                      false
% 0.61/1.05  --soft_lemma_size                       3
% 0.61/1.05  --prop_impl_unit_size                   0
% 0.61/1.05  --prop_impl_unit                        []
% 0.61/1.05  --share_sel_clauses                     true
% 0.61/1.05  --reset_solvers                         false
% 0.61/1.05  --bc_imp_inh                            [conj_cone]
% 0.61/1.05  --conj_cone_tolerance                   3.
% 0.61/1.05  --extra_neg_conj                        none
% 0.61/1.05  --large_theory_mode                     true
% 0.61/1.05  --prolific_symb_bound                   200
% 0.61/1.05  --lt_threshold                          2000
% 0.61/1.05  --clause_weak_htbl                      true
% 0.61/1.05  --gc_record_bc_elim                     false
% 0.61/1.05  
% 0.61/1.05  ------ Preprocessing Options
% 0.61/1.05  
% 0.61/1.05  --preprocessing_flag                    true
% 0.61/1.05  --time_out_prep_mult                    0.1
% 0.61/1.05  --splitting_mode                        input
% 0.61/1.05  --splitting_grd                         true
% 0.61/1.05  --splitting_cvd                         false
% 0.61/1.05  --splitting_cvd_svl                     false
% 0.61/1.05  --splitting_nvd                         32
% 0.61/1.05  --sub_typing                            true
% 0.61/1.05  --prep_gs_sim                           true
% 0.61/1.05  --prep_unflatten                        true
% 0.61/1.05  --prep_res_sim                          true
% 0.61/1.05  --prep_upred                            true
% 0.61/1.05  --prep_sem_filter                       exhaustive
% 0.61/1.05  --prep_sem_filter_out                   false
% 0.61/1.05  --pred_elim                             true
% 0.61/1.05  --res_sim_input                         true
% 0.61/1.05  --eq_ax_congr_red                       true
% 0.61/1.05  --pure_diseq_elim                       true
% 0.61/1.05  --brand_transform                       false
% 0.61/1.05  --non_eq_to_eq                          false
% 0.61/1.05  --prep_def_merge                        true
% 0.61/1.05  --prep_def_merge_prop_impl              false
% 0.61/1.05  --prep_def_merge_mbd                    true
% 0.61/1.05  --prep_def_merge_tr_red                 false
% 0.61/1.05  --prep_def_merge_tr_cl                  false
% 0.61/1.05  --smt_preprocessing                     true
% 0.61/1.05  --smt_ac_axioms                         fast
% 0.61/1.05  --preprocessed_out                      false
% 0.61/1.05  --preprocessed_stats                    false
% 0.61/1.05  
% 0.61/1.05  ------ Abstraction refinement Options
% 0.61/1.05  
% 0.61/1.05  --abstr_ref                             []
% 0.61/1.05  --abstr_ref_prep                        false
% 0.61/1.05  --abstr_ref_until_sat                   false
% 0.61/1.05  --abstr_ref_sig_restrict                funpre
% 0.61/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.61/1.05  --abstr_ref_under                       []
% 0.61/1.05  
% 0.61/1.05  ------ SAT Options
% 0.61/1.05  
% 0.61/1.05  --sat_mode                              false
% 0.61/1.05  --sat_fm_restart_options                ""
% 0.61/1.05  --sat_gr_def                            false
% 0.61/1.05  --sat_epr_types                         true
% 0.61/1.05  --sat_non_cyclic_types                  false
% 0.61/1.05  --sat_finite_models                     false
% 0.61/1.05  --sat_fm_lemmas                         false
% 0.61/1.05  --sat_fm_prep                           false
% 0.61/1.05  --sat_fm_uc_incr                        true
% 0.61/1.05  --sat_out_model                         small
% 0.61/1.05  --sat_out_clauses                       false
% 0.61/1.05  
% 0.61/1.05  ------ QBF Options
% 0.61/1.05  
% 0.61/1.05  --qbf_mode                              false
% 0.61/1.05  --qbf_elim_univ                         false
% 0.61/1.05  --qbf_dom_inst                          none
% 0.61/1.05  --qbf_dom_pre_inst                      false
% 0.61/1.05  --qbf_sk_in                             false
% 0.61/1.05  --qbf_pred_elim                         true
% 0.61/1.05  --qbf_split                             512
% 0.61/1.05  
% 0.61/1.05  ------ BMC1 Options
% 0.61/1.05  
% 0.61/1.05  --bmc1_incremental                      false
% 0.61/1.05  --bmc1_axioms                           reachable_all
% 0.61/1.05  --bmc1_min_bound                        0
% 0.61/1.05  --bmc1_max_bound                        -1
% 0.61/1.05  --bmc1_max_bound_default                -1
% 0.61/1.05  --bmc1_symbol_reachability              true
% 0.61/1.05  --bmc1_property_lemmas                  false
% 0.61/1.05  --bmc1_k_induction                      false
% 0.61/1.05  --bmc1_non_equiv_states                 false
% 0.61/1.05  --bmc1_deadlock                         false
% 0.61/1.05  --bmc1_ucm                              false
% 0.61/1.05  --bmc1_add_unsat_core                   none
% 0.61/1.05  --bmc1_unsat_core_children              false
% 0.61/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.61/1.05  --bmc1_out_stat                         full
% 0.61/1.05  --bmc1_ground_init                      false
% 0.61/1.05  --bmc1_pre_inst_next_state              false
% 0.61/1.05  --bmc1_pre_inst_state                   false
% 0.61/1.05  --bmc1_pre_inst_reach_state             false
% 0.61/1.05  --bmc1_out_unsat_core                   false
% 0.61/1.05  --bmc1_aig_witness_out                  false
% 0.61/1.05  --bmc1_verbose                          false
% 0.61/1.05  --bmc1_dump_clauses_tptp                false
% 0.61/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.61/1.05  --bmc1_dump_file                        -
% 0.61/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.61/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.61/1.05  --bmc1_ucm_extend_mode                  1
% 0.61/1.05  --bmc1_ucm_init_mode                    2
% 0.61/1.05  --bmc1_ucm_cone_mode                    none
% 0.61/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.61/1.05  --bmc1_ucm_relax_model                  4
% 0.61/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.61/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.61/1.05  --bmc1_ucm_layered_model                none
% 0.61/1.05  --bmc1_ucm_max_lemma_size               10
% 0.61/1.05  
% 0.61/1.05  ------ AIG Options
% 0.61/1.05  
% 0.61/1.05  --aig_mode                              false
% 0.61/1.05  
% 0.61/1.05  ------ Instantiation Options
% 0.61/1.05  
% 0.61/1.05  --instantiation_flag                    true
% 0.61/1.05  --inst_sos_flag                         false
% 0.61/1.05  --inst_sos_phase                        true
% 0.61/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.61/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.61/1.05  --inst_lit_sel_side                     num_symb
% 0.61/1.05  --inst_solver_per_active                1400
% 0.61/1.05  --inst_solver_calls_frac                1.
% 0.61/1.05  --inst_passive_queue_type               priority_queues
% 0.61/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.61/1.05  --inst_passive_queues_freq              [25;2]
% 0.61/1.05  --inst_dismatching                      true
% 0.61/1.05  --inst_eager_unprocessed_to_passive     true
% 0.61/1.05  --inst_prop_sim_given                   true
% 0.61/1.05  --inst_prop_sim_new                     false
% 0.61/1.05  --inst_subs_new                         false
% 0.61/1.05  --inst_eq_res_simp                      false
% 0.61/1.05  --inst_subs_given                       false
% 0.61/1.05  --inst_orphan_elimination               true
% 0.61/1.05  --inst_learning_loop_flag               true
% 0.61/1.05  --inst_learning_start                   3000
% 0.61/1.05  --inst_learning_factor                  2
% 0.61/1.05  --inst_start_prop_sim_after_learn       3
% 0.61/1.05  --inst_sel_renew                        solver
% 0.61/1.05  --inst_lit_activity_flag                true
% 0.61/1.05  --inst_restr_to_given                   false
% 0.61/1.05  --inst_activity_threshold               500
% 0.61/1.05  --inst_out_proof                        true
% 0.61/1.05  
% 0.61/1.05  ------ Resolution Options
% 0.61/1.05  
% 0.61/1.05  --resolution_flag                       true
% 0.61/1.05  --res_lit_sel                           adaptive
% 0.61/1.05  --res_lit_sel_side                      none
% 0.61/1.05  --res_ordering                          kbo
% 0.61/1.05  --res_to_prop_solver                    active
% 0.61/1.05  --res_prop_simpl_new                    false
% 0.61/1.05  --res_prop_simpl_given                  true
% 0.61/1.05  --res_passive_queue_type                priority_queues
% 0.61/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.61/1.05  --res_passive_queues_freq               [15;5]
% 0.61/1.05  --res_forward_subs                      full
% 0.61/1.05  --res_backward_subs                     full
% 0.61/1.05  --res_forward_subs_resolution           true
% 0.61/1.05  --res_backward_subs_resolution          true
% 0.61/1.05  --res_orphan_elimination                true
% 0.61/1.05  --res_time_limit                        2.
% 0.61/1.05  --res_out_proof                         true
% 0.61/1.05  
% 0.61/1.05  ------ Superposition Options
% 0.61/1.05  
% 0.61/1.05  --superposition_flag                    true
% 0.61/1.05  --sup_passive_queue_type                priority_queues
% 0.61/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.61/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.61/1.05  --demod_completeness_check              fast
% 0.61/1.05  --demod_use_ground                      true
% 0.61/1.05  --sup_to_prop_solver                    passive
% 0.61/1.05  --sup_prop_simpl_new                    true
% 0.61/1.05  --sup_prop_simpl_given                  true
% 0.61/1.05  --sup_fun_splitting                     false
% 0.61/1.05  --sup_smt_interval                      50000
% 0.61/1.05  
% 0.61/1.05  ------ Superposition Simplification Setup
% 0.61/1.05  
% 0.61/1.05  --sup_indices_passive                   []
% 0.61/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.61/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.61/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.61/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.61/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.61/1.05  --sup_full_bw                           [BwDemod]
% 0.61/1.05  --sup_immed_triv                        [TrivRules]
% 0.61/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.61/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.61/1.05  --sup_immed_bw_main                     []
% 0.61/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.61/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.61/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.61/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.61/1.05  
% 0.61/1.05  ------ Combination Options
% 0.61/1.05  
% 0.61/1.05  --comb_res_mult                         3
% 0.61/1.05  --comb_sup_mult                         2
% 0.61/1.05  --comb_inst_mult                        10
% 0.61/1.05  
% 0.61/1.05  ------ Debug Options
% 0.61/1.05  
% 0.61/1.05  --dbg_backtrace                         false
% 0.61/1.05  --dbg_dump_prop_clauses                 false
% 0.61/1.05  --dbg_dump_prop_clauses_file            -
% 0.61/1.05  --dbg_out_stat                          false
% 0.61/1.05  ------ Parsing...
% 0.61/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.61/1.05  
% 0.61/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.61/1.05  
% 0.61/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.61/1.05  
% 0.61/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.61/1.05  ------ Proving...
% 0.61/1.05  ------ Problem Properties 
% 0.61/1.05  
% 0.61/1.05  
% 0.61/1.05  clauses                                 18
% 0.61/1.05  conjectures                             3
% 0.61/1.05  EPR                                     4
% 0.61/1.05  Horn                                    18
% 0.61/1.05  unary                                   9
% 0.61/1.05  binary                                  7
% 0.61/1.05  lits                                    29
% 0.61/1.05  lits eq                                 9
% 0.61/1.05  fd_pure                                 0
% 0.61/1.05  fd_pseudo                               0
% 0.61/1.05  fd_cond                                 0
% 0.61/1.05  fd_pseudo_cond                          1
% 0.61/1.05  AC symbols                              0
% 0.61/1.05  
% 0.61/1.05  ------ Schedule dynamic 5 is on 
% 0.61/1.05  
% 0.61/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.61/1.05  
% 0.61/1.05  
% 0.61/1.05  ------ 
% 0.61/1.05  Current options:
% 0.61/1.05  ------ 
% 0.61/1.05  
% 0.61/1.05  ------ Input Options
% 0.61/1.05  
% 0.61/1.05  --out_options                           all
% 0.61/1.05  --tptp_safe_out                         true
% 0.61/1.05  --problem_path                          ""
% 0.61/1.05  --include_path                          ""
% 0.61/1.05  --clausifier                            res/vclausify_rel
% 0.61/1.05  --clausifier_options                    --mode clausify
% 0.61/1.05  --stdin                                 false
% 0.61/1.05  --stats_out                             all
% 0.61/1.05  
% 0.61/1.05  ------ General Options
% 0.61/1.05  
% 0.61/1.05  --fof                                   false
% 0.61/1.05  --time_out_real                         305.
% 0.61/1.05  --time_out_virtual                      -1.
% 0.61/1.05  --symbol_type_check                     false
% 0.61/1.05  --clausify_out                          false
% 0.61/1.05  --sig_cnt_out                           false
% 0.61/1.05  --trig_cnt_out                          false
% 0.61/1.05  --trig_cnt_out_tolerance                1.
% 0.61/1.05  --trig_cnt_out_sk_spl                   false
% 0.61/1.05  --abstr_cl_out                          false
% 0.61/1.05  
% 0.61/1.05  ------ Global Options
% 0.61/1.05  
% 0.61/1.05  --schedule                              default
% 0.61/1.05  --add_important_lit                     false
% 0.61/1.05  --prop_solver_per_cl                    1000
% 0.61/1.05  --min_unsat_core                        false
% 0.61/1.05  --soft_assumptions                      false
% 0.61/1.05  --soft_lemma_size                       3
% 0.61/1.05  --prop_impl_unit_size                   0
% 0.61/1.05  --prop_impl_unit                        []
% 0.61/1.05  --share_sel_clauses                     true
% 0.61/1.05  --reset_solvers                         false
% 0.61/1.05  --bc_imp_inh                            [conj_cone]
% 0.61/1.05  --conj_cone_tolerance                   3.
% 0.61/1.05  --extra_neg_conj                        none
% 0.61/1.05  --large_theory_mode                     true
% 0.61/1.05  --prolific_symb_bound                   200
% 0.61/1.05  --lt_threshold                          2000
% 0.61/1.05  --clause_weak_htbl                      true
% 0.61/1.05  --gc_record_bc_elim                     false
% 0.61/1.05  
% 0.61/1.05  ------ Preprocessing Options
% 0.61/1.05  
% 0.61/1.05  --preprocessing_flag                    true
% 0.61/1.05  --time_out_prep_mult                    0.1
% 0.61/1.05  --splitting_mode                        input
% 0.61/1.05  --splitting_grd                         true
% 0.61/1.05  --splitting_cvd                         false
% 0.61/1.05  --splitting_cvd_svl                     false
% 0.61/1.05  --splitting_nvd                         32
% 0.61/1.05  --sub_typing                            true
% 0.61/1.05  --prep_gs_sim                           true
% 0.61/1.05  --prep_unflatten                        true
% 0.61/1.05  --prep_res_sim                          true
% 0.61/1.05  --prep_upred                            true
% 0.61/1.05  --prep_sem_filter                       exhaustive
% 0.61/1.05  --prep_sem_filter_out                   false
% 0.61/1.05  --pred_elim                             true
% 0.61/1.05  --res_sim_input                         true
% 0.61/1.05  --eq_ax_congr_red                       true
% 0.61/1.05  --pure_diseq_elim                       true
% 0.61/1.05  --brand_transform                       false
% 0.61/1.05  --non_eq_to_eq                          false
% 0.61/1.05  --prep_def_merge                        true
% 0.61/1.05  --prep_def_merge_prop_impl              false
% 0.61/1.05  --prep_def_merge_mbd                    true
% 0.61/1.05  --prep_def_merge_tr_red                 false
% 0.61/1.05  --prep_def_merge_tr_cl                  false
% 0.61/1.05  --smt_preprocessing                     true
% 0.61/1.05  --smt_ac_axioms                         fast
% 0.61/1.05  --preprocessed_out                      false
% 0.61/1.05  --preprocessed_stats                    false
% 0.61/1.05  
% 0.61/1.05  ------ Abstraction refinement Options
% 0.61/1.05  
% 0.61/1.05  --abstr_ref                             []
% 0.61/1.05  --abstr_ref_prep                        false
% 0.61/1.05  --abstr_ref_until_sat                   false
% 0.61/1.05  --abstr_ref_sig_restrict                funpre
% 0.61/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.61/1.05  --abstr_ref_under                       []
% 0.61/1.05  
% 0.61/1.05  ------ SAT Options
% 0.61/1.05  
% 0.61/1.05  --sat_mode                              false
% 0.61/1.05  --sat_fm_restart_options                ""
% 0.61/1.05  --sat_gr_def                            false
% 0.61/1.05  --sat_epr_types                         true
% 0.61/1.05  --sat_non_cyclic_types                  false
% 0.61/1.05  --sat_finite_models                     false
% 0.61/1.05  --sat_fm_lemmas                         false
% 0.61/1.05  --sat_fm_prep                           false
% 0.61/1.05  --sat_fm_uc_incr                        true
% 0.61/1.05  --sat_out_model                         small
% 0.61/1.05  --sat_out_clauses                       false
% 0.61/1.05  
% 0.61/1.05  ------ QBF Options
% 0.61/1.05  
% 0.61/1.05  --qbf_mode                              false
% 0.61/1.05  --qbf_elim_univ                         false
% 0.61/1.05  --qbf_dom_inst                          none
% 0.61/1.05  --qbf_dom_pre_inst                      false
% 0.61/1.05  --qbf_sk_in                             false
% 0.61/1.05  --qbf_pred_elim                         true
% 0.61/1.05  --qbf_split                             512
% 0.61/1.05  
% 0.61/1.05  ------ BMC1 Options
% 0.61/1.05  
% 0.61/1.05  --bmc1_incremental                      false
% 0.61/1.05  --bmc1_axioms                           reachable_all
% 0.61/1.05  --bmc1_min_bound                        0
% 0.61/1.05  --bmc1_max_bound                        -1
% 0.61/1.05  --bmc1_max_bound_default                -1
% 0.61/1.05  --bmc1_symbol_reachability              true
% 0.61/1.05  --bmc1_property_lemmas                  false
% 0.61/1.05  --bmc1_k_induction                      false
% 0.61/1.05  --bmc1_non_equiv_states                 false
% 0.61/1.05  --bmc1_deadlock                         false
% 0.61/1.05  --bmc1_ucm                              false
% 0.61/1.05  --bmc1_add_unsat_core                   none
% 0.61/1.05  --bmc1_unsat_core_children              false
% 0.61/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.61/1.05  --bmc1_out_stat                         full
% 0.61/1.05  --bmc1_ground_init                      false
% 0.61/1.05  --bmc1_pre_inst_next_state              false
% 0.61/1.05  --bmc1_pre_inst_state                   false
% 0.61/1.05  --bmc1_pre_inst_reach_state             false
% 0.61/1.05  --bmc1_out_unsat_core                   false
% 0.61/1.05  --bmc1_aig_witness_out                  false
% 0.61/1.05  --bmc1_verbose                          false
% 0.61/1.05  --bmc1_dump_clauses_tptp                false
% 0.61/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.61/1.05  --bmc1_dump_file                        -
% 0.61/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.61/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.61/1.05  --bmc1_ucm_extend_mode                  1
% 0.61/1.05  --bmc1_ucm_init_mode                    2
% 0.61/1.05  --bmc1_ucm_cone_mode                    none
% 0.61/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.61/1.05  --bmc1_ucm_relax_model                  4
% 0.61/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.61/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.61/1.05  --bmc1_ucm_layered_model                none
% 0.61/1.05  --bmc1_ucm_max_lemma_size               10
% 0.61/1.05  
% 0.61/1.05  ------ AIG Options
% 0.61/1.05  
% 0.61/1.05  --aig_mode                              false
% 0.61/1.05  
% 0.61/1.05  ------ Instantiation Options
% 0.61/1.05  
% 0.61/1.05  --instantiation_flag                    true
% 0.61/1.05  --inst_sos_flag                         false
% 0.61/1.05  --inst_sos_phase                        true
% 0.61/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.61/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.61/1.05  --inst_lit_sel_side                     none
% 0.61/1.05  --inst_solver_per_active                1400
% 0.61/1.05  --inst_solver_calls_frac                1.
% 0.61/1.05  --inst_passive_queue_type               priority_queues
% 0.61/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.61/1.05  --inst_passive_queues_freq              [25;2]
% 0.61/1.05  --inst_dismatching                      true
% 0.61/1.05  --inst_eager_unprocessed_to_passive     true
% 0.61/1.05  --inst_prop_sim_given                   true
% 0.61/1.05  --inst_prop_sim_new                     false
% 0.61/1.05  --inst_subs_new                         false
% 0.61/1.05  --inst_eq_res_simp                      false
% 0.61/1.05  --inst_subs_given                       false
% 0.61/1.05  --inst_orphan_elimination               true
% 0.61/1.05  --inst_learning_loop_flag               true
% 0.61/1.05  --inst_learning_start                   3000
% 0.61/1.05  --inst_learning_factor                  2
% 0.61/1.05  --inst_start_prop_sim_after_learn       3
% 0.61/1.05  --inst_sel_renew                        solver
% 0.61/1.05  --inst_lit_activity_flag                true
% 0.61/1.05  --inst_restr_to_given                   false
% 0.61/1.05  --inst_activity_threshold               500
% 0.61/1.05  --inst_out_proof                        true
% 0.61/1.05  
% 0.61/1.05  ------ Resolution Options
% 0.61/1.05  
% 0.61/1.05  --resolution_flag                       false
% 0.61/1.05  --res_lit_sel                           adaptive
% 0.61/1.05  --res_lit_sel_side                      none
% 0.61/1.05  --res_ordering                          kbo
% 0.61/1.05  --res_to_prop_solver                    active
% 0.61/1.05  --res_prop_simpl_new                    false
% 0.61/1.05  --res_prop_simpl_given                  true
% 0.61/1.05  --res_passive_queue_type                priority_queues
% 0.61/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.61/1.05  --res_passive_queues_freq               [15;5]
% 0.61/1.05  --res_forward_subs                      full
% 0.61/1.05  --res_backward_subs                     full
% 0.61/1.05  --res_forward_subs_resolution           true
% 0.61/1.05  --res_backward_subs_resolution          true
% 0.61/1.05  --res_orphan_elimination                true
% 0.61/1.05  --res_time_limit                        2.
% 0.61/1.05  --res_out_proof                         true
% 0.61/1.05  
% 0.61/1.05  ------ Superposition Options
% 0.61/1.05  
% 0.61/1.05  --superposition_flag                    true
% 0.61/1.05  --sup_passive_queue_type                priority_queues
% 0.61/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.61/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.61/1.05  --demod_completeness_check              fast
% 0.61/1.05  --demod_use_ground                      true
% 0.61/1.05  --sup_to_prop_solver                    passive
% 0.61/1.05  --sup_prop_simpl_new                    true
% 0.61/1.05  --sup_prop_simpl_given                  true
% 0.61/1.05  --sup_fun_splitting                     false
% 0.61/1.05  --sup_smt_interval                      50000
% 0.61/1.05  
% 0.61/1.05  ------ Superposition Simplification Setup
% 0.61/1.05  
% 0.61/1.05  --sup_indices_passive                   []
% 0.61/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.61/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.61/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.61/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.61/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.61/1.05  --sup_full_bw                           [BwDemod]
% 0.61/1.05  --sup_immed_triv                        [TrivRules]
% 0.61/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.61/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.61/1.05  --sup_immed_bw_main                     []
% 0.61/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.61/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.61/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.61/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.61/1.05  
% 0.61/1.05  ------ Combination Options
% 0.61/1.05  
% 0.61/1.05  --comb_res_mult                         3
% 0.61/1.05  --comb_sup_mult                         2
% 0.61/1.05  --comb_inst_mult                        10
% 0.61/1.05  
% 0.61/1.05  ------ Debug Options
% 0.61/1.05  
% 0.61/1.05  --dbg_backtrace                         false
% 0.61/1.05  --dbg_dump_prop_clauses                 false
% 0.61/1.05  --dbg_dump_prop_clauses_file            -
% 0.61/1.05  --dbg_out_stat                          false
% 0.61/1.05  
% 0.61/1.05  
% 0.61/1.05  
% 0.61/1.05  
% 0.61/1.05  ------ Proving...
% 0.61/1.05  
% 0.61/1.05  
% 0.61/1.05  % SZS status Theorem for theBenchmark.p
% 0.61/1.05  
% 0.61/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 0.61/1.05  
% 0.61/1.05  fof(f6,axiom,(
% 0.61/1.05    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f20,plain,(
% 0.61/1.05    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.61/1.05    inference(ennf_transformation,[],[f6])).
% 0.61/1.05  
% 0.61/1.05  fof(f41,plain,(
% 0.61/1.05    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f20])).
% 0.61/1.05  
% 0.61/1.05  fof(f15,conjecture,(
% 0.61/1.05    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f16,negated_conjecture,(
% 0.61/1.05    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.61/1.05    inference(negated_conjecture,[],[f15])).
% 0.61/1.05  
% 0.61/1.05  fof(f28,plain,(
% 0.61/1.05    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.61/1.05    inference(ennf_transformation,[],[f16])).
% 0.61/1.05  
% 0.61/1.05  fof(f29,plain,(
% 0.61/1.05    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.61/1.05    inference(flattening,[],[f28])).
% 0.61/1.05  
% 0.61/1.05  fof(f32,plain,(
% 0.61/1.05    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.61/1.05    introduced(choice_axiom,[])).
% 0.61/1.05  
% 0.61/1.05  fof(f33,plain,(
% 0.61/1.05    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.61/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f32])).
% 0.61/1.05  
% 0.61/1.05  fof(f52,plain,(
% 0.61/1.05    v1_relat_1(sK1)),
% 0.61/1.05    inference(cnf_transformation,[],[f33])).
% 0.61/1.05  
% 0.61/1.05  fof(f13,axiom,(
% 0.61/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f25,plain,(
% 0.61/1.05    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 0.61/1.05    inference(ennf_transformation,[],[f13])).
% 0.61/1.05  
% 0.61/1.05  fof(f50,plain,(
% 0.61/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f25])).
% 0.61/1.05  
% 0.61/1.05  fof(f5,axiom,(
% 0.61/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f40,plain,(
% 0.61/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.61/1.05    inference(cnf_transformation,[],[f5])).
% 0.61/1.05  
% 0.61/1.05  fof(f58,plain,(
% 0.61/1.05    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 0.61/1.05    inference(definition_unfolding,[],[f50,f40])).
% 0.61/1.05  
% 0.61/1.05  fof(f1,axiom,(
% 0.61/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f30,plain,(
% 0.61/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.61/1.05    inference(nnf_transformation,[],[f1])).
% 0.61/1.05  
% 0.61/1.05  fof(f31,plain,(
% 0.61/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.61/1.05    inference(flattening,[],[f30])).
% 0.61/1.05  
% 0.61/1.05  fof(f35,plain,(
% 0.61/1.05    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.61/1.05    inference(cnf_transformation,[],[f31])).
% 0.61/1.05  
% 0.61/1.05  fof(f59,plain,(
% 0.61/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.61/1.05    inference(equality_resolution,[],[f35])).
% 0.61/1.05  
% 0.61/1.05  fof(f3,axiom,(
% 0.61/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f19,plain,(
% 0.61/1.05    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.61/1.05    inference(ennf_transformation,[],[f3])).
% 0.61/1.05  
% 0.61/1.05  fof(f38,plain,(
% 0.61/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f19])).
% 0.61/1.05  
% 0.61/1.05  fof(f57,plain,(
% 0.61/1.05    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.61/1.05    inference(definition_unfolding,[],[f38,f40])).
% 0.61/1.05  
% 0.61/1.05  fof(f9,axiom,(
% 0.61/1.05    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f23,plain,(
% 0.61/1.05    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.61/1.05    inference(ennf_transformation,[],[f9])).
% 0.61/1.05  
% 0.61/1.05  fof(f44,plain,(
% 0.61/1.05    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f23])).
% 0.61/1.05  
% 0.61/1.05  fof(f4,axiom,(
% 0.61/1.05    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f39,plain,(
% 0.61/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f4])).
% 0.61/1.05  
% 0.61/1.05  fof(f10,axiom,(
% 0.61/1.05    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f24,plain,(
% 0.61/1.05    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.61/1.05    inference(ennf_transformation,[],[f10])).
% 0.61/1.05  
% 0.61/1.05  fof(f45,plain,(
% 0.61/1.05    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f24])).
% 0.61/1.05  
% 0.61/1.05  fof(f7,axiom,(
% 0.61/1.05    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f21,plain,(
% 0.61/1.05    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.61/1.05    inference(ennf_transformation,[],[f7])).
% 0.61/1.05  
% 0.61/1.05  fof(f42,plain,(
% 0.61/1.05    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f21])).
% 0.61/1.05  
% 0.61/1.05  fof(f14,axiom,(
% 0.61/1.05    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f26,plain,(
% 0.61/1.05    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.61/1.05    inference(ennf_transformation,[],[f14])).
% 0.61/1.05  
% 0.61/1.05  fof(f27,plain,(
% 0.61/1.05    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.61/1.05    inference(flattening,[],[f26])).
% 0.61/1.05  
% 0.61/1.05  fof(f51,plain,(
% 0.61/1.05    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f27])).
% 0.61/1.05  
% 0.61/1.05  fof(f53,plain,(
% 0.61/1.05    v1_funct_1(sK1)),
% 0.61/1.05    inference(cnf_transformation,[],[f33])).
% 0.61/1.05  
% 0.61/1.05  fof(f55,plain,(
% 0.61/1.05    v2_funct_1(sK1)),
% 0.61/1.05    inference(cnf_transformation,[],[f33])).
% 0.61/1.05  
% 0.61/1.05  fof(f54,plain,(
% 0.61/1.05    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.61/1.05    inference(cnf_transformation,[],[f33])).
% 0.61/1.05  
% 0.61/1.05  fof(f2,axiom,(
% 0.61/1.05    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.61/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.61/1.05  
% 0.61/1.05  fof(f17,plain,(
% 0.61/1.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.61/1.05    inference(ennf_transformation,[],[f2])).
% 0.61/1.05  
% 0.61/1.05  fof(f18,plain,(
% 0.61/1.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.61/1.05    inference(flattening,[],[f17])).
% 0.61/1.05  
% 0.61/1.05  fof(f37,plain,(
% 0.61/1.05    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f18])).
% 0.61/1.05  
% 0.61/1.05  fof(f56,plain,(
% 0.61/1.05    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 0.61/1.05    inference(cnf_transformation,[],[f33])).
% 0.61/1.05  
% 0.61/1.05  fof(f36,plain,(
% 0.61/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.61/1.05    inference(cnf_transformation,[],[f31])).
% 0.61/1.05  
% 0.61/1.05  cnf(c_6,plain,
% 0.61/1.05      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 0.61/1.05      inference(cnf_transformation,[],[f41]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_593,plain,
% 0.61/1.05      ( v1_relat_1(X0) != iProver_top
% 0.61/1.05      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_21,negated_conjecture,
% 0.61/1.05      ( v1_relat_1(sK1) ),
% 0.61/1.05      inference(cnf_transformation,[],[f52]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_585,plain,
% 0.61/1.05      ( v1_relat_1(sK1) = iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_15,plain,
% 0.61/1.05      ( ~ v1_relat_1(X0)
% 0.61/1.05      | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 0.61/1.05      inference(cnf_transformation,[],[f58]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_587,plain,
% 0.61/1.05      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 0.61/1.05      | v1_relat_1(X1) != iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_847,plain,
% 0.61/1.05      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_585,c_587]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_1,plain,
% 0.61/1.05      ( r1_tarski(X0,X0) ),
% 0.61/1.05      inference(cnf_transformation,[],[f59]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_596,plain,
% 0.61/1.05      ( r1_tarski(X0,X0) = iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_4,plain,
% 0.61/1.05      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 0.61/1.05      inference(cnf_transformation,[],[f57]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_594,plain,
% 0.61/1.05      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 0.61/1.05      | r1_tarski(X0,X1) != iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_1670,plain,
% 0.61/1.05      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_596,c_594]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2727,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = k10_relat_1(sK1,X0) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_847,c_1670]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_9,plain,
% 0.61/1.05      ( ~ v1_relat_1(X0)
% 0.61/1.05      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 0.61/1.05      inference(cnf_transformation,[],[f44]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_590,plain,
% 0.61/1.05      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 0.61/1.05      | v1_relat_1(X0) != iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_943,plain,
% 0.61/1.05      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_585,c_590]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_5,plain,
% 0.61/1.05      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 0.61/1.05      inference(cnf_transformation,[],[f39]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_1196,plain,
% 0.61/1.05      ( k1_setfam_1(k2_tarski(k10_relat_1(sK1,X0),X1)) = k10_relat_1(k7_relat_1(sK1,X1),X0) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_5,c_847]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_1210,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0)),X1) = k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X1)),X0) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_1196,c_847]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_1416,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0)),k2_relat_1(sK1)) = k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_943,c_1210]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2918,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_2727,c_1416]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2920,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 0.61/1.05      inference(light_normalisation,[status(thm)],[c_2918,c_943]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_10,plain,
% 0.61/1.05      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
% 0.61/1.05      | ~ v1_relat_1(X0) ),
% 0.61/1.05      inference(cnf_transformation,[],[f45]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_589,plain,
% 0.61/1.05      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
% 0.61/1.05      | v1_relat_1(X0) != iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2945,plain,
% 0.61/1.05      ( r1_tarski(k1_relat_1(sK1),k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))))) = iProver_top
% 0.61/1.05      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_2920,c_589]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_7,plain,
% 0.61/1.05      ( ~ v1_relat_1(X0)
% 0.61/1.05      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 0.61/1.05      inference(cnf_transformation,[],[f42]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_592,plain,
% 0.61/1.05      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 0.61/1.05      | v1_relat_1(X0) != iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_1869,plain,
% 0.61/1.05      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_585,c_592]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_16,plain,
% 0.61/1.05      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 0.61/1.05      | ~ v1_funct_1(X0)
% 0.61/1.05      | ~ v2_funct_1(X0)
% 0.61/1.05      | ~ v1_relat_1(X0) ),
% 0.61/1.05      inference(cnf_transformation,[],[f51]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_20,negated_conjecture,
% 0.61/1.05      ( v1_funct_1(sK1) ),
% 0.61/1.05      inference(cnf_transformation,[],[f53]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_209,plain,
% 0.61/1.05      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 0.61/1.05      | ~ v2_funct_1(X0)
% 0.61/1.05      | ~ v1_relat_1(X0)
% 0.61/1.05      | sK1 != X0 ),
% 0.61/1.05      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_210,plain,
% 0.61/1.05      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
% 0.61/1.05      | ~ v2_funct_1(sK1)
% 0.61/1.05      | ~ v1_relat_1(sK1) ),
% 0.61/1.05      inference(unflattening,[status(thm)],[c_209]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_18,negated_conjecture,
% 0.61/1.05      ( v2_funct_1(sK1) ),
% 0.61/1.05      inference(cnf_transformation,[],[f55]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_214,plain,
% 0.61/1.05      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
% 0.61/1.05      inference(global_propositional_subsumption,
% 0.61/1.05                [status(thm)],
% 0.61/1.05                [c_210,c_21,c_18]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_584,plain,
% 0.61/1.05      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_1673,plain,
% 0.61/1.05      ( k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) = k10_relat_1(sK1,k9_relat_1(sK1,X0)) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_584,c_594]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2211,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))),X0) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_1673,c_847]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2354,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_2211,c_1416]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2356,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k1_relat_1(sK1))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) ),
% 0.61/1.05      inference(light_normalisation,[status(thm)],[c_2354,c_943]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2951,plain,
% 0.61/1.05      ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) = iProver_top
% 0.61/1.05      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 0.61/1.05      inference(demodulation,[status(thm)],[c_2945,c_1869,c_2356]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_19,negated_conjecture,
% 0.61/1.05      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 0.61/1.05      inference(cnf_transformation,[],[f54]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_586,plain,
% 0.61/1.05      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_3,plain,
% 0.61/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 0.61/1.05      inference(cnf_transformation,[],[f37]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_595,plain,
% 0.61/1.05      ( r1_tarski(X0,X1) != iProver_top
% 0.61/1.05      | r1_tarski(X1,X2) != iProver_top
% 0.61/1.05      | r1_tarski(X0,X2) = iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2522,plain,
% 0.61/1.05      ( r1_tarski(k1_relat_1(sK1),X0) != iProver_top
% 0.61/1.05      | r1_tarski(sK0,X0) = iProver_top ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_586,c_595]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_3310,plain,
% 0.61/1.05      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) = iProver_top
% 0.61/1.05      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_2951,c_2522]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_3339,plain,
% 0.61/1.05      ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))) = sK0
% 0.61/1.05      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_3310,c_594]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_3342,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) = sK0
% 0.61/1.05      | v1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) != iProver_top ),
% 0.61/1.05      inference(demodulation,[status(thm)],[c_3339,c_847]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_3427,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) = sK0
% 0.61/1.05      | v1_relat_1(sK1) != iProver_top ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_593,c_3342]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_22,plain,
% 0.61/1.05      ( v1_relat_1(sK1) = iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_6161,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) = sK0 ),
% 0.61/1.05      inference(global_propositional_subsumption,
% 0.61/1.05                [status(thm)],
% 0.61/1.05                [c_3427,c_22]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_6165,plain,
% 0.61/1.05      ( r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0)))) = iProver_top
% 0.61/1.05      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_6161,c_589]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_2212,plain,
% 0.61/1.05      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k10_relat_1(sK1,k9_relat_1(sK1,X0)) ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_1673,c_1196]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_6174,plain,
% 0.61/1.05      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top
% 0.61/1.05      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 0.61/1.05      inference(demodulation,[status(thm)],[c_6165,c_1869,c_2212]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_17,negated_conjecture,
% 0.61/1.05      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 0.61/1.05      inference(cnf_transformation,[],[f56]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_0,plain,
% 0.61/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 0.61/1.05      inference(cnf_transformation,[],[f36]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_693,plain,
% 0.61/1.05      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 0.61/1.05      | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 0.61/1.05      | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
% 0.61/1.05      inference(instantiation,[status(thm)],[c_0]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_694,plain,
% 0.61/1.05      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0
% 0.61/1.05      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) != iProver_top
% 0.61/1.05      | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_708,plain,
% 0.61/1.05      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
% 0.61/1.05      inference(instantiation,[status(thm)],[c_214]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_709,plain,
% 0.61/1.05      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) = iProver_top ),
% 0.61/1.05      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_7931,plain,
% 0.61/1.05      ( v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 0.61/1.05      inference(global_propositional_subsumption,
% 0.61/1.05                [status(thm)],
% 0.61/1.05                [c_6174,c_17,c_694,c_709]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(c_7936,plain,
% 0.61/1.05      ( v1_relat_1(sK1) != iProver_top ),
% 0.61/1.05      inference(superposition,[status(thm)],[c_593,c_7931]) ).
% 0.61/1.05  
% 0.61/1.05  cnf(contradiction,plain,
% 0.61/1.05      ( $false ),
% 0.61/1.05      inference(minisat,[status(thm)],[c_7936,c_22]) ).
% 0.61/1.05  
% 0.61/1.05  
% 0.61/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 0.61/1.05  
% 0.61/1.05  ------                               Statistics
% 0.61/1.05  
% 0.61/1.05  ------ General
% 0.61/1.05  
% 0.61/1.05  abstr_ref_over_cycles:                  0
% 0.61/1.05  abstr_ref_under_cycles:                 0
% 0.61/1.05  gc_basic_clause_elim:                   0
% 0.61/1.05  forced_gc_time:                         0
% 0.61/1.05  parsing_time:                           0.006
% 0.61/1.05  unif_index_cands_time:                  0.
% 0.61/1.05  unif_index_add_time:                    0.
% 0.61/1.05  orderings_time:                         0.
% 0.61/1.05  out_proof_time:                         0.008
% 0.61/1.05  total_time:                             0.223
% 0.61/1.05  num_of_symbols:                         45
% 0.61/1.05  num_of_terms:                           7012
% 0.61/1.05  
% 0.61/1.05  ------ Preprocessing
% 0.61/1.05  
% 0.61/1.05  num_of_splits:                          0
% 0.61/1.05  num_of_split_atoms:                     0
% 0.61/1.05  num_of_reused_defs:                     0
% 0.61/1.05  num_eq_ax_congr_red:                    12
% 0.61/1.05  num_of_sem_filtered_clauses:            1
% 0.61/1.05  num_of_subtypes:                        0
% 0.61/1.05  monotx_restored_types:                  0
% 0.61/1.05  sat_num_of_epr_types:                   0
% 0.61/1.05  sat_num_of_non_cyclic_types:            0
% 0.61/1.05  sat_guarded_non_collapsed_types:        0
% 0.61/1.05  num_pure_diseq_elim:                    0
% 0.61/1.05  simp_replaced_by:                       0
% 0.61/1.05  res_preprocessed:                       96
% 0.61/1.05  prep_upred:                             0
% 0.61/1.05  prep_unflattend:                        1
% 0.61/1.05  smt_new_axioms:                         0
% 0.61/1.05  pred_elim_cands:                        2
% 0.61/1.05  pred_elim:                              2
% 0.61/1.05  pred_elim_cl:                           3
% 0.61/1.05  pred_elim_cycles:                       4
% 0.61/1.05  merged_defs:                            0
% 0.61/1.05  merged_defs_ncl:                        0
% 0.61/1.05  bin_hyper_res:                          0
% 0.61/1.05  prep_cycles:                            4
% 0.61/1.05  pred_elim_time:                         0.
% 0.61/1.05  splitting_time:                         0.
% 0.61/1.05  sem_filter_time:                        0.
% 0.61/1.05  monotx_time:                            0.
% 0.61/1.05  subtype_inf_time:                       0.
% 0.61/1.05  
% 0.61/1.05  ------ Problem properties
% 0.61/1.05  
% 0.61/1.05  clauses:                                18
% 0.61/1.05  conjectures:                            3
% 0.61/1.05  epr:                                    4
% 0.61/1.05  horn:                                   18
% 0.61/1.05  ground:                                 3
% 0.61/1.05  unary:                                  9
% 0.61/1.05  binary:                                 7
% 0.61/1.05  lits:                                   29
% 0.61/1.05  lits_eq:                                9
% 0.61/1.05  fd_pure:                                0
% 0.61/1.05  fd_pseudo:                              0
% 0.61/1.05  fd_cond:                                0
% 0.61/1.05  fd_pseudo_cond:                         1
% 0.61/1.05  ac_symbols:                             0
% 0.61/1.05  
% 0.61/1.05  ------ Propositional Solver
% 0.61/1.05  
% 0.61/1.05  prop_solver_calls:                      32
% 0.61/1.05  prop_fast_solver_calls:                 483
% 0.61/1.05  smt_solver_calls:                       0
% 0.61/1.05  smt_fast_solver_calls:                  0
% 0.61/1.05  prop_num_of_clauses:                    3318
% 0.61/1.05  prop_preprocess_simplified:             7612
% 0.61/1.05  prop_fo_subsumed:                       6
% 0.61/1.05  prop_solver_time:                       0.
% 0.61/1.05  smt_solver_time:                        0.
% 0.61/1.05  smt_fast_solver_time:                   0.
% 0.61/1.05  prop_fast_solver_time:                  0.
% 0.61/1.05  prop_unsat_core_time:                   0.
% 0.61/1.05  
% 0.61/1.05  ------ QBF
% 0.61/1.05  
% 0.61/1.05  qbf_q_res:                              0
% 0.61/1.05  qbf_num_tautologies:                    0
% 0.61/1.05  qbf_prep_cycles:                        0
% 0.61/1.05  
% 0.61/1.05  ------ BMC1
% 0.61/1.05  
% 0.61/1.05  bmc1_current_bound:                     -1
% 0.61/1.05  bmc1_last_solved_bound:                 -1
% 0.61/1.05  bmc1_unsat_core_size:                   -1
% 0.61/1.05  bmc1_unsat_core_parents_size:           -1
% 0.61/1.05  bmc1_merge_next_fun:                    0
% 0.61/1.05  bmc1_unsat_core_clauses_time:           0.
% 0.61/1.05  
% 0.61/1.05  ------ Instantiation
% 0.61/1.05  
% 0.61/1.05  inst_num_of_clauses:                    1111
% 0.61/1.05  inst_num_in_passive:                    615
% 0.61/1.05  inst_num_in_active:                     439
% 0.61/1.05  inst_num_in_unprocessed:                57
% 0.61/1.05  inst_num_of_loops:                      450
% 0.61/1.05  inst_num_of_learning_restarts:          0
% 0.61/1.05  inst_num_moves_active_passive:          6
% 0.61/1.05  inst_lit_activity:                      0
% 0.61/1.05  inst_lit_activity_moves:                0
% 0.61/1.05  inst_num_tautologies:                   0
% 0.61/1.05  inst_num_prop_implied:                  0
% 0.61/1.05  inst_num_existing_simplified:           0
% 0.61/1.05  inst_num_eq_res_simplified:             0
% 0.61/1.05  inst_num_child_elim:                    0
% 0.61/1.05  inst_num_of_dismatching_blockings:      245
% 0.61/1.05  inst_num_of_non_proper_insts:           1032
% 0.61/1.05  inst_num_of_duplicates:                 0
% 0.61/1.05  inst_inst_num_from_inst_to_res:         0
% 0.61/1.05  inst_dismatching_checking_time:         0.
% 0.61/1.05  
% 0.61/1.05  ------ Resolution
% 0.61/1.05  
% 0.61/1.05  res_num_of_clauses:                     0
% 0.61/1.05  res_num_in_passive:                     0
% 0.61/1.05  res_num_in_active:                      0
% 0.61/1.05  res_num_of_loops:                       100
% 0.61/1.05  res_forward_subset_subsumed:            153
% 0.61/1.05  res_backward_subset_subsumed:           0
% 0.61/1.05  res_forward_subsumed:                   0
% 0.61/1.05  res_backward_subsumed:                  0
% 0.61/1.05  res_forward_subsumption_resolution:     0
% 0.61/1.05  res_backward_subsumption_resolution:    0
% 0.61/1.05  res_clause_to_clause_subsumption:       805
% 0.61/1.05  res_orphan_elimination:                 0
% 0.61/1.05  res_tautology_del:                      124
% 0.61/1.05  res_num_eq_res_simplified:              0
% 0.61/1.05  res_num_sel_changes:                    0
% 0.61/1.05  res_moves_from_active_to_pass:          0
% 0.61/1.05  
% 0.61/1.05  ------ Superposition
% 0.61/1.05  
% 0.61/1.05  sup_time_total:                         0.
% 0.61/1.05  sup_time_generating:                    0.
% 0.61/1.05  sup_time_sim_full:                      0.
% 0.61/1.05  sup_time_sim_immed:                     0.
% 0.61/1.05  
% 0.61/1.05  sup_num_of_clauses:                     236
% 0.61/1.05  sup_num_in_active:                      73
% 0.61/1.05  sup_num_in_passive:                     163
% 0.61/1.05  sup_num_of_loops:                       89
% 0.61/1.05  sup_fw_superposition:                   263
% 0.61/1.05  sup_bw_superposition:                   243
% 0.61/1.05  sup_immediate_simplified:               146
% 0.61/1.05  sup_given_eliminated:                   0
% 0.61/1.05  comparisons_done:                       0
% 0.61/1.05  comparisons_avoided:                    0
% 0.61/1.05  
% 0.61/1.05  ------ Simplifications
% 0.61/1.05  
% 0.61/1.05  
% 0.61/1.05  sim_fw_subset_subsumed:                 3
% 0.61/1.05  sim_bw_subset_subsumed:                 1
% 0.61/1.05  sim_fw_subsumed:                        39
% 0.61/1.05  sim_bw_subsumed:                        5
% 0.61/1.05  sim_fw_subsumption_res:                 0
% 0.61/1.05  sim_bw_subsumption_res:                 0
% 0.61/1.05  sim_tautology_del:                      3
% 0.61/1.05  sim_eq_tautology_del:                   12
% 0.61/1.05  sim_eq_res_simp:                        0
% 0.61/1.05  sim_fw_demodulated:                     49
% 0.61/1.05  sim_bw_demodulated:                     17
% 0.61/1.05  sim_light_normalised:                   80
% 0.61/1.05  sim_joinable_taut:                      0
% 0.61/1.05  sim_joinable_simp:                      0
% 0.61/1.05  sim_ac_normalised:                      0
% 0.61/1.05  sim_smt_subsumption:                    0
% 0.61/1.05  
%------------------------------------------------------------------------------
