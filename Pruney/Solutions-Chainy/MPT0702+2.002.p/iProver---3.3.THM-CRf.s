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
% DateTime   : Thu Dec  3 11:52:07 EST 2020

% Result     : Theorem 23.93s
% Output     : CNFRefutation 23.93s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 840 expanded)
%              Number of clauses        :   61 ( 224 expanded)
%              Number of leaves         :   12 ( 210 expanded)
%              Depth                    :   24
%              Number of atoms          :  205 (2671 expanded)
%              Number of equality atoms :   73 ( 499 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f38,f34,f34])).

fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f34,f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_585,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_590,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1682,plain,
    ( k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_585,c_590])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_13,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_213,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_214,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_218,plain,
    ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_214,c_17,c_16])).

cnf(c_2179,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1682,c_218])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2180,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k9_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_2179,c_6])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_588,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1051,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_218,c_588])).

cnf(c_1685,plain,
    ( k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1051,c_590])).

cnf(c_7,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1118,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_1926,plain,
    ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1118,c_218])).

cnf(c_2442,plain,
    ( k4_xboole_0(k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),k4_xboole_0(k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),k9_relat_1(sK2,X2))) = k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) ),
    inference(superposition,[status(thm)],[c_1926,c_218])).

cnf(c_2470,plain,
    ( k4_xboole_0(k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),k4_xboole_0(k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),k9_relat_1(sK2,X2))) = k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) ),
    inference(demodulation,[status(thm)],[c_2442,c_8])).

cnf(c_2471,plain,
    ( k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X2))) = k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) ),
    inference(light_normalisation,[status(thm)],[c_2470,c_218])).

cnf(c_41277,plain,
    ( k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1685,c_2471])).

cnf(c_1925,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1118,c_588])).

cnf(c_1927,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1925,c_8])).

cnf(c_1995,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1927,c_590])).

cnf(c_41306,plain,
    ( k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)) = k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_41277,c_1995])).

cnf(c_41307,plain,
    ( k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k9_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_41306,c_6])).

cnf(c_64341,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2180,c_41307])).

cnf(c_65470,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k9_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_64341,c_6])).

cnf(c_11,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_198,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_199,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_203,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_199,c_17,c_16])).

cnf(c_584,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_1683,plain,
    ( k4_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_584,c_590])).

cnf(c_1906,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1118,c_8])).

cnf(c_31822,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k4_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1683,c_1906])).

cnf(c_31896,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_31822,c_6])).

cnf(c_65582,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) ),
    inference(superposition,[status(thm)],[c_65470,c_31896])).

cnf(c_65875,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(demodulation,[status(thm)],[c_65582,c_65470])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_586,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_227,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_228,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
    | ~ r1_tarski(X0,k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_583,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_1684,plain,
    ( k4_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_590])).

cnf(c_37550,plain,
    ( k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_586,c_1684])).

cnf(c_38955,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_37550,c_31896])).

cnf(c_38964,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_38955,c_6])).

cnf(c_65876,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_65875,c_38964])).

cnf(c_65877,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_65876,c_6,c_1995])).

cnf(c_66312,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_65877,c_588])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66312,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:03:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.93/3.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.93/3.52  
% 23.93/3.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.93/3.52  
% 23.93/3.52  ------  iProver source info
% 23.93/3.52  
% 23.93/3.52  git: date: 2020-06-30 10:37:57 +0100
% 23.93/3.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.93/3.52  git: non_committed_changes: false
% 23.93/3.52  git: last_make_outside_of_git: false
% 23.93/3.52  
% 23.93/3.52  ------ 
% 23.93/3.52  
% 23.93/3.52  ------ Input Options
% 23.93/3.52  
% 23.93/3.52  --out_options                           all
% 23.93/3.52  --tptp_safe_out                         true
% 23.93/3.52  --problem_path                          ""
% 23.93/3.52  --include_path                          ""
% 23.93/3.52  --clausifier                            res/vclausify_rel
% 23.93/3.52  --clausifier_options                    ""
% 23.93/3.52  --stdin                                 false
% 23.93/3.52  --stats_out                             all
% 23.93/3.52  
% 23.93/3.52  ------ General Options
% 23.93/3.52  
% 23.93/3.52  --fof                                   false
% 23.93/3.52  --time_out_real                         305.
% 23.93/3.52  --time_out_virtual                      -1.
% 23.93/3.52  --symbol_type_check                     false
% 23.93/3.52  --clausify_out                          false
% 23.93/3.52  --sig_cnt_out                           false
% 23.93/3.52  --trig_cnt_out                          false
% 23.93/3.52  --trig_cnt_out_tolerance                1.
% 23.93/3.52  --trig_cnt_out_sk_spl                   false
% 23.93/3.52  --abstr_cl_out                          false
% 23.93/3.52  
% 23.93/3.52  ------ Global Options
% 23.93/3.52  
% 23.93/3.52  --schedule                              default
% 23.93/3.52  --add_important_lit                     false
% 23.93/3.52  --prop_solver_per_cl                    1000
% 23.93/3.52  --min_unsat_core                        false
% 23.93/3.52  --soft_assumptions                      false
% 23.93/3.52  --soft_lemma_size                       3
% 23.93/3.52  --prop_impl_unit_size                   0
% 23.93/3.52  --prop_impl_unit                        []
% 23.93/3.52  --share_sel_clauses                     true
% 23.93/3.52  --reset_solvers                         false
% 23.93/3.52  --bc_imp_inh                            [conj_cone]
% 23.93/3.52  --conj_cone_tolerance                   3.
% 23.93/3.52  --extra_neg_conj                        none
% 23.93/3.52  --large_theory_mode                     true
% 23.93/3.52  --prolific_symb_bound                   200
% 23.93/3.52  --lt_threshold                          2000
% 23.93/3.52  --clause_weak_htbl                      true
% 23.93/3.52  --gc_record_bc_elim                     false
% 23.93/3.52  
% 23.93/3.52  ------ Preprocessing Options
% 23.93/3.52  
% 23.93/3.52  --preprocessing_flag                    true
% 23.93/3.52  --time_out_prep_mult                    0.1
% 23.93/3.52  --splitting_mode                        input
% 23.93/3.52  --splitting_grd                         true
% 23.93/3.52  --splitting_cvd                         false
% 23.93/3.52  --splitting_cvd_svl                     false
% 23.93/3.52  --splitting_nvd                         32
% 23.93/3.52  --sub_typing                            true
% 23.93/3.52  --prep_gs_sim                           true
% 23.93/3.52  --prep_unflatten                        true
% 23.93/3.52  --prep_res_sim                          true
% 23.93/3.52  --prep_upred                            true
% 23.93/3.52  --prep_sem_filter                       exhaustive
% 23.93/3.52  --prep_sem_filter_out                   false
% 23.93/3.52  --pred_elim                             true
% 23.93/3.52  --res_sim_input                         true
% 23.93/3.52  --eq_ax_congr_red                       true
% 23.93/3.52  --pure_diseq_elim                       true
% 23.93/3.52  --brand_transform                       false
% 23.93/3.52  --non_eq_to_eq                          false
% 23.93/3.52  --prep_def_merge                        true
% 23.93/3.52  --prep_def_merge_prop_impl              false
% 23.93/3.52  --prep_def_merge_mbd                    true
% 23.93/3.52  --prep_def_merge_tr_red                 false
% 23.93/3.52  --prep_def_merge_tr_cl                  false
% 23.93/3.52  --smt_preprocessing                     true
% 23.93/3.52  --smt_ac_axioms                         fast
% 23.93/3.52  --preprocessed_out                      false
% 23.93/3.52  --preprocessed_stats                    false
% 23.93/3.52  
% 23.93/3.52  ------ Abstraction refinement Options
% 23.93/3.52  
% 23.93/3.52  --abstr_ref                             []
% 23.93/3.52  --abstr_ref_prep                        false
% 23.93/3.52  --abstr_ref_until_sat                   false
% 23.93/3.52  --abstr_ref_sig_restrict                funpre
% 23.93/3.52  --abstr_ref_af_restrict_to_split_sk     false
% 23.93/3.52  --abstr_ref_under                       []
% 23.93/3.52  
% 23.93/3.52  ------ SAT Options
% 23.93/3.52  
% 23.93/3.52  --sat_mode                              false
% 23.93/3.52  --sat_fm_restart_options                ""
% 23.93/3.52  --sat_gr_def                            false
% 23.93/3.52  --sat_epr_types                         true
% 23.93/3.52  --sat_non_cyclic_types                  false
% 23.93/3.52  --sat_finite_models                     false
% 23.93/3.52  --sat_fm_lemmas                         false
% 23.93/3.52  --sat_fm_prep                           false
% 23.93/3.52  --sat_fm_uc_incr                        true
% 23.93/3.52  --sat_out_model                         small
% 23.93/3.52  --sat_out_clauses                       false
% 23.93/3.52  
% 23.93/3.52  ------ QBF Options
% 23.93/3.52  
% 23.93/3.52  --qbf_mode                              false
% 23.93/3.52  --qbf_elim_univ                         false
% 23.93/3.52  --qbf_dom_inst                          none
% 23.93/3.52  --qbf_dom_pre_inst                      false
% 23.93/3.52  --qbf_sk_in                             false
% 23.93/3.52  --qbf_pred_elim                         true
% 23.93/3.52  --qbf_split                             512
% 23.93/3.52  
% 23.93/3.52  ------ BMC1 Options
% 23.93/3.52  
% 23.93/3.52  --bmc1_incremental                      false
% 23.93/3.52  --bmc1_axioms                           reachable_all
% 23.93/3.52  --bmc1_min_bound                        0
% 23.93/3.52  --bmc1_max_bound                        -1
% 23.93/3.52  --bmc1_max_bound_default                -1
% 23.93/3.52  --bmc1_symbol_reachability              true
% 23.93/3.52  --bmc1_property_lemmas                  false
% 23.93/3.52  --bmc1_k_induction                      false
% 23.93/3.52  --bmc1_non_equiv_states                 false
% 23.93/3.52  --bmc1_deadlock                         false
% 23.93/3.52  --bmc1_ucm                              false
% 23.93/3.52  --bmc1_add_unsat_core                   none
% 23.93/3.52  --bmc1_unsat_core_children              false
% 23.93/3.52  --bmc1_unsat_core_extrapolate_axioms    false
% 23.93/3.52  --bmc1_out_stat                         full
% 23.93/3.52  --bmc1_ground_init                      false
% 23.93/3.52  --bmc1_pre_inst_next_state              false
% 23.93/3.52  --bmc1_pre_inst_state                   false
% 23.93/3.52  --bmc1_pre_inst_reach_state             false
% 23.93/3.52  --bmc1_out_unsat_core                   false
% 23.93/3.52  --bmc1_aig_witness_out                  false
% 23.93/3.52  --bmc1_verbose                          false
% 23.93/3.52  --bmc1_dump_clauses_tptp                false
% 23.93/3.52  --bmc1_dump_unsat_core_tptp             false
% 23.93/3.52  --bmc1_dump_file                        -
% 23.93/3.52  --bmc1_ucm_expand_uc_limit              128
% 23.93/3.52  --bmc1_ucm_n_expand_iterations          6
% 23.93/3.52  --bmc1_ucm_extend_mode                  1
% 23.93/3.52  --bmc1_ucm_init_mode                    2
% 23.93/3.52  --bmc1_ucm_cone_mode                    none
% 23.93/3.52  --bmc1_ucm_reduced_relation_type        0
% 23.93/3.52  --bmc1_ucm_relax_model                  4
% 23.93/3.52  --bmc1_ucm_full_tr_after_sat            true
% 23.93/3.52  --bmc1_ucm_expand_neg_assumptions       false
% 23.93/3.52  --bmc1_ucm_layered_model                none
% 23.93/3.52  --bmc1_ucm_max_lemma_size               10
% 23.93/3.52  
% 23.93/3.52  ------ AIG Options
% 23.93/3.52  
% 23.93/3.52  --aig_mode                              false
% 23.93/3.52  
% 23.93/3.52  ------ Instantiation Options
% 23.93/3.52  
% 23.93/3.52  --instantiation_flag                    true
% 23.93/3.52  --inst_sos_flag                         true
% 23.93/3.52  --inst_sos_phase                        true
% 23.93/3.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.93/3.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.93/3.52  --inst_lit_sel_side                     num_symb
% 23.93/3.52  --inst_solver_per_active                1400
% 23.93/3.52  --inst_solver_calls_frac                1.
% 23.93/3.52  --inst_passive_queue_type               priority_queues
% 23.93/3.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.93/3.52  --inst_passive_queues_freq              [25;2]
% 23.93/3.52  --inst_dismatching                      true
% 23.93/3.52  --inst_eager_unprocessed_to_passive     true
% 23.93/3.52  --inst_prop_sim_given                   true
% 23.93/3.52  --inst_prop_sim_new                     false
% 23.93/3.52  --inst_subs_new                         false
% 23.93/3.52  --inst_eq_res_simp                      false
% 23.93/3.52  --inst_subs_given                       false
% 23.93/3.52  --inst_orphan_elimination               true
% 23.93/3.52  --inst_learning_loop_flag               true
% 23.93/3.52  --inst_learning_start                   3000
% 23.93/3.52  --inst_learning_factor                  2
% 23.93/3.52  --inst_start_prop_sim_after_learn       3
% 23.93/3.52  --inst_sel_renew                        solver
% 23.93/3.52  --inst_lit_activity_flag                true
% 23.93/3.52  --inst_restr_to_given                   false
% 23.93/3.52  --inst_activity_threshold               500
% 23.93/3.52  --inst_out_proof                        true
% 23.93/3.52  
% 23.93/3.52  ------ Resolution Options
% 23.93/3.52  
% 23.93/3.52  --resolution_flag                       true
% 23.93/3.52  --res_lit_sel                           adaptive
% 23.93/3.52  --res_lit_sel_side                      none
% 23.93/3.52  --res_ordering                          kbo
% 23.93/3.52  --res_to_prop_solver                    active
% 23.93/3.52  --res_prop_simpl_new                    false
% 23.93/3.52  --res_prop_simpl_given                  true
% 23.93/3.52  --res_passive_queue_type                priority_queues
% 23.93/3.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.93/3.52  --res_passive_queues_freq               [15;5]
% 23.93/3.52  --res_forward_subs                      full
% 23.93/3.52  --res_backward_subs                     full
% 23.93/3.52  --res_forward_subs_resolution           true
% 23.93/3.52  --res_backward_subs_resolution          true
% 23.93/3.52  --res_orphan_elimination                true
% 23.93/3.52  --res_time_limit                        2.
% 23.93/3.52  --res_out_proof                         true
% 23.93/3.52  
% 23.93/3.52  ------ Superposition Options
% 23.93/3.52  
% 23.93/3.52  --superposition_flag                    true
% 23.93/3.52  --sup_passive_queue_type                priority_queues
% 23.93/3.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.93/3.52  --sup_passive_queues_freq               [8;1;4]
% 23.93/3.52  --demod_completeness_check              fast
% 23.93/3.52  --demod_use_ground                      true
% 23.93/3.52  --sup_to_prop_solver                    passive
% 23.93/3.52  --sup_prop_simpl_new                    true
% 23.93/3.52  --sup_prop_simpl_given                  true
% 23.93/3.52  --sup_fun_splitting                     true
% 23.93/3.52  --sup_smt_interval                      50000
% 23.93/3.52  
% 23.93/3.52  ------ Superposition Simplification Setup
% 23.93/3.52  
% 23.93/3.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.93/3.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.93/3.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.93/3.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.93/3.52  --sup_full_triv                         [TrivRules;PropSubs]
% 23.93/3.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.93/3.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.93/3.52  --sup_immed_triv                        [TrivRules]
% 23.93/3.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.93/3.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.93/3.52  --sup_immed_bw_main                     []
% 23.93/3.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.93/3.52  --sup_input_triv                        [Unflattening;TrivRules]
% 23.93/3.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.93/3.52  --sup_input_bw                          []
% 23.93/3.52  
% 23.93/3.52  ------ Combination Options
% 23.93/3.52  
% 23.93/3.52  --comb_res_mult                         3
% 23.93/3.52  --comb_sup_mult                         2
% 23.93/3.52  --comb_inst_mult                        10
% 23.93/3.52  
% 23.93/3.52  ------ Debug Options
% 23.93/3.52  
% 23.93/3.52  --dbg_backtrace                         false
% 23.93/3.52  --dbg_dump_prop_clauses                 false
% 23.93/3.52  --dbg_dump_prop_clauses_file            -
% 23.93/3.52  --dbg_out_stat                          false
% 23.93/3.52  ------ Parsing...
% 23.93/3.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.93/3.52  
% 23.93/3.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 23.93/3.52  
% 23.93/3.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.93/3.52  
% 23.93/3.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.93/3.52  ------ Proving...
% 23.93/3.52  ------ Problem Properties 
% 23.93/3.52  
% 23.93/3.52  
% 23.93/3.52  clauses                                 14
% 23.93/3.52  conjectures                             3
% 23.93/3.52  EPR                                     3
% 23.93/3.52  Horn                                    14
% 23.93/3.52  unary                                   10
% 23.93/3.52  binary                                  3
% 23.93/3.52  lits                                    19
% 23.93/3.52  lits eq                                 7
% 23.93/3.52  fd_pure                                 0
% 23.93/3.52  fd_pseudo                               0
% 23.93/3.52  fd_cond                                 0
% 23.93/3.52  fd_pseudo_cond                          1
% 23.93/3.52  AC symbols                              0
% 23.93/3.52  
% 23.93/3.52  ------ Schedule dynamic 5 is on 
% 23.93/3.52  
% 23.93/3.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.93/3.52  
% 23.93/3.52  
% 23.93/3.52  ------ 
% 23.93/3.52  Current options:
% 23.93/3.52  ------ 
% 23.93/3.52  
% 23.93/3.52  ------ Input Options
% 23.93/3.52  
% 23.93/3.52  --out_options                           all
% 23.93/3.52  --tptp_safe_out                         true
% 23.93/3.52  --problem_path                          ""
% 23.93/3.52  --include_path                          ""
% 23.93/3.52  --clausifier                            res/vclausify_rel
% 23.93/3.52  --clausifier_options                    ""
% 23.93/3.52  --stdin                                 false
% 23.93/3.52  --stats_out                             all
% 23.93/3.52  
% 23.93/3.52  ------ General Options
% 23.93/3.52  
% 23.93/3.52  --fof                                   false
% 23.93/3.52  --time_out_real                         305.
% 23.93/3.52  --time_out_virtual                      -1.
% 23.93/3.52  --symbol_type_check                     false
% 23.93/3.52  --clausify_out                          false
% 23.93/3.52  --sig_cnt_out                           false
% 23.93/3.52  --trig_cnt_out                          false
% 23.93/3.52  --trig_cnt_out_tolerance                1.
% 23.93/3.52  --trig_cnt_out_sk_spl                   false
% 23.93/3.52  --abstr_cl_out                          false
% 23.93/3.52  
% 23.93/3.52  ------ Global Options
% 23.93/3.52  
% 23.93/3.52  --schedule                              default
% 23.93/3.52  --add_important_lit                     false
% 23.93/3.52  --prop_solver_per_cl                    1000
% 23.93/3.52  --min_unsat_core                        false
% 23.93/3.52  --soft_assumptions                      false
% 23.93/3.52  --soft_lemma_size                       3
% 23.93/3.52  --prop_impl_unit_size                   0
% 23.93/3.52  --prop_impl_unit                        []
% 23.93/3.52  --share_sel_clauses                     true
% 23.93/3.52  --reset_solvers                         false
% 23.93/3.52  --bc_imp_inh                            [conj_cone]
% 23.93/3.52  --conj_cone_tolerance                   3.
% 23.93/3.52  --extra_neg_conj                        none
% 23.93/3.52  --large_theory_mode                     true
% 23.93/3.52  --prolific_symb_bound                   200
% 23.93/3.52  --lt_threshold                          2000
% 23.93/3.52  --clause_weak_htbl                      true
% 23.93/3.52  --gc_record_bc_elim                     false
% 23.93/3.52  
% 23.93/3.52  ------ Preprocessing Options
% 23.93/3.52  
% 23.93/3.52  --preprocessing_flag                    true
% 23.93/3.52  --time_out_prep_mult                    0.1
% 23.93/3.52  --splitting_mode                        input
% 23.93/3.52  --splitting_grd                         true
% 23.93/3.52  --splitting_cvd                         false
% 23.93/3.52  --splitting_cvd_svl                     false
% 23.93/3.52  --splitting_nvd                         32
% 23.93/3.52  --sub_typing                            true
% 23.93/3.52  --prep_gs_sim                           true
% 23.93/3.52  --prep_unflatten                        true
% 23.93/3.52  --prep_res_sim                          true
% 23.93/3.52  --prep_upred                            true
% 23.93/3.52  --prep_sem_filter                       exhaustive
% 23.93/3.52  --prep_sem_filter_out                   false
% 23.93/3.52  --pred_elim                             true
% 23.93/3.52  --res_sim_input                         true
% 23.93/3.52  --eq_ax_congr_red                       true
% 23.93/3.52  --pure_diseq_elim                       true
% 23.93/3.52  --brand_transform                       false
% 23.93/3.52  --non_eq_to_eq                          false
% 23.93/3.52  --prep_def_merge                        true
% 23.93/3.52  --prep_def_merge_prop_impl              false
% 23.93/3.52  --prep_def_merge_mbd                    true
% 23.93/3.52  --prep_def_merge_tr_red                 false
% 23.93/3.52  --prep_def_merge_tr_cl                  false
% 23.93/3.52  --smt_preprocessing                     true
% 23.93/3.52  --smt_ac_axioms                         fast
% 23.93/3.52  --preprocessed_out                      false
% 23.93/3.52  --preprocessed_stats                    false
% 23.93/3.52  
% 23.93/3.52  ------ Abstraction refinement Options
% 23.93/3.52  
% 23.93/3.52  --abstr_ref                             []
% 23.93/3.52  --abstr_ref_prep                        false
% 23.93/3.52  --abstr_ref_until_sat                   false
% 23.93/3.52  --abstr_ref_sig_restrict                funpre
% 23.93/3.52  --abstr_ref_af_restrict_to_split_sk     false
% 23.93/3.52  --abstr_ref_under                       []
% 23.93/3.52  
% 23.93/3.52  ------ SAT Options
% 23.93/3.52  
% 23.93/3.52  --sat_mode                              false
% 23.93/3.52  --sat_fm_restart_options                ""
% 23.93/3.52  --sat_gr_def                            false
% 23.93/3.52  --sat_epr_types                         true
% 23.93/3.52  --sat_non_cyclic_types                  false
% 23.93/3.52  --sat_finite_models                     false
% 23.93/3.52  --sat_fm_lemmas                         false
% 23.93/3.52  --sat_fm_prep                           false
% 23.93/3.52  --sat_fm_uc_incr                        true
% 23.93/3.52  --sat_out_model                         small
% 23.93/3.52  --sat_out_clauses                       false
% 23.93/3.52  
% 23.93/3.52  ------ QBF Options
% 23.93/3.52  
% 23.93/3.52  --qbf_mode                              false
% 23.93/3.52  --qbf_elim_univ                         false
% 23.93/3.52  --qbf_dom_inst                          none
% 23.93/3.52  --qbf_dom_pre_inst                      false
% 23.93/3.52  --qbf_sk_in                             false
% 23.93/3.52  --qbf_pred_elim                         true
% 23.93/3.52  --qbf_split                             512
% 23.93/3.52  
% 23.93/3.52  ------ BMC1 Options
% 23.93/3.52  
% 23.93/3.52  --bmc1_incremental                      false
% 23.93/3.52  --bmc1_axioms                           reachable_all
% 23.93/3.52  --bmc1_min_bound                        0
% 23.93/3.52  --bmc1_max_bound                        -1
% 23.93/3.52  --bmc1_max_bound_default                -1
% 23.93/3.52  --bmc1_symbol_reachability              true
% 23.93/3.52  --bmc1_property_lemmas                  false
% 23.93/3.52  --bmc1_k_induction                      false
% 23.93/3.52  --bmc1_non_equiv_states                 false
% 23.93/3.52  --bmc1_deadlock                         false
% 23.93/3.52  --bmc1_ucm                              false
% 23.93/3.52  --bmc1_add_unsat_core                   none
% 23.93/3.52  --bmc1_unsat_core_children              false
% 23.93/3.52  --bmc1_unsat_core_extrapolate_axioms    false
% 23.93/3.52  --bmc1_out_stat                         full
% 23.93/3.52  --bmc1_ground_init                      false
% 23.93/3.52  --bmc1_pre_inst_next_state              false
% 23.93/3.52  --bmc1_pre_inst_state                   false
% 23.93/3.52  --bmc1_pre_inst_reach_state             false
% 23.93/3.52  --bmc1_out_unsat_core                   false
% 23.93/3.52  --bmc1_aig_witness_out                  false
% 23.93/3.52  --bmc1_verbose                          false
% 23.93/3.52  --bmc1_dump_clauses_tptp                false
% 23.93/3.52  --bmc1_dump_unsat_core_tptp             false
% 23.93/3.52  --bmc1_dump_file                        -
% 23.93/3.52  --bmc1_ucm_expand_uc_limit              128
% 23.93/3.52  --bmc1_ucm_n_expand_iterations          6
% 23.93/3.52  --bmc1_ucm_extend_mode                  1
% 23.93/3.52  --bmc1_ucm_init_mode                    2
% 23.93/3.52  --bmc1_ucm_cone_mode                    none
% 23.93/3.52  --bmc1_ucm_reduced_relation_type        0
% 23.93/3.52  --bmc1_ucm_relax_model                  4
% 23.93/3.52  --bmc1_ucm_full_tr_after_sat            true
% 23.93/3.52  --bmc1_ucm_expand_neg_assumptions       false
% 23.93/3.52  --bmc1_ucm_layered_model                none
% 23.93/3.52  --bmc1_ucm_max_lemma_size               10
% 23.93/3.52  
% 23.93/3.52  ------ AIG Options
% 23.93/3.52  
% 23.93/3.52  --aig_mode                              false
% 23.93/3.52  
% 23.93/3.52  ------ Instantiation Options
% 23.93/3.52  
% 23.93/3.52  --instantiation_flag                    true
% 23.93/3.52  --inst_sos_flag                         true
% 23.93/3.52  --inst_sos_phase                        true
% 23.93/3.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.93/3.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.93/3.52  --inst_lit_sel_side                     none
% 23.93/3.52  --inst_solver_per_active                1400
% 23.93/3.52  --inst_solver_calls_frac                1.
% 23.93/3.52  --inst_passive_queue_type               priority_queues
% 23.93/3.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.93/3.52  --inst_passive_queues_freq              [25;2]
% 23.93/3.52  --inst_dismatching                      true
% 23.93/3.52  --inst_eager_unprocessed_to_passive     true
% 23.93/3.52  --inst_prop_sim_given                   true
% 23.93/3.52  --inst_prop_sim_new                     false
% 23.93/3.52  --inst_subs_new                         false
% 23.93/3.52  --inst_eq_res_simp                      false
% 23.93/3.52  --inst_subs_given                       false
% 23.93/3.52  --inst_orphan_elimination               true
% 23.93/3.52  --inst_learning_loop_flag               true
% 23.93/3.52  --inst_learning_start                   3000
% 23.93/3.52  --inst_learning_factor                  2
% 23.93/3.52  --inst_start_prop_sim_after_learn       3
% 23.93/3.52  --inst_sel_renew                        solver
% 23.93/3.52  --inst_lit_activity_flag                true
% 23.93/3.52  --inst_restr_to_given                   false
% 23.93/3.52  --inst_activity_threshold               500
% 23.93/3.52  --inst_out_proof                        true
% 23.93/3.52  
% 23.93/3.52  ------ Resolution Options
% 23.93/3.52  
% 23.93/3.52  --resolution_flag                       false
% 23.93/3.52  --res_lit_sel                           adaptive
% 23.93/3.52  --res_lit_sel_side                      none
% 23.93/3.52  --res_ordering                          kbo
% 23.93/3.52  --res_to_prop_solver                    active
% 23.93/3.52  --res_prop_simpl_new                    false
% 23.93/3.52  --res_prop_simpl_given                  true
% 23.93/3.52  --res_passive_queue_type                priority_queues
% 23.93/3.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.93/3.52  --res_passive_queues_freq               [15;5]
% 23.93/3.52  --res_forward_subs                      full
% 23.93/3.52  --res_backward_subs                     full
% 23.93/3.52  --res_forward_subs_resolution           true
% 23.93/3.52  --res_backward_subs_resolution          true
% 23.93/3.52  --res_orphan_elimination                true
% 23.93/3.52  --res_time_limit                        2.
% 23.93/3.52  --res_out_proof                         true
% 23.93/3.52  
% 23.93/3.52  ------ Superposition Options
% 23.93/3.52  
% 23.93/3.52  --superposition_flag                    true
% 23.93/3.52  --sup_passive_queue_type                priority_queues
% 23.93/3.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.93/3.52  --sup_passive_queues_freq               [8;1;4]
% 23.93/3.52  --demod_completeness_check              fast
% 23.93/3.52  --demod_use_ground                      true
% 23.93/3.52  --sup_to_prop_solver                    passive
% 23.93/3.52  --sup_prop_simpl_new                    true
% 23.93/3.52  --sup_prop_simpl_given                  true
% 23.93/3.52  --sup_fun_splitting                     true
% 23.93/3.52  --sup_smt_interval                      50000
% 23.93/3.52  
% 23.93/3.52  ------ Superposition Simplification Setup
% 23.93/3.52  
% 23.93/3.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.93/3.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.93/3.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.93/3.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.93/3.52  --sup_full_triv                         [TrivRules;PropSubs]
% 23.93/3.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.93/3.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.93/3.52  --sup_immed_triv                        [TrivRules]
% 23.93/3.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.93/3.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.93/3.52  --sup_immed_bw_main                     []
% 23.93/3.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.93/3.52  --sup_input_triv                        [Unflattening;TrivRules]
% 23.93/3.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.93/3.52  --sup_input_bw                          []
% 23.93/3.52  
% 23.93/3.52  ------ Combination Options
% 23.93/3.52  
% 23.93/3.52  --comb_res_mult                         3
% 23.93/3.52  --comb_sup_mult                         2
% 23.93/3.52  --comb_inst_mult                        10
% 23.93/3.52  
% 23.93/3.52  ------ Debug Options
% 23.93/3.52  
% 23.93/3.52  --dbg_backtrace                         false
% 23.93/3.52  --dbg_dump_prop_clauses                 false
% 23.93/3.52  --dbg_dump_prop_clauses_file            -
% 23.93/3.52  --dbg_out_stat                          false
% 23.93/3.52  
% 23.93/3.52  
% 23.93/3.52  
% 23.93/3.52  
% 23.93/3.52  ------ Proving...
% 23.93/3.52  
% 23.93/3.52  
% 23.93/3.52  % SZS status Theorem for theBenchmark.p
% 23.93/3.52  
% 23.93/3.52  % SZS output start CNFRefutation for theBenchmark.p
% 23.93/3.52  
% 23.93/3.52  fof(f12,conjecture,(
% 23.93/3.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f13,negated_conjecture,(
% 23.93/3.52    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 23.93/3.52    inference(negated_conjecture,[],[f12])).
% 23.93/3.52  
% 23.93/3.52  fof(f20,plain,(
% 23.93/3.52    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 23.93/3.52    inference(ennf_transformation,[],[f13])).
% 23.93/3.52  
% 23.93/3.52  fof(f21,plain,(
% 23.93/3.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 23.93/3.52    inference(flattening,[],[f20])).
% 23.93/3.52  
% 23.93/3.52  fof(f25,plain,(
% 23.93/3.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 23.93/3.52    introduced(choice_axiom,[])).
% 23.93/3.52  
% 23.93/3.52  fof(f26,plain,(
% 23.93/3.52    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 23.93/3.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).
% 23.93/3.52  
% 23.93/3.52  fof(f43,plain,(
% 23.93/3.52    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 23.93/3.52    inference(cnf_transformation,[],[f26])).
% 23.93/3.52  
% 23.93/3.52  fof(f2,axiom,(
% 23.93/3.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f24,plain,(
% 23.93/3.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 23.93/3.52    inference(nnf_transformation,[],[f2])).
% 23.93/3.52  
% 23.93/3.52  fof(f31,plain,(
% 23.93/3.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 23.93/3.52    inference(cnf_transformation,[],[f24])).
% 23.93/3.52  
% 23.93/3.52  fof(f9,axiom,(
% 23.93/3.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f14,plain,(
% 23.93/3.52    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 23.93/3.52    inference(ennf_transformation,[],[f9])).
% 23.93/3.52  
% 23.93/3.52  fof(f15,plain,(
% 23.93/3.52    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 23.93/3.52    inference(flattening,[],[f14])).
% 23.93/3.52  
% 23.93/3.52  fof(f38,plain,(
% 23.93/3.52    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 23.93/3.52    inference(cnf_transformation,[],[f15])).
% 23.93/3.52  
% 23.93/3.52  fof(f5,axiom,(
% 23.93/3.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f34,plain,(
% 23.93/3.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.93/3.52    inference(cnf_transformation,[],[f5])).
% 23.93/3.52  
% 23.93/3.52  fof(f50,plain,(
% 23.93/3.52    ( ! [X2,X0,X1] : (k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 23.93/3.52    inference(definition_unfolding,[],[f38,f34,f34])).
% 23.93/3.52  
% 23.93/3.52  fof(f45,plain,(
% 23.93/3.52    v2_funct_1(sK2)),
% 23.93/3.52    inference(cnf_transformation,[],[f26])).
% 23.93/3.52  
% 23.93/3.52  fof(f41,plain,(
% 23.93/3.52    v1_relat_1(sK2)),
% 23.93/3.52    inference(cnf_transformation,[],[f26])).
% 23.93/3.52  
% 23.93/3.52  fof(f42,plain,(
% 23.93/3.52    v1_funct_1(sK2)),
% 23.93/3.52    inference(cnf_transformation,[],[f26])).
% 23.93/3.52  
% 23.93/3.52  fof(f4,axiom,(
% 23.93/3.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f33,plain,(
% 23.93/3.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.93/3.52    inference(cnf_transformation,[],[f4])).
% 23.93/3.52  
% 23.93/3.52  fof(f3,axiom,(
% 23.93/3.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f32,plain,(
% 23.93/3.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.93/3.52    inference(cnf_transformation,[],[f3])).
% 23.93/3.52  
% 23.93/3.52  fof(f47,plain,(
% 23.93/3.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 23.93/3.52    inference(definition_unfolding,[],[f32,f34])).
% 23.93/3.52  
% 23.93/3.52  fof(f6,axiom,(
% 23.93/3.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f35,plain,(
% 23.93/3.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 23.93/3.52    inference(cnf_transformation,[],[f6])).
% 23.93/3.52  
% 23.93/3.52  fof(f7,axiom,(
% 23.93/3.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f36,plain,(
% 23.93/3.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.93/3.52    inference(cnf_transformation,[],[f7])).
% 23.93/3.52  
% 23.93/3.52  fof(f48,plain,(
% 23.93/3.52    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 23.93/3.52    inference(definition_unfolding,[],[f35,f36,f36])).
% 23.93/3.52  
% 23.93/3.52  fof(f8,axiom,(
% 23.93/3.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f37,plain,(
% 23.93/3.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 23.93/3.52    inference(cnf_transformation,[],[f8])).
% 23.93/3.52  
% 23.93/3.52  fof(f49,plain,(
% 23.93/3.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 23.93/3.52    inference(definition_unfolding,[],[f37,f34,f36])).
% 23.93/3.52  
% 23.93/3.52  fof(f11,axiom,(
% 23.93/3.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f18,plain,(
% 23.93/3.52    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.93/3.52    inference(ennf_transformation,[],[f11])).
% 23.93/3.52  
% 23.93/3.52  fof(f19,plain,(
% 23.93/3.52    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.93/3.52    inference(flattening,[],[f18])).
% 23.93/3.52  
% 23.93/3.52  fof(f40,plain,(
% 23.93/3.52    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.93/3.52    inference(cnf_transformation,[],[f19])).
% 23.93/3.52  
% 23.93/3.52  fof(f44,plain,(
% 23.93/3.52    r1_tarski(sK0,k1_relat_1(sK2))),
% 23.93/3.52    inference(cnf_transformation,[],[f26])).
% 23.93/3.52  
% 23.93/3.52  fof(f10,axiom,(
% 23.93/3.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 23.93/3.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.93/3.52  
% 23.93/3.52  fof(f16,plain,(
% 23.93/3.52    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 23.93/3.52    inference(ennf_transformation,[],[f10])).
% 23.93/3.52  
% 23.93/3.52  fof(f17,plain,(
% 23.93/3.52    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 23.93/3.52    inference(flattening,[],[f16])).
% 23.93/3.52  
% 23.93/3.52  fof(f39,plain,(
% 23.93/3.52    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.93/3.52    inference(cnf_transformation,[],[f17])).
% 23.93/3.52  
% 23.93/3.52  fof(f46,plain,(
% 23.93/3.52    ~r1_tarski(sK0,sK1)),
% 23.93/3.52    inference(cnf_transformation,[],[f26])).
% 23.93/3.52  
% 23.93/3.52  cnf(c_15,negated_conjecture,
% 23.93/3.52      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 23.93/3.52      inference(cnf_transformation,[],[f43]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_585,plain,
% 23.93/3.52      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 23.93/3.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_3,plain,
% 23.93/3.52      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 23.93/3.52      inference(cnf_transformation,[],[f31]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_590,plain,
% 23.93/3.52      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 23.93/3.52      | r1_tarski(X0,X1) != iProver_top ),
% 23.93/3.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1682,plain,
% 23.93/3.52      ( k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_585,c_590]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_9,plain,
% 23.93/3.52      ( ~ v1_relat_1(X0)
% 23.93/3.52      | ~ v1_funct_1(X0)
% 23.93/3.52      | ~ v2_funct_1(X0)
% 23.93/3.52      | k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 23.93/3.52      inference(cnf_transformation,[],[f50]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_13,negated_conjecture,
% 23.93/3.52      ( v2_funct_1(sK2) ),
% 23.93/3.52      inference(cnf_transformation,[],[f45]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_213,plain,
% 23.93/3.52      ( ~ v1_relat_1(X0)
% 23.93/3.52      | ~ v1_funct_1(X0)
% 23.93/3.52      | k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 23.93/3.52      | sK2 != X0 ),
% 23.93/3.52      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_214,plain,
% 23.93/3.52      ( ~ v1_relat_1(sK2)
% 23.93/3.52      | ~ v1_funct_1(sK2)
% 23.93/3.52      | k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 23.93/3.52      inference(unflattening,[status(thm)],[c_213]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_17,negated_conjecture,
% 23.93/3.52      ( v1_relat_1(sK2) ),
% 23.93/3.52      inference(cnf_transformation,[],[f41]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_16,negated_conjecture,
% 23.93/3.52      ( v1_funct_1(sK2) ),
% 23.93/3.52      inference(cnf_transformation,[],[f42]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_218,plain,
% 23.93/3.52      ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 23.93/3.52      inference(global_propositional_subsumption,
% 23.93/3.52                [status(thm)],
% 23.93/3.52                [c_214,c_17,c_16]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_2179,plain,
% 23.93/3.52      ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0) ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_1682,c_218]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_6,plain,
% 23.93/3.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.93/3.52      inference(cnf_transformation,[],[f33]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_2180,plain,
% 23.93/3.52      ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k9_relat_1(sK2,sK0) ),
% 23.93/3.52      inference(demodulation,[status(thm)],[c_2179,c_6]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_5,plain,
% 23.93/3.52      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 23.93/3.52      inference(cnf_transformation,[],[f47]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_588,plain,
% 23.93/3.52      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 23.93/3.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1051,plain,
% 23.93/3.52      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X0)) = iProver_top ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_218,c_588]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1685,plain,
% 23.93/3.52      ( k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X0)) = k1_xboole_0 ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_1051,c_590]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_7,plain,
% 23.93/3.52      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 23.93/3.52      inference(cnf_transformation,[],[f48]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_8,plain,
% 23.93/3.52      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 23.93/3.52      inference(cnf_transformation,[],[f49]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1118,plain,
% 23.93/3.52      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1926,plain,
% 23.93/3.52      ( k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_1118,c_218]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_2442,plain,
% 23.93/3.52      ( k4_xboole_0(k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),k4_xboole_0(k1_setfam_1(k2_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),k9_relat_1(sK2,X2))) = k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_1926,c_218]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_2470,plain,
% 23.93/3.52      ( k4_xboole_0(k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),k4_xboole_0(k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))),k9_relat_1(sK2,X2))) = k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) ),
% 23.93/3.52      inference(demodulation,[status(thm)],[c_2442,c_8]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_2471,plain,
% 23.93/3.52      ( k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X2))) = k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) ),
% 23.93/3.52      inference(light_normalisation,[status(thm)],[c_2470,c_218]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_41277,plain,
% 23.93/3.52      ( k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1))) = k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_1685,c_2471]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1925,plain,
% 23.93/3.52      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_1118,c_588]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1927,plain,
% 23.93/3.52      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 23.93/3.52      inference(light_normalisation,[status(thm)],[c_1925,c_8]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1995,plain,
% 23.93/3.52      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_1927,c_590]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_41306,plain,
% 23.93/3.52      ( k9_relat_1(sK2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)) = k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 23.93/3.52      inference(light_normalisation,[status(thm)],[c_41277,c_1995]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_41307,plain,
% 23.93/3.52      ( k4_xboole_0(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k1_xboole_0) = k9_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 23.93/3.52      inference(demodulation,[status(thm)],[c_41306,c_6]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_64341,plain,
% 23.93/3.52      ( k9_relat_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0) ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_2180,c_41307]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_65470,plain,
% 23.93/3.52      ( k9_relat_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k9_relat_1(sK2,sK0) ),
% 23.93/3.52      inference(demodulation,[status(thm)],[c_64341,c_6]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_11,plain,
% 23.93/3.52      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 23.93/3.52      | ~ v1_relat_1(X0)
% 23.93/3.52      | ~ v1_funct_1(X0)
% 23.93/3.52      | ~ v2_funct_1(X0) ),
% 23.93/3.52      inference(cnf_transformation,[],[f40]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_198,plain,
% 23.93/3.52      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 23.93/3.52      | ~ v1_relat_1(X0)
% 23.93/3.52      | ~ v1_funct_1(X0)
% 23.93/3.52      | sK2 != X0 ),
% 23.93/3.52      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_199,plain,
% 23.93/3.52      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
% 23.93/3.52      | ~ v1_relat_1(sK2)
% 23.93/3.52      | ~ v1_funct_1(sK2) ),
% 23.93/3.52      inference(unflattening,[status(thm)],[c_198]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_203,plain,
% 23.93/3.52      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
% 23.93/3.52      inference(global_propositional_subsumption,
% 23.93/3.52                [status(thm)],
% 23.93/3.52                [c_199,c_17,c_16]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_584,plain,
% 23.93/3.52      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = iProver_top ),
% 23.93/3.52      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1683,plain,
% 23.93/3.52      ( k4_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = k1_xboole_0 ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_584,c_590]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_1906,plain,
% 23.93/3.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_1118,c_8]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_31822,plain,
% 23.93/3.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k4_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),k1_xboole_0) ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_1683,c_1906]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_31896,plain,
% 23.93/3.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
% 23.93/3.52      inference(demodulation,[status(thm)],[c_31822,c_6]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_65582,plain,
% 23.93/3.52      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) ),
% 23.93/3.52      inference(superposition,[status(thm)],[c_65470,c_31896]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_65875,plain,
% 23.93/3.52      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
% 23.93/3.52      inference(demodulation,[status(thm)],[c_65582,c_65470]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_14,negated_conjecture,
% 23.93/3.52      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 23.93/3.52      inference(cnf_transformation,[],[f44]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_586,plain,
% 23.93/3.52      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 23.93/3.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.93/3.52  
% 23.93/3.52  cnf(c_10,plain,
% 23.93/3.52      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 23.93/3.52      | ~ r1_tarski(X0,k1_relat_1(X1))
% 23.93/3.52      | ~ v1_relat_1(X1) ),
% 23.93/3.52      inference(cnf_transformation,[],[f39]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_227,plain,
% 23.93/3.53      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 23.93/3.53      | ~ r1_tarski(X0,k1_relat_1(X1))
% 23.93/3.53      | sK2 != X1 ),
% 23.93/3.53      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_228,plain,
% 23.93/3.53      ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
% 23.93/3.53      | ~ r1_tarski(X0,k1_relat_1(sK2)) ),
% 23.93/3.53      inference(unflattening,[status(thm)],[c_227]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_583,plain,
% 23.93/3.53      ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = iProver_top
% 23.93/3.53      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 23.93/3.53      inference(predicate_to_equality,[status(thm)],[c_228]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_1684,plain,
% 23.93/3.53      ( k4_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = k1_xboole_0
% 23.93/3.53      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 23.93/3.53      inference(superposition,[status(thm)],[c_583,c_590]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_37550,plain,
% 23.93/3.53      ( k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = k1_xboole_0 ),
% 23.93/3.53      inference(superposition,[status(thm)],[c_586,c_1684]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_38955,plain,
% 23.93/3.53      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 23.93/3.53      inference(superposition,[status(thm)],[c_37550,c_31896]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_38964,plain,
% 23.93/3.53      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 23.93/3.53      inference(demodulation,[status(thm)],[c_38955,c_6]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_65876,plain,
% 23.93/3.53      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)) = sK0 ),
% 23.93/3.53      inference(light_normalisation,[status(thm)],[c_65875,c_38964]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_65877,plain,
% 23.93/3.53      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = sK0 ),
% 23.93/3.53      inference(demodulation,[status(thm)],[c_65876,c_6,c_1995]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_66312,plain,
% 23.93/3.53      ( r1_tarski(sK0,sK1) = iProver_top ),
% 23.93/3.53      inference(superposition,[status(thm)],[c_65877,c_588]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_12,negated_conjecture,
% 23.93/3.53      ( ~ r1_tarski(sK0,sK1) ),
% 23.93/3.53      inference(cnf_transformation,[],[f46]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(c_23,plain,
% 23.93/3.53      ( r1_tarski(sK0,sK1) != iProver_top ),
% 23.93/3.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.93/3.53  
% 23.93/3.53  cnf(contradiction,plain,
% 23.93/3.53      ( $false ),
% 23.93/3.53      inference(minisat,[status(thm)],[c_66312,c_23]) ).
% 23.93/3.53  
% 23.93/3.53  
% 23.93/3.53  % SZS output end CNFRefutation for theBenchmark.p
% 23.93/3.53  
% 23.93/3.53  ------                               Statistics
% 23.93/3.53  
% 23.93/3.53  ------ General
% 23.93/3.53  
% 23.93/3.53  abstr_ref_over_cycles:                  0
% 23.93/3.53  abstr_ref_under_cycles:                 0
% 23.93/3.53  gc_basic_clause_elim:                   0
% 23.93/3.53  forced_gc_time:                         0
% 23.93/3.53  parsing_time:                           0.006
% 23.93/3.53  unif_index_cands_time:                  0.
% 23.93/3.53  unif_index_add_time:                    0.
% 23.93/3.53  orderings_time:                         0.
% 23.93/3.53  out_proof_time:                         0.01
% 23.93/3.53  total_time:                             2.821
% 23.93/3.53  num_of_symbols:                         45
% 23.93/3.53  num_of_terms:                           121444
% 23.93/3.53  
% 23.93/3.53  ------ Preprocessing
% 23.93/3.53  
% 23.93/3.53  num_of_splits:                          0
% 23.93/3.53  num_of_split_atoms:                     0
% 23.93/3.53  num_of_reused_defs:                     0
% 23.93/3.53  num_eq_ax_congr_red:                    13
% 23.93/3.53  num_of_sem_filtered_clauses:            1
% 23.93/3.53  num_of_subtypes:                        0
% 23.93/3.53  monotx_restored_types:                  0
% 23.93/3.53  sat_num_of_epr_types:                   0
% 23.93/3.53  sat_num_of_non_cyclic_types:            0
% 23.93/3.53  sat_guarded_non_collapsed_types:        0
% 23.93/3.53  num_pure_diseq_elim:                    0
% 23.93/3.53  simp_replaced_by:                       0
% 23.93/3.53  res_preprocessed:                       76
% 23.93/3.53  prep_upred:                             0
% 23.93/3.53  prep_unflattend:                        3
% 23.93/3.53  smt_new_axioms:                         0
% 23.93/3.53  pred_elim_cands:                        1
% 23.93/3.53  pred_elim:                              3
% 23.93/3.53  pred_elim_cl:                           3
% 23.93/3.53  pred_elim_cycles:                       5
% 23.93/3.53  merged_defs:                            8
% 23.93/3.53  merged_defs_ncl:                        0
% 23.93/3.53  bin_hyper_res:                          8
% 23.93/3.53  prep_cycles:                            4
% 23.93/3.53  pred_elim_time:                         0.
% 23.93/3.53  splitting_time:                         0.
% 23.93/3.53  sem_filter_time:                        0.
% 23.93/3.53  monotx_time:                            0.
% 23.93/3.53  subtype_inf_time:                       0.
% 23.93/3.53  
% 23.93/3.53  ------ Problem properties
% 23.93/3.53  
% 23.93/3.53  clauses:                                14
% 23.93/3.53  conjectures:                            3
% 23.93/3.53  epr:                                    3
% 23.93/3.53  horn:                                   14
% 23.93/3.53  ground:                                 3
% 23.93/3.53  unary:                                  10
% 23.93/3.53  binary:                                 3
% 23.93/3.53  lits:                                   19
% 23.93/3.53  lits_eq:                                7
% 23.93/3.53  fd_pure:                                0
% 23.93/3.53  fd_pseudo:                              0
% 23.93/3.53  fd_cond:                                0
% 23.93/3.53  fd_pseudo_cond:                         1
% 23.93/3.53  ac_symbols:                             0
% 23.93/3.53  
% 23.93/3.53  ------ Propositional Solver
% 23.93/3.53  
% 23.93/3.53  prop_solver_calls:                      32
% 23.93/3.53  prop_fast_solver_calls:                 516
% 23.93/3.53  smt_solver_calls:                       0
% 23.93/3.53  smt_fast_solver_calls:                  0
% 23.93/3.53  prop_num_of_clauses:                    25361
% 23.93/3.53  prop_preprocess_simplified:             18929
% 23.93/3.53  prop_fo_subsumed:                       4
% 23.93/3.53  prop_solver_time:                       0.
% 23.93/3.53  smt_solver_time:                        0.
% 23.93/3.53  smt_fast_solver_time:                   0.
% 23.93/3.53  prop_fast_solver_time:                  0.
% 23.93/3.53  prop_unsat_core_time:                   0.002
% 23.93/3.53  
% 23.93/3.53  ------ QBF
% 23.93/3.53  
% 23.93/3.53  qbf_q_res:                              0
% 23.93/3.53  qbf_num_tautologies:                    0
% 23.93/3.53  qbf_prep_cycles:                        0
% 23.93/3.53  
% 23.93/3.53  ------ BMC1
% 23.93/3.53  
% 23.93/3.53  bmc1_current_bound:                     -1
% 23.93/3.53  bmc1_last_solved_bound:                 -1
% 23.93/3.53  bmc1_unsat_core_size:                   -1
% 23.93/3.53  bmc1_unsat_core_parents_size:           -1
% 23.93/3.53  bmc1_merge_next_fun:                    0
% 23.93/3.53  bmc1_unsat_core_clauses_time:           0.
% 23.93/3.53  
% 23.93/3.53  ------ Instantiation
% 23.93/3.53  
% 23.93/3.53  inst_num_of_clauses:                    2613
% 23.93/3.53  inst_num_in_passive:                    1324
% 23.93/3.53  inst_num_in_active:                     995
% 23.93/3.53  inst_num_in_unprocessed:                294
% 23.93/3.53  inst_num_of_loops:                      1040
% 23.93/3.53  inst_num_of_learning_restarts:          0
% 23.93/3.53  inst_num_moves_active_passive:          43
% 23.93/3.53  inst_lit_activity:                      0
% 23.93/3.53  inst_lit_activity_moves:                0
% 23.93/3.53  inst_num_tautologies:                   0
% 23.93/3.53  inst_num_prop_implied:                  0
% 23.93/3.53  inst_num_existing_simplified:           0
% 23.93/3.53  inst_num_eq_res_simplified:             0
% 23.93/3.53  inst_num_child_elim:                    0
% 23.93/3.53  inst_num_of_dismatching_blockings:      1044
% 23.93/3.53  inst_num_of_non_proper_insts:           3271
% 23.93/3.53  inst_num_of_duplicates:                 0
% 23.93/3.53  inst_inst_num_from_inst_to_res:         0
% 23.93/3.53  inst_dismatching_checking_time:         0.
% 23.93/3.53  
% 23.93/3.53  ------ Resolution
% 23.93/3.53  
% 23.93/3.53  res_num_of_clauses:                     0
% 23.93/3.53  res_num_in_passive:                     0
% 23.93/3.53  res_num_in_active:                      0
% 23.93/3.53  res_num_of_loops:                       80
% 23.93/3.53  res_forward_subset_subsumed:            516
% 23.93/3.53  res_backward_subset_subsumed:           0
% 23.93/3.53  res_forward_subsumed:                   0
% 23.93/3.53  res_backward_subsumed:                  0
% 23.93/3.53  res_forward_subsumption_resolution:     0
% 23.93/3.53  res_backward_subsumption_resolution:    0
% 23.93/3.53  res_clause_to_clause_subsumption:       50763
% 23.93/3.53  res_orphan_elimination:                 0
% 23.93/3.53  res_tautology_del:                      264
% 23.93/3.53  res_num_eq_res_simplified:              0
% 23.93/3.53  res_num_sel_changes:                    0
% 23.93/3.53  res_moves_from_active_to_pass:          0
% 23.93/3.53  
% 23.93/3.53  ------ Superposition
% 23.93/3.53  
% 23.93/3.53  sup_time_total:                         0.
% 23.93/3.53  sup_time_generating:                    0.
% 23.93/3.53  sup_time_sim_full:                      0.
% 23.93/3.53  sup_time_sim_immed:                     0.
% 23.93/3.53  
% 23.93/3.53  sup_num_of_clauses:                     5997
% 23.93/3.53  sup_num_in_active:                      172
% 23.93/3.53  sup_num_in_passive:                     5825
% 23.93/3.53  sup_num_of_loops:                       206
% 23.93/3.53  sup_fw_superposition:                   11444
% 23.93/3.53  sup_bw_superposition:                   16125
% 23.93/3.53  sup_immediate_simplified:               10534
% 23.93/3.53  sup_given_eliminated:                   4
% 23.93/3.53  comparisons_done:                       0
% 23.93/3.53  comparisons_avoided:                    0
% 23.93/3.53  
% 23.93/3.53  ------ Simplifications
% 23.93/3.53  
% 23.93/3.53  
% 23.93/3.53  sim_fw_subset_subsumed:                 1
% 23.93/3.53  sim_bw_subset_subsumed:                 2
% 23.93/3.53  sim_fw_subsumed:                        4689
% 23.93/3.53  sim_bw_subsumed:                        190
% 23.93/3.53  sim_fw_subsumption_res:                 0
% 23.93/3.53  sim_bw_subsumption_res:                 0
% 23.93/3.53  sim_tautology_del:                      0
% 23.93/3.53  sim_eq_tautology_del:                   921
% 23.93/3.53  sim_eq_res_simp:                        3
% 23.93/3.53  sim_fw_demodulated:                     7526
% 23.93/3.53  sim_bw_demodulated:                     233
% 23.93/3.53  sim_light_normalised:                   2655
% 23.93/3.53  sim_joinable_taut:                      0
% 23.93/3.53  sim_joinable_simp:                      0
% 23.93/3.53  sim_ac_normalised:                      0
% 23.93/3.53  sim_smt_subsumption:                    0
% 23.93/3.53  
%------------------------------------------------------------------------------
