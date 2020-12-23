%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:07 EST 2020

% Result     : Theorem 19.81s
% Output     : CNFRefutation 19.81s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 225 expanded)
%              Number of clauses        :   43 (  67 expanded)
%              Number of leaves         :    9 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  180 ( 802 expanded)
%              Number of equality atoms :   48 ( 101 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,
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

fof(f27,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).

fof(f42,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f37,f36,f36])).

fof(f44,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f45,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_491,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_494,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_869,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_491,c_494])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_190,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_191,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_195,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_191,c_16,c_15])).

cnf(c_1453,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_869,c_195])).

cnf(c_10,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_175,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_176,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_180,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_176,c_16,c_15])).

cnf(c_490,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1460,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_490])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_492,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_204,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_205,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
    | ~ r1_tarski(X0,k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_489,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_205])).

cnf(c_871,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_494])).

cnf(c_7,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_870,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_490,c_494])).

cnf(c_3130,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_870])).

cnf(c_5523,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_871,c_3130])).

cnf(c_5531,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_492,c_5523])).

cnf(c_47007,plain,
    ( r1_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1460,c_5531])).

cnf(c_47012,plain,
    ( k1_setfam_1(k2_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1)))) = sK0 ),
    inference(superposition,[status(thm)],[c_47007,c_494])).

cnf(c_5,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_495,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_894,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_495,c_494])).

cnf(c_9521,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_894])).

cnf(c_47378,plain,
    ( k1_setfam_1(k2_tarski(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_47012,c_9521])).

cnf(c_892,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_495])).

cnf(c_47760,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_47378,c_892])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47760,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:36:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 19.81/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.81/3.00  
% 19.81/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.81/3.00  
% 19.81/3.00  ------  iProver source info
% 19.81/3.00  
% 19.81/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.81/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.81/3.00  git: non_committed_changes: false
% 19.81/3.00  git: last_make_outside_of_git: false
% 19.81/3.00  
% 19.81/3.00  ------ 
% 19.81/3.00  
% 19.81/3.00  ------ Input Options
% 19.81/3.00  
% 19.81/3.00  --out_options                           all
% 19.81/3.00  --tptp_safe_out                         true
% 19.81/3.00  --problem_path                          ""
% 19.81/3.00  --include_path                          ""
% 19.81/3.00  --clausifier                            res/vclausify_rel
% 19.81/3.00  --clausifier_options                    --mode clausify
% 19.81/3.00  --stdin                                 false
% 19.81/3.00  --stats_out                             all
% 19.81/3.00  
% 19.81/3.00  ------ General Options
% 19.81/3.00  
% 19.81/3.00  --fof                                   false
% 19.81/3.00  --time_out_real                         305.
% 19.81/3.00  --time_out_virtual                      -1.
% 19.81/3.00  --symbol_type_check                     false
% 19.81/3.00  --clausify_out                          false
% 19.81/3.00  --sig_cnt_out                           false
% 19.81/3.00  --trig_cnt_out                          false
% 19.81/3.00  --trig_cnt_out_tolerance                1.
% 19.81/3.00  --trig_cnt_out_sk_spl                   false
% 19.81/3.00  --abstr_cl_out                          false
% 19.81/3.00  
% 19.81/3.00  ------ Global Options
% 19.81/3.00  
% 19.81/3.00  --schedule                              default
% 19.81/3.00  --add_important_lit                     false
% 19.81/3.00  --prop_solver_per_cl                    1000
% 19.81/3.00  --min_unsat_core                        false
% 19.81/3.00  --soft_assumptions                      false
% 19.81/3.00  --soft_lemma_size                       3
% 19.81/3.00  --prop_impl_unit_size                   0
% 19.81/3.00  --prop_impl_unit                        []
% 19.81/3.00  --share_sel_clauses                     true
% 19.81/3.00  --reset_solvers                         false
% 19.81/3.00  --bc_imp_inh                            [conj_cone]
% 19.81/3.00  --conj_cone_tolerance                   3.
% 19.81/3.00  --extra_neg_conj                        none
% 19.81/3.00  --large_theory_mode                     true
% 19.81/3.00  --prolific_symb_bound                   200
% 19.81/3.00  --lt_threshold                          2000
% 19.81/3.00  --clause_weak_htbl                      true
% 19.81/3.00  --gc_record_bc_elim                     false
% 19.81/3.00  
% 19.81/3.00  ------ Preprocessing Options
% 19.81/3.00  
% 19.81/3.00  --preprocessing_flag                    true
% 19.81/3.00  --time_out_prep_mult                    0.1
% 19.81/3.00  --splitting_mode                        input
% 19.81/3.00  --splitting_grd                         true
% 19.81/3.00  --splitting_cvd                         false
% 19.81/3.00  --splitting_cvd_svl                     false
% 19.81/3.00  --splitting_nvd                         32
% 19.81/3.00  --sub_typing                            true
% 19.81/3.00  --prep_gs_sim                           true
% 19.81/3.00  --prep_unflatten                        true
% 19.81/3.00  --prep_res_sim                          true
% 19.81/3.00  --prep_upred                            true
% 19.81/3.00  --prep_sem_filter                       exhaustive
% 19.81/3.00  --prep_sem_filter_out                   false
% 19.81/3.00  --pred_elim                             true
% 19.81/3.00  --res_sim_input                         true
% 19.81/3.00  --eq_ax_congr_red                       true
% 19.81/3.00  --pure_diseq_elim                       true
% 19.81/3.00  --brand_transform                       false
% 19.81/3.00  --non_eq_to_eq                          false
% 19.81/3.00  --prep_def_merge                        true
% 19.81/3.00  --prep_def_merge_prop_impl              false
% 19.81/3.00  --prep_def_merge_mbd                    true
% 19.81/3.00  --prep_def_merge_tr_red                 false
% 19.81/3.00  --prep_def_merge_tr_cl                  false
% 19.81/3.00  --smt_preprocessing                     true
% 19.81/3.00  --smt_ac_axioms                         fast
% 19.81/3.00  --preprocessed_out                      false
% 19.81/3.00  --preprocessed_stats                    false
% 19.81/3.00  
% 19.81/3.00  ------ Abstraction refinement Options
% 19.81/3.00  
% 19.81/3.00  --abstr_ref                             []
% 19.81/3.00  --abstr_ref_prep                        false
% 19.81/3.00  --abstr_ref_until_sat                   false
% 19.81/3.00  --abstr_ref_sig_restrict                funpre
% 19.81/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.81/3.00  --abstr_ref_under                       []
% 19.81/3.00  
% 19.81/3.00  ------ SAT Options
% 19.81/3.00  
% 19.81/3.00  --sat_mode                              false
% 19.81/3.00  --sat_fm_restart_options                ""
% 19.81/3.00  --sat_gr_def                            false
% 19.81/3.00  --sat_epr_types                         true
% 19.81/3.00  --sat_non_cyclic_types                  false
% 19.81/3.00  --sat_finite_models                     false
% 19.81/3.00  --sat_fm_lemmas                         false
% 19.81/3.00  --sat_fm_prep                           false
% 19.81/3.00  --sat_fm_uc_incr                        true
% 19.81/3.00  --sat_out_model                         small
% 19.81/3.00  --sat_out_clauses                       false
% 19.81/3.00  
% 19.81/3.00  ------ QBF Options
% 19.81/3.00  
% 19.81/3.00  --qbf_mode                              false
% 19.81/3.00  --qbf_elim_univ                         false
% 19.81/3.00  --qbf_dom_inst                          none
% 19.81/3.00  --qbf_dom_pre_inst                      false
% 19.81/3.00  --qbf_sk_in                             false
% 19.81/3.00  --qbf_pred_elim                         true
% 19.81/3.00  --qbf_split                             512
% 19.81/3.00  
% 19.81/3.00  ------ BMC1 Options
% 19.81/3.00  
% 19.81/3.00  --bmc1_incremental                      false
% 19.81/3.00  --bmc1_axioms                           reachable_all
% 19.81/3.00  --bmc1_min_bound                        0
% 19.81/3.00  --bmc1_max_bound                        -1
% 19.81/3.00  --bmc1_max_bound_default                -1
% 19.81/3.00  --bmc1_symbol_reachability              true
% 19.81/3.00  --bmc1_property_lemmas                  false
% 19.81/3.00  --bmc1_k_induction                      false
% 19.81/3.00  --bmc1_non_equiv_states                 false
% 19.81/3.00  --bmc1_deadlock                         false
% 19.81/3.00  --bmc1_ucm                              false
% 19.81/3.00  --bmc1_add_unsat_core                   none
% 19.81/3.00  --bmc1_unsat_core_children              false
% 19.81/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.81/3.00  --bmc1_out_stat                         full
% 19.81/3.00  --bmc1_ground_init                      false
% 19.81/3.00  --bmc1_pre_inst_next_state              false
% 19.81/3.00  --bmc1_pre_inst_state                   false
% 19.81/3.00  --bmc1_pre_inst_reach_state             false
% 19.81/3.00  --bmc1_out_unsat_core                   false
% 19.81/3.00  --bmc1_aig_witness_out                  false
% 19.81/3.00  --bmc1_verbose                          false
% 19.81/3.00  --bmc1_dump_clauses_tptp                false
% 19.81/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.81/3.00  --bmc1_dump_file                        -
% 19.81/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.81/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.81/3.00  --bmc1_ucm_extend_mode                  1
% 19.81/3.00  --bmc1_ucm_init_mode                    2
% 19.81/3.00  --bmc1_ucm_cone_mode                    none
% 19.81/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.81/3.00  --bmc1_ucm_relax_model                  4
% 19.81/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.81/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.81/3.00  --bmc1_ucm_layered_model                none
% 19.81/3.00  --bmc1_ucm_max_lemma_size               10
% 19.81/3.00  
% 19.81/3.00  ------ AIG Options
% 19.81/3.00  
% 19.81/3.00  --aig_mode                              false
% 19.81/3.00  
% 19.81/3.00  ------ Instantiation Options
% 19.81/3.00  
% 19.81/3.00  --instantiation_flag                    true
% 19.81/3.00  --inst_sos_flag                         false
% 19.81/3.00  --inst_sos_phase                        true
% 19.81/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.81/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.81/3.00  --inst_lit_sel_side                     num_symb
% 19.81/3.00  --inst_solver_per_active                1400
% 19.81/3.00  --inst_solver_calls_frac                1.
% 19.81/3.00  --inst_passive_queue_type               priority_queues
% 19.81/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.81/3.00  --inst_passive_queues_freq              [25;2]
% 19.81/3.00  --inst_dismatching                      true
% 19.81/3.00  --inst_eager_unprocessed_to_passive     true
% 19.81/3.00  --inst_prop_sim_given                   true
% 19.81/3.00  --inst_prop_sim_new                     false
% 19.81/3.00  --inst_subs_new                         false
% 19.81/3.00  --inst_eq_res_simp                      false
% 19.81/3.00  --inst_subs_given                       false
% 19.81/3.00  --inst_orphan_elimination               true
% 19.81/3.00  --inst_learning_loop_flag               true
% 19.81/3.00  --inst_learning_start                   3000
% 19.81/3.00  --inst_learning_factor                  2
% 19.81/3.00  --inst_start_prop_sim_after_learn       3
% 19.81/3.00  --inst_sel_renew                        solver
% 19.81/3.00  --inst_lit_activity_flag                true
% 19.81/3.00  --inst_restr_to_given                   false
% 19.81/3.00  --inst_activity_threshold               500
% 19.81/3.00  --inst_out_proof                        true
% 19.81/3.00  
% 19.81/3.00  ------ Resolution Options
% 19.81/3.00  
% 19.81/3.00  --resolution_flag                       true
% 19.81/3.00  --res_lit_sel                           adaptive
% 19.81/3.00  --res_lit_sel_side                      none
% 19.81/3.00  --res_ordering                          kbo
% 19.81/3.00  --res_to_prop_solver                    active
% 19.81/3.00  --res_prop_simpl_new                    false
% 19.81/3.00  --res_prop_simpl_given                  true
% 19.81/3.00  --res_passive_queue_type                priority_queues
% 19.81/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.81/3.00  --res_passive_queues_freq               [15;5]
% 19.81/3.00  --res_forward_subs                      full
% 19.81/3.00  --res_backward_subs                     full
% 19.81/3.00  --res_forward_subs_resolution           true
% 19.81/3.00  --res_backward_subs_resolution          true
% 19.81/3.00  --res_orphan_elimination                true
% 19.81/3.00  --res_time_limit                        2.
% 19.81/3.00  --res_out_proof                         true
% 19.81/3.00  
% 19.81/3.00  ------ Superposition Options
% 19.81/3.00  
% 19.81/3.00  --superposition_flag                    true
% 19.81/3.00  --sup_passive_queue_type                priority_queues
% 19.81/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.81/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.81/3.00  --demod_completeness_check              fast
% 19.81/3.00  --demod_use_ground                      true
% 19.81/3.00  --sup_to_prop_solver                    passive
% 19.81/3.00  --sup_prop_simpl_new                    true
% 19.81/3.00  --sup_prop_simpl_given                  true
% 19.81/3.00  --sup_fun_splitting                     false
% 19.81/3.00  --sup_smt_interval                      50000
% 19.81/3.00  
% 19.81/3.00  ------ Superposition Simplification Setup
% 19.81/3.00  
% 19.81/3.00  --sup_indices_passive                   []
% 19.81/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.81/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.81/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.81/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.81/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.81/3.00  --sup_full_bw                           [BwDemod]
% 19.81/3.00  --sup_immed_triv                        [TrivRules]
% 19.81/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.81/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.81/3.00  --sup_immed_bw_main                     []
% 19.81/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.81/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.81/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.81/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.81/3.00  
% 19.81/3.00  ------ Combination Options
% 19.81/3.00  
% 19.81/3.00  --comb_res_mult                         3
% 19.81/3.00  --comb_sup_mult                         2
% 19.81/3.00  --comb_inst_mult                        10
% 19.81/3.00  
% 19.81/3.00  ------ Debug Options
% 19.81/3.00  
% 19.81/3.00  --dbg_backtrace                         false
% 19.81/3.00  --dbg_dump_prop_clauses                 false
% 19.81/3.00  --dbg_dump_prop_clauses_file            -
% 19.81/3.00  --dbg_out_stat                          false
% 19.81/3.00  ------ Parsing...
% 19.81/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.81/3.00  
% 19.81/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 19.81/3.00  
% 19.81/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.81/3.00  
% 19.81/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.81/3.00  ------ Proving...
% 19.81/3.00  ------ Problem Properties 
% 19.81/3.00  
% 19.81/3.00  
% 19.81/3.00  clauses                                 13
% 19.81/3.00  conjectures                             3
% 19.81/3.00  EPR                                     3
% 19.81/3.00  Horn                                    13
% 19.81/3.00  unary                                   8
% 19.81/3.00  binary                                  4
% 19.81/3.00  lits                                    19
% 19.81/3.00  lits eq                                 5
% 19.81/3.00  fd_pure                                 0
% 19.81/3.00  fd_pseudo                               0
% 19.81/3.00  fd_cond                                 0
% 19.81/3.00  fd_pseudo_cond                          1
% 19.81/3.00  AC symbols                              0
% 19.81/3.00  
% 19.81/3.00  ------ Schedule dynamic 5 is on 
% 19.81/3.00  
% 19.81/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.81/3.00  
% 19.81/3.00  
% 19.81/3.00  ------ 
% 19.81/3.00  Current options:
% 19.81/3.00  ------ 
% 19.81/3.00  
% 19.81/3.00  ------ Input Options
% 19.81/3.00  
% 19.81/3.00  --out_options                           all
% 19.81/3.00  --tptp_safe_out                         true
% 19.81/3.00  --problem_path                          ""
% 19.81/3.00  --include_path                          ""
% 19.81/3.00  --clausifier                            res/vclausify_rel
% 19.81/3.00  --clausifier_options                    --mode clausify
% 19.81/3.00  --stdin                                 false
% 19.81/3.00  --stats_out                             all
% 19.81/3.00  
% 19.81/3.00  ------ General Options
% 19.81/3.00  
% 19.81/3.00  --fof                                   false
% 19.81/3.00  --time_out_real                         305.
% 19.81/3.00  --time_out_virtual                      -1.
% 19.81/3.00  --symbol_type_check                     false
% 19.81/3.00  --clausify_out                          false
% 19.81/3.00  --sig_cnt_out                           false
% 19.81/3.00  --trig_cnt_out                          false
% 19.81/3.00  --trig_cnt_out_tolerance                1.
% 19.81/3.00  --trig_cnt_out_sk_spl                   false
% 19.81/3.00  --abstr_cl_out                          false
% 19.81/3.00  
% 19.81/3.00  ------ Global Options
% 19.81/3.00  
% 19.81/3.00  --schedule                              default
% 19.81/3.00  --add_important_lit                     false
% 19.81/3.00  --prop_solver_per_cl                    1000
% 19.81/3.00  --min_unsat_core                        false
% 19.81/3.00  --soft_assumptions                      false
% 19.81/3.00  --soft_lemma_size                       3
% 19.81/3.00  --prop_impl_unit_size                   0
% 19.81/3.00  --prop_impl_unit                        []
% 19.81/3.00  --share_sel_clauses                     true
% 19.81/3.00  --reset_solvers                         false
% 19.81/3.00  --bc_imp_inh                            [conj_cone]
% 19.81/3.00  --conj_cone_tolerance                   3.
% 19.81/3.00  --extra_neg_conj                        none
% 19.81/3.00  --large_theory_mode                     true
% 19.81/3.00  --prolific_symb_bound                   200
% 19.81/3.00  --lt_threshold                          2000
% 19.81/3.00  --clause_weak_htbl                      true
% 19.81/3.00  --gc_record_bc_elim                     false
% 19.81/3.00  
% 19.81/3.00  ------ Preprocessing Options
% 19.81/3.00  
% 19.81/3.00  --preprocessing_flag                    true
% 19.81/3.00  --time_out_prep_mult                    0.1
% 19.81/3.00  --splitting_mode                        input
% 19.81/3.00  --splitting_grd                         true
% 19.81/3.00  --splitting_cvd                         false
% 19.81/3.00  --splitting_cvd_svl                     false
% 19.81/3.00  --splitting_nvd                         32
% 19.81/3.00  --sub_typing                            true
% 19.81/3.00  --prep_gs_sim                           true
% 19.81/3.00  --prep_unflatten                        true
% 19.81/3.00  --prep_res_sim                          true
% 19.81/3.00  --prep_upred                            true
% 19.81/3.00  --prep_sem_filter                       exhaustive
% 19.81/3.00  --prep_sem_filter_out                   false
% 19.81/3.00  --pred_elim                             true
% 19.81/3.00  --res_sim_input                         true
% 19.81/3.00  --eq_ax_congr_red                       true
% 19.81/3.00  --pure_diseq_elim                       true
% 19.81/3.00  --brand_transform                       false
% 19.81/3.00  --non_eq_to_eq                          false
% 19.81/3.00  --prep_def_merge                        true
% 19.81/3.00  --prep_def_merge_prop_impl              false
% 19.81/3.00  --prep_def_merge_mbd                    true
% 19.81/3.00  --prep_def_merge_tr_red                 false
% 19.81/3.00  --prep_def_merge_tr_cl                  false
% 19.81/3.00  --smt_preprocessing                     true
% 19.81/3.00  --smt_ac_axioms                         fast
% 19.81/3.00  --preprocessed_out                      false
% 19.81/3.00  --preprocessed_stats                    false
% 19.81/3.00  
% 19.81/3.00  ------ Abstraction refinement Options
% 19.81/3.00  
% 19.81/3.00  --abstr_ref                             []
% 19.81/3.00  --abstr_ref_prep                        false
% 19.81/3.00  --abstr_ref_until_sat                   false
% 19.81/3.00  --abstr_ref_sig_restrict                funpre
% 19.81/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.81/3.00  --abstr_ref_under                       []
% 19.81/3.00  
% 19.81/3.00  ------ SAT Options
% 19.81/3.00  
% 19.81/3.00  --sat_mode                              false
% 19.81/3.00  --sat_fm_restart_options                ""
% 19.81/3.00  --sat_gr_def                            false
% 19.81/3.00  --sat_epr_types                         true
% 19.81/3.00  --sat_non_cyclic_types                  false
% 19.81/3.00  --sat_finite_models                     false
% 19.81/3.00  --sat_fm_lemmas                         false
% 19.81/3.00  --sat_fm_prep                           false
% 19.81/3.00  --sat_fm_uc_incr                        true
% 19.81/3.00  --sat_out_model                         small
% 19.81/3.00  --sat_out_clauses                       false
% 19.81/3.00  
% 19.81/3.00  ------ QBF Options
% 19.81/3.00  
% 19.81/3.00  --qbf_mode                              false
% 19.81/3.00  --qbf_elim_univ                         false
% 19.81/3.00  --qbf_dom_inst                          none
% 19.81/3.00  --qbf_dom_pre_inst                      false
% 19.81/3.00  --qbf_sk_in                             false
% 19.81/3.00  --qbf_pred_elim                         true
% 19.81/3.00  --qbf_split                             512
% 19.81/3.00  
% 19.81/3.00  ------ BMC1 Options
% 19.81/3.00  
% 19.81/3.00  --bmc1_incremental                      false
% 19.81/3.00  --bmc1_axioms                           reachable_all
% 19.81/3.00  --bmc1_min_bound                        0
% 19.81/3.00  --bmc1_max_bound                        -1
% 19.81/3.00  --bmc1_max_bound_default                -1
% 19.81/3.00  --bmc1_symbol_reachability              true
% 19.81/3.00  --bmc1_property_lemmas                  false
% 19.81/3.00  --bmc1_k_induction                      false
% 19.81/3.00  --bmc1_non_equiv_states                 false
% 19.81/3.00  --bmc1_deadlock                         false
% 19.81/3.00  --bmc1_ucm                              false
% 19.81/3.00  --bmc1_add_unsat_core                   none
% 19.81/3.00  --bmc1_unsat_core_children              false
% 19.81/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.81/3.00  --bmc1_out_stat                         full
% 19.81/3.00  --bmc1_ground_init                      false
% 19.81/3.00  --bmc1_pre_inst_next_state              false
% 19.81/3.00  --bmc1_pre_inst_state                   false
% 19.81/3.00  --bmc1_pre_inst_reach_state             false
% 19.81/3.00  --bmc1_out_unsat_core                   false
% 19.81/3.00  --bmc1_aig_witness_out                  false
% 19.81/3.00  --bmc1_verbose                          false
% 19.81/3.00  --bmc1_dump_clauses_tptp                false
% 19.81/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.81/3.00  --bmc1_dump_file                        -
% 19.81/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.81/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.81/3.00  --bmc1_ucm_extend_mode                  1
% 19.81/3.00  --bmc1_ucm_init_mode                    2
% 19.81/3.00  --bmc1_ucm_cone_mode                    none
% 19.81/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.81/3.00  --bmc1_ucm_relax_model                  4
% 19.81/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.81/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.81/3.00  --bmc1_ucm_layered_model                none
% 19.81/3.00  --bmc1_ucm_max_lemma_size               10
% 19.81/3.00  
% 19.81/3.00  ------ AIG Options
% 19.81/3.00  
% 19.81/3.00  --aig_mode                              false
% 19.81/3.00  
% 19.81/3.00  ------ Instantiation Options
% 19.81/3.00  
% 19.81/3.00  --instantiation_flag                    true
% 19.81/3.00  --inst_sos_flag                         false
% 19.81/3.00  --inst_sos_phase                        true
% 19.81/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.81/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.81/3.00  --inst_lit_sel_side                     none
% 19.81/3.00  --inst_solver_per_active                1400
% 19.81/3.00  --inst_solver_calls_frac                1.
% 19.81/3.00  --inst_passive_queue_type               priority_queues
% 19.81/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.81/3.00  --inst_passive_queues_freq              [25;2]
% 19.81/3.00  --inst_dismatching                      true
% 19.81/3.00  --inst_eager_unprocessed_to_passive     true
% 19.81/3.00  --inst_prop_sim_given                   true
% 19.81/3.00  --inst_prop_sim_new                     false
% 19.81/3.00  --inst_subs_new                         false
% 19.81/3.00  --inst_eq_res_simp                      false
% 19.81/3.00  --inst_subs_given                       false
% 19.81/3.00  --inst_orphan_elimination               true
% 19.81/3.00  --inst_learning_loop_flag               true
% 19.81/3.00  --inst_learning_start                   3000
% 19.81/3.00  --inst_learning_factor                  2
% 19.81/3.00  --inst_start_prop_sim_after_learn       3
% 19.81/3.00  --inst_sel_renew                        solver
% 19.81/3.00  --inst_lit_activity_flag                true
% 19.81/3.00  --inst_restr_to_given                   false
% 19.81/3.00  --inst_activity_threshold               500
% 19.81/3.00  --inst_out_proof                        true
% 19.81/3.00  
% 19.81/3.00  ------ Resolution Options
% 19.81/3.00  
% 19.81/3.00  --resolution_flag                       false
% 19.81/3.00  --res_lit_sel                           adaptive
% 19.81/3.00  --res_lit_sel_side                      none
% 19.81/3.00  --res_ordering                          kbo
% 19.81/3.00  --res_to_prop_solver                    active
% 19.81/3.00  --res_prop_simpl_new                    false
% 19.81/3.00  --res_prop_simpl_given                  true
% 19.81/3.00  --res_passive_queue_type                priority_queues
% 19.81/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.81/3.00  --res_passive_queues_freq               [15;5]
% 19.81/3.00  --res_forward_subs                      full
% 19.81/3.00  --res_backward_subs                     full
% 19.81/3.00  --res_forward_subs_resolution           true
% 19.81/3.00  --res_backward_subs_resolution          true
% 19.81/3.00  --res_orphan_elimination                true
% 19.81/3.00  --res_time_limit                        2.
% 19.81/3.00  --res_out_proof                         true
% 19.81/3.00  
% 19.81/3.00  ------ Superposition Options
% 19.81/3.00  
% 19.81/3.00  --superposition_flag                    true
% 19.81/3.00  --sup_passive_queue_type                priority_queues
% 19.81/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.81/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.81/3.00  --demod_completeness_check              fast
% 19.81/3.00  --demod_use_ground                      true
% 19.81/3.00  --sup_to_prop_solver                    passive
% 19.81/3.00  --sup_prop_simpl_new                    true
% 19.81/3.00  --sup_prop_simpl_given                  true
% 19.81/3.00  --sup_fun_splitting                     false
% 19.81/3.00  --sup_smt_interval                      50000
% 19.81/3.00  
% 19.81/3.00  ------ Superposition Simplification Setup
% 19.81/3.00  
% 19.81/3.00  --sup_indices_passive                   []
% 19.81/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.81/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.81/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.81/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.81/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.81/3.00  --sup_full_bw                           [BwDemod]
% 19.81/3.00  --sup_immed_triv                        [TrivRules]
% 19.81/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.81/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.81/3.00  --sup_immed_bw_main                     []
% 19.81/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.81/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.81/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.81/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.81/3.00  
% 19.81/3.00  ------ Combination Options
% 19.81/3.00  
% 19.81/3.00  --comb_res_mult                         3
% 19.81/3.00  --comb_sup_mult                         2
% 19.81/3.00  --comb_inst_mult                        10
% 19.81/3.00  
% 19.81/3.00  ------ Debug Options
% 19.81/3.00  
% 19.81/3.00  --dbg_backtrace                         false
% 19.81/3.00  --dbg_dump_prop_clauses                 false
% 19.81/3.00  --dbg_dump_prop_clauses_file            -
% 19.81/3.00  --dbg_out_stat                          false
% 19.81/3.00  
% 19.81/3.00  
% 19.81/3.00  
% 19.81/3.00  
% 19.81/3.00  ------ Proving...
% 19.81/3.00  
% 19.81/3.00  
% 19.81/3.00  % SZS status Theorem for theBenchmark.p
% 19.81/3.00  
% 19.81/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.81/3.00  
% 19.81/3.00  fof(f11,conjecture,(
% 19.81/3.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 19.81/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.81/3.00  
% 19.81/3.00  fof(f12,negated_conjecture,(
% 19.81/3.00    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 19.81/3.00    inference(negated_conjecture,[],[f11])).
% 19.81/3.00  
% 19.81/3.00  fof(f22,plain,(
% 19.81/3.00    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 19.81/3.00    inference(ennf_transformation,[],[f12])).
% 19.81/3.00  
% 19.81/3.00  fof(f23,plain,(
% 19.81/3.00    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 19.81/3.00    inference(flattening,[],[f22])).
% 19.81/3.00  
% 19.81/3.00  fof(f26,plain,(
% 19.81/3.00    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 19.81/3.00    introduced(choice_axiom,[])).
% 19.81/3.00  
% 19.81/3.00  fof(f27,plain,(
% 19.81/3.00    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 19.81/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).
% 19.81/3.00  
% 19.81/3.00  fof(f42,plain,(
% 19.81/3.00    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 19.81/3.00    inference(cnf_transformation,[],[f27])).
% 19.81/3.00  
% 19.81/3.00  fof(f5,axiom,(
% 19.81/3.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.81/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.81/3.00  
% 19.81/3.00  fof(f15,plain,(
% 19.81/3.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.81/3.00    inference(ennf_transformation,[],[f5])).
% 19.81/3.00  
% 19.81/3.00  fof(f34,plain,(
% 19.81/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.81/3.00    inference(cnf_transformation,[],[f15])).
% 19.81/3.00  
% 19.81/3.00  fof(f7,axiom,(
% 19.81/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.81/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.81/3.00  
% 19.81/3.00  fof(f36,plain,(
% 19.81/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.81/3.00    inference(cnf_transformation,[],[f7])).
% 19.81/3.00  
% 19.81/3.00  fof(f47,plain,(
% 19.81/3.00    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 19.81/3.00    inference(definition_unfolding,[],[f34,f36])).
% 19.81/3.00  
% 19.81/3.00  fof(f8,axiom,(
% 19.81/3.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 19.81/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.81/3.00  
% 19.81/3.00  fof(f16,plain,(
% 19.81/3.00    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 19.81/3.00    inference(ennf_transformation,[],[f8])).
% 19.81/3.00  
% 19.81/3.00  fof(f17,plain,(
% 19.81/3.00    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.81/3.00    inference(flattening,[],[f16])).
% 19.81/3.00  
% 19.81/3.00  fof(f37,plain,(
% 19.81/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.81/3.00    inference(cnf_transformation,[],[f17])).
% 19.81/3.00  
% 19.81/3.00  fof(f48,plain,(
% 19.81/3.00    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.81/3.00    inference(definition_unfolding,[],[f37,f36,f36])).
% 19.81/3.00  
% 19.81/3.00  fof(f44,plain,(
% 19.81/3.00    v2_funct_1(sK2)),
% 19.81/3.00    inference(cnf_transformation,[],[f27])).
% 19.81/3.00  
% 19.81/3.00  fof(f40,plain,(
% 19.81/3.00    v1_relat_1(sK2)),
% 19.81/3.00    inference(cnf_transformation,[],[f27])).
% 19.81/3.00  
% 19.81/3.00  fof(f41,plain,(
% 19.81/3.00    v1_funct_1(sK2)),
% 19.81/3.00    inference(cnf_transformation,[],[f27])).
% 19.81/3.00  
% 19.81/3.00  fof(f10,axiom,(
% 19.81/3.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 19.81/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.81/3.00  
% 19.81/3.00  fof(f20,plain,(
% 19.81/3.00    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.81/3.00    inference(ennf_transformation,[],[f10])).
% 19.81/3.00  
% 19.81/3.00  fof(f21,plain,(
% 19.81/3.00    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.81/3.00    inference(flattening,[],[f20])).
% 19.81/3.00  
% 19.81/3.00  fof(f39,plain,(
% 19.81/3.00    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.81/3.00    inference(cnf_transformation,[],[f21])).
% 19.81/3.00  
% 19.81/3.00  fof(f43,plain,(
% 19.81/3.00    r1_tarski(sK0,k1_relat_1(sK2))),
% 19.81/3.00    inference(cnf_transformation,[],[f27])).
% 19.81/3.00  
% 19.81/3.00  fof(f9,axiom,(
% 19.81/3.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 19.81/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.81/3.00  
% 19.81/3.00  fof(f18,plain,(
% 19.81/3.00    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 19.81/3.00    inference(ennf_transformation,[],[f9])).
% 19.81/3.00  
% 19.81/3.00  fof(f19,plain,(
% 19.81/3.00    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.81/3.00    inference(flattening,[],[f18])).
% 19.81/3.00  
% 19.81/3.00  fof(f38,plain,(
% 19.81/3.00    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.81/3.00    inference(cnf_transformation,[],[f19])).
% 19.81/3.00  
% 19.81/3.00  fof(f6,axiom,(
% 19.81/3.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 19.81/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.81/3.00  
% 19.81/3.00  fof(f35,plain,(
% 19.81/3.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 19.81/3.00    inference(cnf_transformation,[],[f6])).
% 19.81/3.00  
% 19.81/3.00  fof(f4,axiom,(
% 19.81/3.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.81/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.81/3.00  
% 19.81/3.00  fof(f33,plain,(
% 19.81/3.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.81/3.00    inference(cnf_transformation,[],[f4])).
% 19.81/3.00  
% 19.81/3.00  fof(f46,plain,(
% 19.81/3.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 19.81/3.00    inference(definition_unfolding,[],[f33,f36])).
% 19.81/3.00  
% 19.81/3.00  fof(f45,plain,(
% 19.81/3.00    ~r1_tarski(sK0,sK1)),
% 19.81/3.00    inference(cnf_transformation,[],[f27])).
% 19.81/3.00  
% 19.81/3.00  cnf(c_14,negated_conjecture,
% 19.81/3.00      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 19.81/3.00      inference(cnf_transformation,[],[f42]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_491,plain,
% 19.81/3.00      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 19.81/3.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_6,plain,
% 19.81/3.00      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 19.81/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_494,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 19.81/3.00      | r1_tarski(X0,X1) != iProver_top ),
% 19.81/3.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_869,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k9_relat_1(sK2,sK0) ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_491,c_494]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_8,plain,
% 19.81/3.00      ( ~ v1_relat_1(X0)
% 19.81/3.00      | ~ v1_funct_1(X0)
% 19.81/3.00      | ~ v2_funct_1(X0)
% 19.81/3.00      | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 19.81/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_12,negated_conjecture,
% 19.81/3.00      ( v2_funct_1(sK2) ),
% 19.81/3.00      inference(cnf_transformation,[],[f44]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_190,plain,
% 19.81/3.00      ( ~ v1_relat_1(X0)
% 19.81/3.00      | ~ v1_funct_1(X0)
% 19.81/3.00      | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 19.81/3.00      | sK2 != X0 ),
% 19.81/3.00      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_191,plain,
% 19.81/3.00      ( ~ v1_relat_1(sK2)
% 19.81/3.00      | ~ v1_funct_1(sK2)
% 19.81/3.00      | k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 19.81/3.00      inference(unflattening,[status(thm)],[c_190]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_16,negated_conjecture,
% 19.81/3.00      ( v1_relat_1(sK2) ),
% 19.81/3.00      inference(cnf_transformation,[],[f40]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_15,negated_conjecture,
% 19.81/3.00      ( v1_funct_1(sK2) ),
% 19.81/3.00      inference(cnf_transformation,[],[f41]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_195,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 19.81/3.00      inference(global_propositional_subsumption,
% 19.81/3.00                [status(thm)],
% 19.81/3.00                [c_191,c_16,c_15]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_1453,plain,
% 19.81/3.00      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) = k9_relat_1(sK2,sK0) ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_869,c_195]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_10,plain,
% 19.81/3.00      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 19.81/3.00      | ~ v1_relat_1(X0)
% 19.81/3.00      | ~ v1_funct_1(X0)
% 19.81/3.00      | ~ v2_funct_1(X0) ),
% 19.81/3.00      inference(cnf_transformation,[],[f39]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_175,plain,
% 19.81/3.00      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 19.81/3.00      | ~ v1_relat_1(X0)
% 19.81/3.00      | ~ v1_funct_1(X0)
% 19.81/3.00      | sK2 != X0 ),
% 19.81/3.00      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_176,plain,
% 19.81/3.00      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
% 19.81/3.00      | ~ v1_relat_1(sK2)
% 19.81/3.00      | ~ v1_funct_1(sK2) ),
% 19.81/3.00      inference(unflattening,[status(thm)],[c_175]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_180,plain,
% 19.81/3.00      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
% 19.81/3.00      inference(global_propositional_subsumption,
% 19.81/3.00                [status(thm)],
% 19.81/3.00                [c_176,c_16,c_15]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_490,plain,
% 19.81/3.00      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = iProver_top ),
% 19.81/3.00      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_1460,plain,
% 19.81/3.00      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_1453,c_490]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_13,negated_conjecture,
% 19.81/3.00      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 19.81/3.00      inference(cnf_transformation,[],[f43]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_492,plain,
% 19.81/3.00      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 19.81/3.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_9,plain,
% 19.81/3.00      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 19.81/3.00      | ~ r1_tarski(X0,k1_relat_1(X1))
% 19.81/3.00      | ~ v1_relat_1(X1) ),
% 19.81/3.00      inference(cnf_transformation,[],[f38]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_204,plain,
% 19.81/3.00      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 19.81/3.00      | ~ r1_tarski(X0,k1_relat_1(X1))
% 19.81/3.00      | sK2 != X1 ),
% 19.81/3.00      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_205,plain,
% 19.81/3.00      ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
% 19.81/3.00      | ~ r1_tarski(X0,k1_relat_1(sK2)) ),
% 19.81/3.00      inference(unflattening,[status(thm)],[c_204]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_489,plain,
% 19.81/3.00      ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = iProver_top
% 19.81/3.00      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 19.81/3.00      inference(predicate_to_equality,[status(thm)],[c_205]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_871,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = X0
% 19.81/3.00      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_489,c_494]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_7,plain,
% 19.81/3.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 19.81/3.00      inference(cnf_transformation,[],[f35]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_870,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_490,c_494]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_3130,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) = k10_relat_1(sK2,k9_relat_1(sK2,X0)) ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_7,c_870]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_5523,plain,
% 19.81/3.00      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 19.81/3.00      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 19.81/3.00      inference(demodulation,[status(thm)],[c_871,c_3130]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_5531,plain,
% 19.81/3.00      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = sK0 ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_492,c_5523]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_47007,plain,
% 19.81/3.00      ( r1_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
% 19.81/3.00      inference(light_normalisation,[status(thm)],[c_1460,c_5531]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_47012,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1)))) = sK0 ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_47007,c_494]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_5,plain,
% 19.81/3.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 19.81/3.00      inference(cnf_transformation,[],[f46]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_495,plain,
% 19.81/3.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 19.81/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_894,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_495,c_494]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_9521,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_7,c_894]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_47378,plain,
% 19.81/3.00      ( k1_setfam_1(k2_tarski(sK0,sK1)) = sK0 ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_47012,c_9521]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_892,plain,
% 19.81/3.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_7,c_495]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_47760,plain,
% 19.81/3.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 19.81/3.00      inference(superposition,[status(thm)],[c_47378,c_892]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_11,negated_conjecture,
% 19.81/3.00      ( ~ r1_tarski(sK0,sK1) ),
% 19.81/3.00      inference(cnf_transformation,[],[f45]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(c_22,plain,
% 19.81/3.00      ( r1_tarski(sK0,sK1) != iProver_top ),
% 19.81/3.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.81/3.00  
% 19.81/3.00  cnf(contradiction,plain,
% 19.81/3.00      ( $false ),
% 19.81/3.00      inference(minisat,[status(thm)],[c_47760,c_22]) ).
% 19.81/3.00  
% 19.81/3.00  
% 19.81/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.81/3.00  
% 19.81/3.00  ------                               Statistics
% 19.81/3.00  
% 19.81/3.00  ------ General
% 19.81/3.00  
% 19.81/3.00  abstr_ref_over_cycles:                  0
% 19.81/3.00  abstr_ref_under_cycles:                 0
% 19.81/3.00  gc_basic_clause_elim:                   0
% 19.81/3.00  forced_gc_time:                         0
% 19.81/3.00  parsing_time:                           0.013
% 19.81/3.00  unif_index_cands_time:                  0.
% 19.81/3.00  unif_index_add_time:                    0.
% 19.81/3.00  orderings_time:                         0.
% 19.81/3.00  out_proof_time:                         0.008
% 19.81/3.00  total_time:                             2.39
% 19.81/3.00  num_of_symbols:                         44
% 19.81/3.00  num_of_terms:                           148536
% 19.81/3.00  
% 19.81/3.00  ------ Preprocessing
% 19.81/3.00  
% 19.81/3.00  num_of_splits:                          0
% 19.81/3.00  num_of_split_atoms:                     0
% 19.81/3.00  num_of_reused_defs:                     0
% 19.81/3.00  num_eq_ax_congr_red:                    7
% 19.81/3.00  num_of_sem_filtered_clauses:            1
% 19.81/3.00  num_of_subtypes:                        0
% 19.81/3.00  monotx_restored_types:                  0
% 19.81/3.00  sat_num_of_epr_types:                   0
% 19.81/3.00  sat_num_of_non_cyclic_types:            0
% 19.81/3.00  sat_guarded_non_collapsed_types:        0
% 19.81/3.00  num_pure_diseq_elim:                    0
% 19.81/3.00  simp_replaced_by:                       0
% 19.81/3.00  res_preprocessed:                       72
% 19.81/3.00  prep_upred:                             0
% 19.81/3.00  prep_unflattend:                        3
% 19.81/3.00  smt_new_axioms:                         0
% 19.81/3.00  pred_elim_cands:                        1
% 19.81/3.00  pred_elim:                              3
% 19.81/3.00  pred_elim_cl:                           3
% 19.81/3.00  pred_elim_cycles:                       5
% 19.81/3.00  merged_defs:                            0
% 19.81/3.00  merged_defs_ncl:                        0
% 19.81/3.00  bin_hyper_res:                          0
% 19.81/3.00  prep_cycles:                            4
% 19.81/3.00  pred_elim_time:                         0.001
% 19.81/3.00  splitting_time:                         0.
% 19.81/3.00  sem_filter_time:                        0.
% 19.81/3.00  monotx_time:                            0.
% 19.81/3.00  subtype_inf_time:                       0.
% 19.81/3.00  
% 19.81/3.00  ------ Problem properties
% 19.81/3.00  
% 19.81/3.00  clauses:                                13
% 19.81/3.00  conjectures:                            3
% 19.81/3.00  epr:                                    3
% 19.81/3.00  horn:                                   13
% 19.81/3.00  ground:                                 3
% 19.81/3.00  unary:                                  8
% 19.81/3.00  binary:                                 4
% 19.81/3.00  lits:                                   19
% 19.81/3.00  lits_eq:                                5
% 19.81/3.00  fd_pure:                                0
% 19.81/3.00  fd_pseudo:                              0
% 19.81/3.00  fd_cond:                                0
% 19.81/3.00  fd_pseudo_cond:                         1
% 19.81/3.00  ac_symbols:                             0
% 19.81/3.00  
% 19.81/3.00  ------ Propositional Solver
% 19.81/3.00  
% 19.81/3.00  prop_solver_calls:                      30
% 19.81/3.00  prop_fast_solver_calls:                 415
% 19.81/3.00  smt_solver_calls:                       0
% 19.81/3.00  smt_fast_solver_calls:                  0
% 19.81/3.00  prop_num_of_clauses:                    14296
% 19.81/3.00  prop_preprocess_simplified:             13259
% 19.81/3.00  prop_fo_subsumed:                       4
% 19.81/3.00  prop_solver_time:                       0.
% 19.81/3.00  smt_solver_time:                        0.
% 19.81/3.00  smt_fast_solver_time:                   0.
% 19.81/3.00  prop_fast_solver_time:                  0.
% 19.81/3.00  prop_unsat_core_time:                   0.001
% 19.81/3.00  
% 19.81/3.00  ------ QBF
% 19.81/3.00  
% 19.81/3.00  qbf_q_res:                              0
% 19.81/3.00  qbf_num_tautologies:                    0
% 19.81/3.00  qbf_prep_cycles:                        0
% 19.81/3.00  
% 19.81/3.00  ------ BMC1
% 19.81/3.00  
% 19.81/3.00  bmc1_current_bound:                     -1
% 19.81/3.00  bmc1_last_solved_bound:                 -1
% 19.81/3.00  bmc1_unsat_core_size:                   -1
% 19.81/3.00  bmc1_unsat_core_parents_size:           -1
% 19.81/3.00  bmc1_merge_next_fun:                    0
% 19.81/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.81/3.00  
% 19.81/3.00  ------ Instantiation
% 19.81/3.00  
% 19.81/3.00  inst_num_of_clauses:                    1859
% 19.81/3.00  inst_num_in_passive:                    960
% 19.81/3.00  inst_num_in_active:                     637
% 19.81/3.00  inst_num_in_unprocessed:                262
% 19.81/3.00  inst_num_of_loops:                      640
% 19.81/3.00  inst_num_of_learning_restarts:          0
% 19.81/3.00  inst_num_moves_active_passive:          1
% 19.81/3.00  inst_lit_activity:                      0
% 19.81/3.00  inst_lit_activity_moves:                0
% 19.81/3.00  inst_num_tautologies:                   0
% 19.81/3.00  inst_num_prop_implied:                  0
% 19.81/3.00  inst_num_existing_simplified:           0
% 19.81/3.00  inst_num_eq_res_simplified:             0
% 19.81/3.00  inst_num_child_elim:                    0
% 19.81/3.00  inst_num_of_dismatching_blockings:      536
% 19.81/3.00  inst_num_of_non_proper_insts:           1950
% 19.81/3.00  inst_num_of_duplicates:                 0
% 19.81/3.00  inst_inst_num_from_inst_to_res:         0
% 19.81/3.00  inst_dismatching_checking_time:         0.
% 19.81/3.00  
% 19.81/3.00  ------ Resolution
% 19.81/3.00  
% 19.81/3.00  res_num_of_clauses:                     0
% 19.81/3.00  res_num_in_passive:                     0
% 19.81/3.00  res_num_in_active:                      0
% 19.81/3.00  res_num_of_loops:                       76
% 19.81/3.00  res_forward_subset_subsumed:            303
% 19.81/3.00  res_backward_subset_subsumed:           0
% 19.81/3.00  res_forward_subsumed:                   0
% 19.81/3.00  res_backward_subsumed:                  0
% 19.81/3.00  res_forward_subsumption_resolution:     0
% 19.81/3.00  res_backward_subsumption_resolution:    0
% 19.81/3.00  res_clause_to_clause_subsumption:       117906
% 19.81/3.00  res_orphan_elimination:                 0
% 19.81/3.00  res_tautology_del:                      103
% 19.81/3.00  res_num_eq_res_simplified:              0
% 19.81/3.00  res_num_sel_changes:                    0
% 19.81/3.00  res_moves_from_active_to_pass:          0
% 19.81/3.00  
% 19.81/3.00  ------ Superposition
% 19.81/3.00  
% 19.81/3.00  sup_time_total:                         0.
% 19.81/3.00  sup_time_generating:                    0.
% 19.81/3.00  sup_time_sim_full:                      0.
% 19.81/3.00  sup_time_sim_immed:                     0.
% 19.81/3.00  
% 19.81/3.00  sup_num_of_clauses:                     4473
% 19.81/3.00  sup_num_in_active:                      121
% 19.81/3.00  sup_num_in_passive:                     4352
% 19.81/3.00  sup_num_of_loops:                       126
% 19.81/3.00  sup_fw_superposition:                   8912
% 19.81/3.00  sup_bw_superposition:                   7666
% 19.81/3.00  sup_immediate_simplified:               4575
% 19.81/3.00  sup_given_eliminated:                   1
% 19.81/3.00  comparisons_done:                       0
% 19.81/3.00  comparisons_avoided:                    0
% 19.81/3.00  
% 19.81/3.00  ------ Simplifications
% 19.81/3.00  
% 19.81/3.00  
% 19.81/3.00  sim_fw_subset_subsumed:                 2
% 19.81/3.00  sim_bw_subset_subsumed:                 2
% 19.81/3.00  sim_fw_subsumed:                        583
% 19.81/3.00  sim_bw_subsumed:                        711
% 19.81/3.00  sim_fw_subsumption_res:                 0
% 19.81/3.00  sim_bw_subsumption_res:                 0
% 19.81/3.00  sim_tautology_del:                      2
% 19.81/3.00  sim_eq_tautology_del:                   218
% 19.81/3.00  sim_eq_res_simp:                        0
% 19.81/3.00  sim_fw_demodulated:                     2748
% 19.81/3.00  sim_bw_demodulated:                     68
% 19.81/3.00  sim_light_normalised:                   834
% 19.81/3.00  sim_joinable_taut:                      0
% 19.81/3.00  sim_joinable_simp:                      0
% 19.81/3.00  sim_ac_normalised:                      0
% 19.81/3.00  sim_smt_subsumption:                    0
% 19.81/3.00  
%------------------------------------------------------------------------------
