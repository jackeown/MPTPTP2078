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
% DateTime   : Thu Dec  3 11:52:01 EST 2020

% Result     : Theorem 7.77s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 435 expanded)
%              Number of clauses        :   56 ( 161 expanded)
%              Number of leaves         :   13 (  85 expanded)
%              Depth                    :   20
%              Number of atoms          :  197 ( 906 expanded)
%              Number of equality atoms :  105 ( 412 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f32,f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f42,plain,(
    k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f42,f43,f43])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_214,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_447,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_222,plain,
    ( ~ v1_relat_1(X0_40)
    | k7_relat_1(k7_relat_1(X0_40,X0_41),X0_41) = k7_relat_1(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_440,plain,
    ( k7_relat_1(k7_relat_1(X0_40,X0_41),X0_41) = k7_relat_1(X0_40,X0_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_721,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_41),X0_41) = k7_relat_1(sK2,X0_41) ),
    inference(superposition,[status(thm)],[c_447,c_440])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_223,plain,
    ( ~ v1_relat_1(X0_40)
    | k7_relat_1(X0_40,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k7_relat_1(k7_relat_1(X0_40,X0_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_439,plain,
    ( k7_relat_1(X0_40,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k7_relat_1(k7_relat_1(X0_40,X0_41),X1_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_662,plain,
    ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k7_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
    inference(superposition,[status(thm)],[c_447,c_439])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_224,plain,
    ( ~ v1_relat_1(X0_40)
    | v1_relat_1(k7_relat_1(X0_40,X0_41)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_438,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k7_relat_1(X0_40,X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_834,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_438])).

cnf(c_13,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1061,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_834,c_13])).

cnf(c_1068,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_41)) = iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_1061])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_219,plain,
    ( ~ v1_funct_1(X0_40)
    | v1_funct_1(k7_relat_1(X0_40,X0_41))
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_443,plain,
    ( v1_funct_1(X0_40) != iProver_top
    | v1_funct_1(k7_relat_1(X0_40,X0_41)) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_217,plain,
    ( ~ v1_funct_1(X0_40)
    | ~ v1_relat_1(X0_40)
    | k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(X0_40,k1_relat_1(X0_40)))) = k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_445,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(X0_40,k1_relat_1(X0_40)))) = k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41))
    | v1_funct_1(X0_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_1090,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(k7_relat_1(X0_40,X1_41),k1_relat_1(k7_relat_1(X0_40,X1_41))))) = k9_relat_1(k7_relat_1(X0_40,X1_41),k10_relat_1(k7_relat_1(X0_40,X1_41),X0_41))
    | v1_funct_1(X0_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k7_relat_1(X0_40,X1_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_443,c_445])).

cnf(c_17249,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(k7_relat_1(sK2,X1_41),k1_relat_1(k7_relat_1(sK2,X1_41))))) = k9_relat_1(k7_relat_1(sK2,X1_41),k10_relat_1(k7_relat_1(sK2,X1_41),X0_41))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1068,c_1090])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_221,plain,
    ( ~ v1_relat_1(X0_40)
    | k9_relat_1(X0_40,k1_relat_1(X0_40)) = k2_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_441,plain,
    ( k9_relat_1(X0_40,k1_relat_1(X0_40)) = k2_relat_1(X0_40)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_1374,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_relat_1(k7_relat_1(sK2,X0_41))) = k2_relat_1(k7_relat_1(sK2,X0_41)) ),
    inference(superposition,[status(thm)],[c_1068,c_441])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_220,plain,
    ( ~ v1_relat_1(X0_40)
    | k2_relat_1(k7_relat_1(X0_40,X0_41)) = k9_relat_1(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_442,plain,
    ( k2_relat_1(k7_relat_1(X0_40,X0_41)) = k9_relat_1(X0_40,X0_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_669,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_41)) = k9_relat_1(sK2,X0_41) ),
    inference(superposition,[status(thm)],[c_447,c_442])).

cnf(c_1375,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_relat_1(k7_relat_1(sK2,X0_41))) = k9_relat_1(sK2,X0_41) ),
    inference(light_normalisation,[status(thm)],[c_1374,c_669])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_218,plain,
    ( ~ v1_relat_1(X0_40)
    | k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_444,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_1370,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(k7_relat_1(sK2,X1_41),X2_41))) = k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_41),X0_41),X2_41) ),
    inference(superposition,[status(thm)],[c_1068,c_444])).

cnf(c_5207,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_41),k10_relat_1(k7_relat_1(sK2,X1_41),X2_41)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_41),X0_41),X2_41)) ),
    inference(superposition,[status(thm)],[c_1370,c_662])).

cnf(c_1372,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = k9_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
    inference(superposition,[status(thm)],[c_1068,c_442])).

cnf(c_6222,plain,
    ( k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41),X2_41))) = k9_relat_1(k7_relat_1(sK2,X1_41),k10_relat_1(k7_relat_1(sK2,X0_41),X2_41)) ),
    inference(superposition,[status(thm)],[c_5207,c_1372])).

cnf(c_6243,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_41),k10_relat_1(k7_relat_1(sK2,X1_41),X2_41)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_41),X0_41),X2_41)) ),
    inference(demodulation,[status(thm)],[c_6222,c_669])).

cnf(c_17438,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(sK2,X1_41))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_41),X0_41))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17249,c_721,c_1375,c_6243])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_19299,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(sK2,X1_41))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_41),X0_41)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17438,c_13,c_14])).

cnf(c_767,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(sK2,X1_41))) = k10_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
    inference(superposition,[status(thm)],[c_447,c_444])).

cnf(c_0,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_225,plain,
    ( k1_enumset1(X0_41,X0_41,X1_41) = k1_enumset1(X1_41,X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_10,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_216,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_513,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_225,c_216])).

cnf(c_904,plain,
    ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_767,c_513])).

cnf(c_19303,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_19299,c_904])).

cnf(c_19304,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_19303])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:53:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.77/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.77/1.48  
% 7.77/1.48  ------  iProver source info
% 7.77/1.48  
% 7.77/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.77/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.77/1.48  git: non_committed_changes: false
% 7.77/1.48  git: last_make_outside_of_git: false
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    ""
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             all
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         305.
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              default
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           true
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             true
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    true
% 7.77/1.48  --inst_sos_flag                         true
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     num_symb
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       true
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    passive
% 7.77/1.48  --sup_prop_simpl_new                    true
% 7.77/1.48  --sup_prop_simpl_given                  true
% 7.77/1.48  --sup_fun_splitting                     true
% 7.77/1.48  --sup_smt_interval                      50000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_input_bw                          []
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         3
% 7.77/1.48  --comb_sup_mult                         2
% 7.77/1.48  --comb_inst_mult                        10
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  ------ Parsing...
% 7.77/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.77/1.48  ------ Proving...
% 7.77/1.48  ------ Problem Properties 
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  clauses                                 12
% 7.77/1.48  conjectures                             3
% 7.77/1.48  EPR                                     2
% 7.77/1.48  Horn                                    12
% 7.77/1.48  unary                                   4
% 7.77/1.48  binary                                  6
% 7.77/1.48  lits                                    22
% 7.77/1.48  lits eq                                 8
% 7.77/1.48  fd_pure                                 0
% 7.77/1.48  fd_pseudo                               0
% 7.77/1.48  fd_cond                                 0
% 7.77/1.48  fd_pseudo_cond                          0
% 7.77/1.48  AC symbols                              0
% 7.77/1.48  
% 7.77/1.48  ------ Schedule dynamic 5 is on 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  Current options:
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    ""
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             all
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         305.
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              default
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           true
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             true
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    true
% 7.77/1.48  --inst_sos_flag                         true
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     none
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       false
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    passive
% 7.77/1.48  --sup_prop_simpl_new                    true
% 7.77/1.48  --sup_prop_simpl_given                  true
% 7.77/1.48  --sup_fun_splitting                     true
% 7.77/1.48  --sup_smt_interval                      50000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_input_bw                          []
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         3
% 7.77/1.48  --comb_sup_mult                         2
% 7.77/1.48  --comb_inst_mult                        10
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ Proving...
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  % SZS status Theorem for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48   Resolution empty clause
% 7.77/1.48  
% 7.77/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  fof(f12,conjecture,(
% 7.77/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f13,negated_conjecture,(
% 7.77/1.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))))),
% 7.77/1.48    inference(negated_conjecture,[],[f12])).
% 7.77/1.48  
% 7.77/1.48  fof(f24,plain,(
% 7.77/1.48    ? [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.77/1.48    inference(ennf_transformation,[],[f13])).
% 7.77/1.48  
% 7.77/1.48  fof(f25,plain,(
% 7.77/1.48    ? [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.77/1.48    inference(flattening,[],[f24])).
% 7.77/1.48  
% 7.77/1.48  fof(f26,plain,(
% 7.77/1.48    ? [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f27,plain,(
% 7.77/1.48    k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).
% 7.77/1.48  
% 7.77/1.48  fof(f40,plain,(
% 7.77/1.48    v1_relat_1(sK2)),
% 7.77/1.48    inference(cnf_transformation,[],[f27])).
% 7.77/1.48  
% 7.77/1.48  fof(f6,axiom,(
% 7.77/1.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f16,plain,(
% 7.77/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1))),
% 7.77/1.48    inference(ennf_transformation,[],[f6])).
% 7.77/1.48  
% 7.77/1.48  fof(f33,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f16])).
% 7.77/1.48  
% 7.77/1.48  fof(f5,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f15,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.77/1.48    inference(ennf_transformation,[],[f5])).
% 7.77/1.48  
% 7.77/1.48  fof(f32,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f15])).
% 7.77/1.48  
% 7.77/1.48  fof(f3,axiom,(
% 7.77/1.48    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f30,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f3])).
% 7.77/1.48  
% 7.77/1.48  fof(f2,axiom,(
% 7.77/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f29,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f2])).
% 7.77/1.48  
% 7.77/1.48  fof(f43,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f30,f29])).
% 7.77/1.48  
% 7.77/1.48  fof(f45,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f32,f43])).
% 7.77/1.48  
% 7.77/1.48  fof(f4,axiom,(
% 7.77/1.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f14,plain,(
% 7.77/1.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(ennf_transformation,[],[f4])).
% 7.77/1.48  
% 7.77/1.48  fof(f31,plain,(
% 7.77/1.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f14])).
% 7.77/1.48  
% 7.77/1.48  fof(f9,axiom,(
% 7.77/1.48    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f19,plain,(
% 7.77/1.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.48    inference(ennf_transformation,[],[f9])).
% 7.77/1.48  
% 7.77/1.48  fof(f20,plain,(
% 7.77/1.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(flattening,[],[f19])).
% 7.77/1.48  
% 7.77/1.48  fof(f37,plain,(
% 7.77/1.48    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f20])).
% 7.77/1.48  
% 7.77/1.48  fof(f11,axiom,(
% 7.77/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f22,plain,(
% 7.77/1.48    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.77/1.48    inference(ennf_transformation,[],[f11])).
% 7.77/1.48  
% 7.77/1.48  fof(f23,plain,(
% 7.77/1.48    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.77/1.48    inference(flattening,[],[f22])).
% 7.77/1.48  
% 7.77/1.48  fof(f39,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f23])).
% 7.77/1.48  
% 7.77/1.48  fof(f47,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f39,f43])).
% 7.77/1.48  
% 7.77/1.48  fof(f7,axiom,(
% 7.77/1.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f17,plain,(
% 7.77/1.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(ennf_transformation,[],[f7])).
% 7.77/1.48  
% 7.77/1.48  fof(f34,plain,(
% 7.77/1.48    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f17])).
% 7.77/1.48  
% 7.77/1.48  fof(f8,axiom,(
% 7.77/1.48    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f18,plain,(
% 7.77/1.48    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.77/1.48    inference(ennf_transformation,[],[f8])).
% 7.77/1.48  
% 7.77/1.48  fof(f35,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f18])).
% 7.77/1.48  
% 7.77/1.48  fof(f10,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f21,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.77/1.48    inference(ennf_transformation,[],[f10])).
% 7.77/1.48  
% 7.77/1.48  fof(f38,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f21])).
% 7.77/1.48  
% 7.77/1.48  fof(f46,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f38,f43])).
% 7.77/1.48  
% 7.77/1.48  fof(f41,plain,(
% 7.77/1.48    v1_funct_1(sK2)),
% 7.77/1.48    inference(cnf_transformation,[],[f27])).
% 7.77/1.48  
% 7.77/1.48  fof(f1,axiom,(
% 7.77/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f28,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f1])).
% 7.77/1.48  
% 7.77/1.48  fof(f44,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f28,f29,f29])).
% 7.77/1.48  
% 7.77/1.48  fof(f42,plain,(
% 7.77/1.48    k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),
% 7.77/1.48    inference(cnf_transformation,[],[f27])).
% 7.77/1.48  
% 7.77/1.48  fof(f48,plain,(
% 7.77/1.48    k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))))),
% 7.77/1.48    inference(definition_unfolding,[],[f42,f43,f43])).
% 7.77/1.48  
% 7.77/1.48  cnf(c_12,negated_conjecture,
% 7.77/1.48      ( v1_relat_1(sK2) ),
% 7.77/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_214,negated_conjecture,
% 7.77/1.48      ( v1_relat_1(sK2) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_12]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_447,plain,
% 7.77/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_3,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0)
% 7.77/1.48      | k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_222,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0_40)
% 7.77/1.48      | k7_relat_1(k7_relat_1(X0_40,X0_41),X0_41) = k7_relat_1(X0_40,X0_41) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_440,plain,
% 7.77/1.48      ( k7_relat_1(k7_relat_1(X0_40,X0_41),X0_41) = k7_relat_1(X0_40,X0_41)
% 7.77/1.48      | v1_relat_1(X0_40) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_721,plain,
% 7.77/1.48      ( k7_relat_1(k7_relat_1(sK2,X0_41),X0_41) = k7_relat_1(sK2,X0_41) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_447,c_440]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0)
% 7.77/1.48      | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.77/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_223,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0_40)
% 7.77/1.48      | k7_relat_1(X0_40,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k7_relat_1(k7_relat_1(X0_40,X0_41),X1_41) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_439,plain,
% 7.77/1.48      ( k7_relat_1(X0_40,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k7_relat_1(k7_relat_1(X0_40,X0_41),X1_41)
% 7.77/1.48      | v1_relat_1(X0_40) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_662,plain,
% 7.77/1.48      ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k7_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_447,c_439]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.77/1.48      inference(cnf_transformation,[],[f31]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_224,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0_40) | v1_relat_1(k7_relat_1(X0_40,X0_41)) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_438,plain,
% 7.77/1.48      ( v1_relat_1(X0_40) != iProver_top
% 7.77/1.48      | v1_relat_1(k7_relat_1(X0_40,X0_41)) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_834,plain,
% 7.77/1.48      ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = iProver_top
% 7.77/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_662,c_438]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_13,plain,
% 7.77/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1061,plain,
% 7.77/1.48      ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = iProver_top ),
% 7.77/1.48      inference(global_propositional_subsumption,[status(thm)],[c_834,c_13]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1068,plain,
% 7.77/1.48      ( v1_relat_1(k7_relat_1(sK2,X0_41)) = iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_721,c_1061]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6,plain,
% 7.77/1.48      ( ~ v1_funct_1(X0) | v1_funct_1(k7_relat_1(X0,X1)) | ~ v1_relat_1(X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_219,plain,
% 7.77/1.48      ( ~ v1_funct_1(X0_40)
% 7.77/1.48      | v1_funct_1(k7_relat_1(X0_40,X0_41))
% 7.77/1.48      | ~ v1_relat_1(X0_40) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_443,plain,
% 7.77/1.48      ( v1_funct_1(X0_40) != iProver_top
% 7.77/1.48      | v1_funct_1(k7_relat_1(X0_40,X0_41)) = iProver_top
% 7.77/1.48      | v1_relat_1(X0_40) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_9,plain,
% 7.77/1.48      ( ~ v1_funct_1(X0)
% 7.77/1.48      | ~ v1_relat_1(X0)
% 7.77/1.48      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 7.77/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_217,plain,
% 7.77/1.48      ( ~ v1_funct_1(X0_40)
% 7.77/1.48      | ~ v1_relat_1(X0_40)
% 7.77/1.48      | k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(X0_40,k1_relat_1(X0_40)))) = k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_445,plain,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(X0_40,k1_relat_1(X0_40)))) = k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41))
% 7.77/1.48      | v1_funct_1(X0_40) != iProver_top
% 7.77/1.48      | v1_relat_1(X0_40) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1090,plain,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(k7_relat_1(X0_40,X1_41),k1_relat_1(k7_relat_1(X0_40,X1_41))))) = k9_relat_1(k7_relat_1(X0_40,X1_41),k10_relat_1(k7_relat_1(X0_40,X1_41),X0_41))
% 7.77/1.48      | v1_funct_1(X0_40) != iProver_top
% 7.77/1.48      | v1_relat_1(X0_40) != iProver_top
% 7.77/1.48      | v1_relat_1(k7_relat_1(X0_40,X1_41)) != iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_443,c_445]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_17249,plain,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(k7_relat_1(sK2,X1_41),k1_relat_1(k7_relat_1(sK2,X1_41))))) = k9_relat_1(k7_relat_1(sK2,X1_41),k10_relat_1(k7_relat_1(sK2,X1_41),X0_41))
% 7.77/1.48      | v1_funct_1(sK2) != iProver_top
% 7.77/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1068,c_1090]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_4,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_221,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0_40)
% 7.77/1.48      | k9_relat_1(X0_40,k1_relat_1(X0_40)) = k2_relat_1(X0_40) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_441,plain,
% 7.77/1.48      ( k9_relat_1(X0_40,k1_relat_1(X0_40)) = k2_relat_1(X0_40)
% 7.77/1.48      | v1_relat_1(X0_40) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1374,plain,
% 7.77/1.48      ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_relat_1(k7_relat_1(sK2,X0_41))) = k2_relat_1(k7_relat_1(sK2,X0_41)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1068,c_441]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_5,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_220,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0_40)
% 7.77/1.48      | k2_relat_1(k7_relat_1(X0_40,X0_41)) = k9_relat_1(X0_40,X0_41) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_442,plain,
% 7.77/1.48      ( k2_relat_1(k7_relat_1(X0_40,X0_41)) = k9_relat_1(X0_40,X0_41)
% 7.77/1.48      | v1_relat_1(X0_40) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_669,plain,
% 7.77/1.48      ( k2_relat_1(k7_relat_1(sK2,X0_41)) = k9_relat_1(sK2,X0_41) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_447,c_442]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1375,plain,
% 7.77/1.48      ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_relat_1(k7_relat_1(sK2,X0_41))) = k9_relat_1(sK2,X0_41) ),
% 7.77/1.48      inference(light_normalisation,[status(thm)],[c_1374,c_669]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_8,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0)
% 7.77/1.48      | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.77/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_218,plain,
% 7.77/1.48      ( ~ v1_relat_1(X0_40)
% 7.77/1.48      | k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_8]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_444,plain,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41)
% 7.77/1.48      | v1_relat_1(X0_40) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1370,plain,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(k7_relat_1(sK2,X1_41),X2_41))) = k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_41),X0_41),X2_41) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1068,c_444]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_5207,plain,
% 7.77/1.48      ( k7_relat_1(k7_relat_1(sK2,X0_41),k10_relat_1(k7_relat_1(sK2,X1_41),X2_41)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_41),X0_41),X2_41)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1370,c_662]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1372,plain,
% 7.77/1.48      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = k9_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1068,c_442]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6222,plain,
% 7.77/1.48      ( k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41),X2_41))) = k9_relat_1(k7_relat_1(sK2,X1_41),k10_relat_1(k7_relat_1(sK2,X0_41),X2_41)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_5207,c_1372]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_6243,plain,
% 7.77/1.48      ( k9_relat_1(k7_relat_1(sK2,X0_41),k10_relat_1(k7_relat_1(sK2,X1_41),X2_41)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_41),X0_41),X2_41)) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_6222,c_669]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_17438,plain,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(sK2,X1_41))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_41),X0_41))
% 7.77/1.48      | v1_funct_1(sK2) != iProver_top
% 7.77/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_17249,c_721,c_1375,c_6243]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_11,negated_conjecture,
% 7.77/1.48      ( v1_funct_1(sK2) ),
% 7.77/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_14,plain,
% 7.77/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_19299,plain,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k9_relat_1(sK2,X1_41))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_41),X0_41)) ),
% 7.77/1.48      inference(global_propositional_subsumption,
% 7.77/1.48                [status(thm)],
% 7.77/1.48                [c_17438,c_13,c_14]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_767,plain,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(sK2,X1_41))) = k10_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_447,c_444]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_0,plain,
% 7.77/1.48      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_225,plain,
% 7.77/1.48      ( k1_enumset1(X0_41,X0_41,X1_41) = k1_enumset1(X1_41,X1_41,X0_41) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10,negated_conjecture,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_216,negated_conjecture,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
% 7.77/1.48      inference(subtyping,[status(esa)],[c_10]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_513,plain,
% 7.77/1.48      ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_225,c_216]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_904,plain,
% 7.77/1.48      ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_767,c_513]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_19303,plain,
% 7.77/1.48      ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_19299,c_904]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_19304,plain,
% 7.77/1.48      ( $false ),
% 7.77/1.48      inference(equality_resolution_simp,[status(thm)],[c_19303]) ).
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  ------                               Statistics
% 7.77/1.48  
% 7.77/1.48  ------ General
% 7.77/1.48  
% 7.77/1.48  abstr_ref_over_cycles:                  0
% 7.77/1.48  abstr_ref_under_cycles:                 0
% 7.77/1.48  gc_basic_clause_elim:                   0
% 7.77/1.48  forced_gc_time:                         0
% 7.77/1.48  parsing_time:                           0.012
% 7.77/1.48  unif_index_cands_time:                  0.
% 7.77/1.48  unif_index_add_time:                    0.
% 7.77/1.48  orderings_time:                         0.
% 7.77/1.48  out_proof_time:                         0.01
% 7.77/1.48  total_time:                             0.679
% 7.77/1.48  num_of_symbols:                         43
% 7.77/1.48  num_of_terms:                           23759
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing
% 7.77/1.48  
% 7.77/1.48  num_of_splits:                          0
% 7.77/1.48  num_of_split_atoms:                     0
% 7.77/1.48  num_of_reused_defs:                     0
% 7.77/1.48  num_eq_ax_congr_red:                    3
% 7.77/1.48  num_of_sem_filtered_clauses:            1
% 7.77/1.48  num_of_subtypes:                        3
% 7.77/1.48  monotx_restored_types:                  0
% 7.77/1.48  sat_num_of_epr_types:                   0
% 7.77/1.48  sat_num_of_non_cyclic_types:            0
% 7.77/1.48  sat_guarded_non_collapsed_types:        0
% 7.77/1.48  num_pure_diseq_elim:                    0
% 7.77/1.48  simp_replaced_by:                       0
% 7.77/1.48  res_preprocessed:                       77
% 7.77/1.48  prep_upred:                             0
% 7.77/1.48  prep_unflattend:                        0
% 7.77/1.48  smt_new_axioms:                         0
% 7.77/1.48  pred_elim_cands:                        2
% 7.77/1.48  pred_elim:                              0
% 7.77/1.48  pred_elim_cl:                           0
% 7.77/1.48  pred_elim_cycles:                       2
% 7.77/1.48  merged_defs:                            0
% 7.77/1.48  merged_defs_ncl:                        0
% 7.77/1.48  bin_hyper_res:                          0
% 7.77/1.48  prep_cycles:                            4
% 7.77/1.48  pred_elim_time:                         0.
% 7.77/1.48  splitting_time:                         0.
% 7.77/1.48  sem_filter_time:                        0.
% 7.77/1.48  monotx_time:                            0.
% 7.77/1.48  subtype_inf_time:                       0.
% 7.77/1.48  
% 7.77/1.48  ------ Problem properties
% 7.77/1.48  
% 7.77/1.48  clauses:                                12
% 7.77/1.48  conjectures:                            3
% 7.77/1.48  epr:                                    2
% 7.77/1.48  horn:                                   12
% 7.77/1.48  ground:                                 3
% 7.77/1.48  unary:                                  4
% 7.77/1.48  binary:                                 6
% 7.77/1.48  lits:                                   22
% 7.77/1.48  lits_eq:                                8
% 7.77/1.48  fd_pure:                                0
% 7.77/1.48  fd_pseudo:                              0
% 7.77/1.48  fd_cond:                                0
% 7.77/1.48  fd_pseudo_cond:                         0
% 7.77/1.48  ac_symbols:                             0
% 7.77/1.48  
% 7.77/1.48  ------ Propositional Solver
% 7.77/1.48  
% 7.77/1.48  prop_solver_calls:                      34
% 7.77/1.48  prop_fast_solver_calls:                 495
% 7.77/1.48  smt_solver_calls:                       0
% 7.77/1.48  smt_fast_solver_calls:                  0
% 7.77/1.48  prop_num_of_clauses:                    3402
% 7.77/1.48  prop_preprocess_simplified:             6460
% 7.77/1.48  prop_fo_subsumed:                       7
% 7.77/1.48  prop_solver_time:                       0.
% 7.77/1.48  smt_solver_time:                        0.
% 7.77/1.48  smt_fast_solver_time:                   0.
% 7.77/1.48  prop_fast_solver_time:                  0.
% 7.77/1.48  prop_unsat_core_time:                   0.
% 7.77/1.48  
% 7.77/1.48  ------ QBF
% 7.77/1.48  
% 7.77/1.48  qbf_q_res:                              0
% 7.77/1.48  qbf_num_tautologies:                    0
% 7.77/1.48  qbf_prep_cycles:                        0
% 7.77/1.48  
% 7.77/1.48  ------ BMC1
% 7.77/1.48  
% 7.77/1.48  bmc1_current_bound:                     -1
% 7.77/1.48  bmc1_last_solved_bound:                 -1
% 7.77/1.48  bmc1_unsat_core_size:                   -1
% 7.77/1.48  bmc1_unsat_core_parents_size:           -1
% 7.77/1.48  bmc1_merge_next_fun:                    0
% 7.77/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation
% 7.77/1.48  
% 7.77/1.48  inst_num_of_clauses:                    1214
% 7.77/1.48  inst_num_in_passive:                    42
% 7.77/1.48  inst_num_in_active:                     663
% 7.77/1.48  inst_num_in_unprocessed:                511
% 7.77/1.48  inst_num_of_loops:                      700
% 7.77/1.48  inst_num_of_learning_restarts:          0
% 7.77/1.48  inst_num_moves_active_passive:          30
% 7.77/1.48  inst_lit_activity:                      0
% 7.77/1.48  inst_lit_activity_moves:                0
% 7.77/1.48  inst_num_tautologies:                   0
% 7.77/1.48  inst_num_prop_implied:                  0
% 7.77/1.48  inst_num_existing_simplified:           0
% 7.77/1.48  inst_num_eq_res_simplified:             0
% 7.77/1.48  inst_num_child_elim:                    0
% 7.77/1.48  inst_num_of_dismatching_blockings:      1198
% 7.77/1.48  inst_num_of_non_proper_insts:           3051
% 7.77/1.48  inst_num_of_duplicates:                 0
% 7.77/1.48  inst_inst_num_from_inst_to_res:         0
% 7.77/1.48  inst_dismatching_checking_time:         0.
% 7.77/1.48  
% 7.77/1.48  ------ Resolution
% 7.77/1.48  
% 7.77/1.48  res_num_of_clauses:                     0
% 7.77/1.48  res_num_in_passive:                     0
% 7.77/1.48  res_num_in_active:                      0
% 7.77/1.48  res_num_of_loops:                       81
% 7.77/1.48  res_forward_subset_subsumed:            336
% 7.77/1.48  res_backward_subset_subsumed:           6
% 7.77/1.48  res_forward_subsumed:                   0
% 7.77/1.48  res_backward_subsumed:                  0
% 7.77/1.48  res_forward_subsumption_resolution:     0
% 7.77/1.48  res_backward_subsumption_resolution:    0
% 7.77/1.48  res_clause_to_clause_subsumption:       4995
% 7.77/1.48  res_orphan_elimination:                 0
% 7.77/1.48  res_tautology_del:                      481
% 7.77/1.48  res_num_eq_res_simplified:              0
% 7.77/1.48  res_num_sel_changes:                    0
% 7.77/1.48  res_moves_from_active_to_pass:          0
% 7.77/1.48  
% 7.77/1.48  ------ Superposition
% 7.77/1.48  
% 7.77/1.48  sup_time_total:                         0.
% 7.77/1.48  sup_time_generating:                    0.
% 7.77/1.48  sup_time_sim_full:                      0.
% 7.77/1.48  sup_time_sim_immed:                     0.
% 7.77/1.48  
% 7.77/1.48  sup_num_of_clauses:                     926
% 7.77/1.48  sup_num_in_active:                      133
% 7.77/1.48  sup_num_in_passive:                     793
% 7.77/1.48  sup_num_of_loops:                       139
% 7.77/1.48  sup_fw_superposition:                   2728
% 7.77/1.48  sup_bw_superposition:                   1912
% 7.77/1.48  sup_immediate_simplified:               2212
% 7.77/1.48  sup_given_eliminated:                   0
% 7.77/1.48  comparisons_done:                       0
% 7.77/1.48  comparisons_avoided:                    0
% 7.77/1.48  
% 7.77/1.48  ------ Simplifications
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  sim_fw_subset_subsumed:                 14
% 7.77/1.48  sim_bw_subset_subsumed:                 11
% 7.77/1.48  sim_fw_subsumed:                        275
% 7.77/1.48  sim_bw_subsumed:                        51
% 7.77/1.48  sim_fw_subsumption_res:                 0
% 7.77/1.48  sim_bw_subsumption_res:                 0
% 7.77/1.48  sim_tautology_del:                      28
% 7.77/1.48  sim_eq_tautology_del:                   324
% 7.77/1.48  sim_eq_res_simp:                        0
% 7.77/1.48  sim_fw_demodulated:                     1923
% 7.77/1.48  sim_bw_demodulated:                     38
% 7.77/1.48  sim_light_normalised:                   1212
% 7.77/1.48  sim_joinable_taut:                      0
% 7.77/1.48  sim_joinable_simp:                      0
% 7.77/1.48  sim_ac_normalised:                      0
% 7.77/1.48  sim_smt_subsumption:                    0
% 7.77/1.48  
%------------------------------------------------------------------------------
