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
% DateTime   : Thu Dec  3 11:52:01 EST 2020

% Result     : Theorem 11.97s
% Output     : CNFRefutation 11.97s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 784 expanded)
%              Number of clauses        :   91 ( 281 expanded)
%              Number of leaves         :   18 ( 161 expanded)
%              Depth                    :   24
%              Number of atoms          :  280 (1540 expanded)
%              Number of equality atoms :  158 ( 746 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f33])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f52,plain,(
    k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f52,f53,f53])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_308,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_624,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_312,plain,
    ( ~ v1_funct_1(X0_41)
    | v1_funct_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_621,plain,
    ( v1_funct_1(X0_41) != iProver_top
    | v1_funct_1(k7_relat_1(X0_41,X0_42)) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_310,plain,
    ( ~ v1_funct_1(X0_41)
    | ~ v1_relat_1(X0_41)
    | k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(X0_41,k1_relat_1(X0_41)))) = k9_relat_1(X0_41,k10_relat_1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_623,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(X0_41,k1_relat_1(X0_41)))) = k9_relat_1(X0_41,k10_relat_1(X0_41,X0_42))
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_1635,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(X0_41,X1_42),k1_relat_1(k7_relat_1(X0_41,X1_42))))) = k9_relat_1(k7_relat_1(X0_41,X1_42),k10_relat_1(k7_relat_1(X0_41,X1_42),X0_42))
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k7_relat_1(X0_41,X1_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_623])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_320,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k7_relat_1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_613,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k7_relat_1(X0_41,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_41445,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(X0_41,X1_42),k1_relat_1(k7_relat_1(X0_41,X1_42))))) = k9_relat_1(k7_relat_1(X0_41,X1_42),k10_relat_1(k7_relat_1(X0_41,X1_42),X0_42))
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1635,c_613])).

cnf(c_41449,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(sK2,X1_42),k1_relat_1(k7_relat_1(sK2,X1_42))))) = k9_relat_1(k7_relat_1(sK2,X1_42),k10_relat_1(k7_relat_1(sK2,X1_42),X0_42))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_624,c_41445])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_307,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_625,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_317,plain,
    ( ~ v1_relat_1(X0_41)
    | k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_616,plain,
    ( k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_794,plain,
    ( k9_relat_1(k7_relat_1(X0_41,X0_42),k1_relat_1(k7_relat_1(X0_41,X0_42))) = k2_relat_1(k7_relat_1(X0_41,X0_42))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_616])).

cnf(c_2180,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k2_relat_1(k7_relat_1(sK2,X0_42)) ),
    inference(superposition,[status(thm)],[c_625,c_794])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_316,plain,
    ( ~ v1_relat_1(X0_41)
    | k2_relat_1(k7_relat_1(X0_41,X0_42)) = k9_relat_1(X0_41,X0_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_617,plain,
    ( k2_relat_1(k7_relat_1(X0_41,X0_42)) = k9_relat_1(X0_41,X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_869,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_42)) = k9_relat_1(sK2,X0_42) ),
    inference(superposition,[status(thm)],[c_625,c_617])).

cnf(c_2190,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k9_relat_1(sK2,X0_42) ),
    inference(light_normalisation,[status(thm)],[c_2180,c_869])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_314,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),X0_42)
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_619,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),X0_42) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ v1_relat_1(X0_41)
    | k7_relat_1(k7_relat_1(X0_41,X1_42),X0_42) = k7_relat_1(X0_41,X0_42) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_615,plain,
    ( k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) = k7_relat_1(X0_41,X1_42)
    | r1_tarski(X1_42,X0_42) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_1463,plain,
    ( k7_relat_1(k7_relat_1(X0_41,X0_42),k1_relat_1(k7_relat_1(X1_41,X0_42))) = k7_relat_1(X0_41,k1_relat_1(k7_relat_1(X1_41,X0_42)))
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_619,c_615])).

cnf(c_29762,plain,
    ( k7_relat_1(k7_relat_1(X0_41,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK2,X0_42)))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_1463])).

cnf(c_31540,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0_42))) ),
    inference(superposition,[status(thm)],[c_625,c_29762])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_315,plain,
    ( ~ v1_relat_1(X0_41)
    | k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),X0_42))) = k7_relat_1(X0_41,X0_42) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_618,plain,
    ( k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),X0_42))) = k7_relat_1(X0_41,X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_1549,plain,
    ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0_42))) = k7_relat_1(sK2,X0_42) ),
    inference(superposition,[status(thm)],[c_625,c_618])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_313,plain,
    ( ~ v1_relat_1(X0_41)
    | k1_setfam_1(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),X0_42)) = k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_620,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),X0_42)) = k1_relat_1(k7_relat_1(X0_41,X0_42))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_946,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0_42)) = k1_relat_1(k7_relat_1(sK2,X0_42)) ),
    inference(superposition,[status(thm)],[c_625,c_620])).

cnf(c_1556,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0_42))) = k7_relat_1(sK2,X0_42) ),
    inference(light_normalisation,[status(thm)],[c_1549,c_946])).

cnf(c_31559,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k7_relat_1(sK2,X0_42) ),
    inference(light_normalisation,[status(thm)],[c_31540,c_1556])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_319,plain,
    ( ~ v1_relat_1(X0_41)
    | k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_614,plain,
    ( k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_854,plain,
    ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_625,c_614])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_311,plain,
    ( ~ v1_relat_1(X0_41)
    | k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(X0_41,X1_42))) = k10_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_622,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(X0_41,X1_42))) = k10_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_1565,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(sK2,X1_42))) = k10_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_625,c_622])).

cnf(c_1661,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(sK2,X1_42)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) ),
    inference(superposition,[status(thm)],[c_1565,c_854])).

cnf(c_2641,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))),X2_42)) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k10_relat_1(sK2,X2_42)) ),
    inference(superposition,[status(thm)],[c_854,c_1661])).

cnf(c_1796,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42))) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) ),
    inference(superposition,[status(thm)],[c_854,c_1556])).

cnf(c_0,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_321,plain,
    ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1094,plain,
    ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_321,c_854])).

cnf(c_1818,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42))) = k7_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
    inference(light_normalisation,[status(thm)],[c_1796,c_1094])).

cnf(c_2643,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42))),X2_42)) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),k10_relat_1(sK2,X2_42)) ),
    inference(superposition,[status(thm)],[c_1818,c_1661])).

cnf(c_2670,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42)) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k10_relat_1(sK2,X2_42)) ),
    inference(light_normalisation,[status(thm)],[c_2643,c_1818])).

cnf(c_2675,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))),X2_42)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42)) ),
    inference(light_normalisation,[status(thm)],[c_2641,c_2670])).

cnf(c_2677,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),X2_42)) ),
    inference(light_normalisation,[status(thm)],[c_2675,c_1094])).

cnf(c_22936,plain,
    ( k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),X2_42)) ),
    inference(superposition,[status(thm)],[c_2677,c_869])).

cnf(c_31607,plain,
    ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0_42))),X0_42),X1_42)) = k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42))) ),
    inference(superposition,[status(thm)],[c_31559,c_22936])).

cnf(c_31895,plain,
    ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42)) = k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42))) ),
    inference(light_normalisation,[status(thm)],[c_31607,c_1556])).

cnf(c_31896,plain,
    ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) ),
    inference(demodulation,[status(thm)],[c_31895,c_869])).

cnf(c_1566,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(k7_relat_1(X0_41,X1_42),X2_42))) = k10_relat_1(k7_relat_1(k7_relat_1(X0_41,X1_42),X0_42),X2_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_622])).

cnf(c_37288,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(k7_relat_1(sK2,X1_42),X2_42))) = k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),X2_42) ),
    inference(superposition,[status(thm)],[c_625,c_1566])).

cnf(c_870,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)) = k9_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_617])).

cnf(c_4418,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k9_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_625,c_870])).

cnf(c_1099,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) ),
    inference(superposition,[status(thm)],[c_854,c_869])).

cnf(c_4563,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k9_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
    inference(demodulation,[status(thm)],[c_4418,c_1099])).

cnf(c_37540,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X1_42),X2_42)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),X2_42)) ),
    inference(superposition,[status(thm)],[c_37288,c_4563])).

cnf(c_41466,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(sK2,X1_42))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_42),X0_42))
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41449,c_2190,c_31896,c_37540])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_42643,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(sK2,X1_42))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_42),X0_42)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41466,c_16])).

cnf(c_13,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_309,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_721,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_321,c_309])).

cnf(c_1656,plain,
    ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_1565,c_721])).

cnf(c_42647,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_42643,c_1656])).

cnf(c_325,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_7616,plain,
    ( k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) = k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_332,plain,
    ( X0_43 != X1_43
    | k1_setfam_1(X0_43) = k1_setfam_1(X1_43) ),
    theory(equality)).

cnf(c_4998,plain,
    ( X0_43 != k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))
    | k1_setfam_1(X0_43) = k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_7615,plain,
    ( k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) != k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))
    | k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) = k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(instantiation,[status(thm)],[c_4998])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42647,c_7616,c_7615])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.97/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.97/1.99  
% 11.97/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.97/1.99  
% 11.97/1.99  ------  iProver source info
% 11.97/1.99  
% 11.97/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.97/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.97/1.99  git: non_committed_changes: false
% 11.97/1.99  git: last_make_outside_of_git: false
% 11.97/1.99  
% 11.97/1.99  ------ 
% 11.97/1.99  
% 11.97/1.99  ------ Input Options
% 11.97/1.99  
% 11.97/1.99  --out_options                           all
% 11.97/1.99  --tptp_safe_out                         true
% 11.97/1.99  --problem_path                          ""
% 11.97/1.99  --include_path                          ""
% 11.97/1.99  --clausifier                            res/vclausify_rel
% 11.97/1.99  --clausifier_options                    --mode clausify
% 11.97/1.99  --stdin                                 false
% 11.97/1.99  --stats_out                             all
% 11.97/1.99  
% 11.97/1.99  ------ General Options
% 11.97/1.99  
% 11.97/1.99  --fof                                   false
% 11.97/1.99  --time_out_real                         305.
% 11.97/1.99  --time_out_virtual                      -1.
% 11.97/1.99  --symbol_type_check                     false
% 11.97/1.99  --clausify_out                          false
% 11.97/1.99  --sig_cnt_out                           false
% 11.97/1.99  --trig_cnt_out                          false
% 11.97/1.99  --trig_cnt_out_tolerance                1.
% 11.97/1.99  --trig_cnt_out_sk_spl                   false
% 11.97/1.99  --abstr_cl_out                          false
% 11.97/1.99  
% 11.97/1.99  ------ Global Options
% 11.97/1.99  
% 11.97/1.99  --schedule                              default
% 11.97/1.99  --add_important_lit                     false
% 11.97/1.99  --prop_solver_per_cl                    1000
% 11.97/1.99  --min_unsat_core                        false
% 11.97/1.99  --soft_assumptions                      false
% 11.97/1.99  --soft_lemma_size                       3
% 11.97/1.99  --prop_impl_unit_size                   0
% 11.97/1.99  --prop_impl_unit                        []
% 11.97/1.99  --share_sel_clauses                     true
% 11.97/1.99  --reset_solvers                         false
% 11.97/1.99  --bc_imp_inh                            [conj_cone]
% 11.97/1.99  --conj_cone_tolerance                   3.
% 11.97/1.99  --extra_neg_conj                        none
% 11.97/1.99  --large_theory_mode                     true
% 11.97/1.99  --prolific_symb_bound                   200
% 11.97/1.99  --lt_threshold                          2000
% 11.97/1.99  --clause_weak_htbl                      true
% 11.97/1.99  --gc_record_bc_elim                     false
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing Options
% 11.97/1.99  
% 11.97/1.99  --preprocessing_flag                    true
% 11.97/1.99  --time_out_prep_mult                    0.1
% 11.97/1.99  --splitting_mode                        input
% 11.97/1.99  --splitting_grd                         true
% 11.97/1.99  --splitting_cvd                         false
% 11.97/1.99  --splitting_cvd_svl                     false
% 11.97/1.99  --splitting_nvd                         32
% 11.97/1.99  --sub_typing                            true
% 11.97/1.99  --prep_gs_sim                           true
% 11.97/1.99  --prep_unflatten                        true
% 11.97/1.99  --prep_res_sim                          true
% 11.97/1.99  --prep_upred                            true
% 11.97/1.99  --prep_sem_filter                       exhaustive
% 11.97/1.99  --prep_sem_filter_out                   false
% 11.97/1.99  --pred_elim                             true
% 11.97/1.99  --res_sim_input                         true
% 11.97/1.99  --eq_ax_congr_red                       true
% 11.97/1.99  --pure_diseq_elim                       true
% 11.97/1.99  --brand_transform                       false
% 11.97/1.99  --non_eq_to_eq                          false
% 11.97/1.99  --prep_def_merge                        true
% 11.97/1.99  --prep_def_merge_prop_impl              false
% 11.97/1.99  --prep_def_merge_mbd                    true
% 11.97/1.99  --prep_def_merge_tr_red                 false
% 11.97/1.99  --prep_def_merge_tr_cl                  false
% 11.97/1.99  --smt_preprocessing                     true
% 11.97/1.99  --smt_ac_axioms                         fast
% 11.97/1.99  --preprocessed_out                      false
% 11.97/1.99  --preprocessed_stats                    false
% 11.97/1.99  
% 11.97/1.99  ------ Abstraction refinement Options
% 11.97/1.99  
% 11.97/1.99  --abstr_ref                             []
% 11.97/1.99  --abstr_ref_prep                        false
% 11.97/1.99  --abstr_ref_until_sat                   false
% 11.97/1.99  --abstr_ref_sig_restrict                funpre
% 11.97/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.97/1.99  --abstr_ref_under                       []
% 11.97/1.99  
% 11.97/1.99  ------ SAT Options
% 11.97/1.99  
% 11.97/1.99  --sat_mode                              false
% 11.97/1.99  --sat_fm_restart_options                ""
% 11.97/1.99  --sat_gr_def                            false
% 11.97/1.99  --sat_epr_types                         true
% 11.97/1.99  --sat_non_cyclic_types                  false
% 11.97/1.99  --sat_finite_models                     false
% 11.97/1.99  --sat_fm_lemmas                         false
% 11.97/1.99  --sat_fm_prep                           false
% 11.97/1.99  --sat_fm_uc_incr                        true
% 11.97/1.99  --sat_out_model                         small
% 11.97/1.99  --sat_out_clauses                       false
% 11.97/1.99  
% 11.97/1.99  ------ QBF Options
% 11.97/1.99  
% 11.97/1.99  --qbf_mode                              false
% 11.97/1.99  --qbf_elim_univ                         false
% 11.97/1.99  --qbf_dom_inst                          none
% 11.97/1.99  --qbf_dom_pre_inst                      false
% 11.97/1.99  --qbf_sk_in                             false
% 11.97/1.99  --qbf_pred_elim                         true
% 11.97/1.99  --qbf_split                             512
% 11.97/1.99  
% 11.97/1.99  ------ BMC1 Options
% 11.97/1.99  
% 11.97/1.99  --bmc1_incremental                      false
% 11.97/1.99  --bmc1_axioms                           reachable_all
% 11.97/1.99  --bmc1_min_bound                        0
% 11.97/1.99  --bmc1_max_bound                        -1
% 11.97/1.99  --bmc1_max_bound_default                -1
% 11.97/1.99  --bmc1_symbol_reachability              true
% 11.97/1.99  --bmc1_property_lemmas                  false
% 11.97/1.99  --bmc1_k_induction                      false
% 11.97/1.99  --bmc1_non_equiv_states                 false
% 11.97/1.99  --bmc1_deadlock                         false
% 11.97/1.99  --bmc1_ucm                              false
% 11.97/1.99  --bmc1_add_unsat_core                   none
% 11.97/1.99  --bmc1_unsat_core_children              false
% 11.97/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.97/1.99  --bmc1_out_stat                         full
% 11.97/1.99  --bmc1_ground_init                      false
% 11.97/1.99  --bmc1_pre_inst_next_state              false
% 11.97/1.99  --bmc1_pre_inst_state                   false
% 11.97/1.99  --bmc1_pre_inst_reach_state             false
% 11.97/1.99  --bmc1_out_unsat_core                   false
% 11.97/1.99  --bmc1_aig_witness_out                  false
% 11.97/1.99  --bmc1_verbose                          false
% 11.97/1.99  --bmc1_dump_clauses_tptp                false
% 11.97/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.97/1.99  --bmc1_dump_file                        -
% 11.97/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.97/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.97/1.99  --bmc1_ucm_extend_mode                  1
% 11.97/1.99  --bmc1_ucm_init_mode                    2
% 11.97/1.99  --bmc1_ucm_cone_mode                    none
% 11.97/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.97/1.99  --bmc1_ucm_relax_model                  4
% 11.97/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.97/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.97/1.99  --bmc1_ucm_layered_model                none
% 11.97/1.99  --bmc1_ucm_max_lemma_size               10
% 11.97/1.99  
% 11.97/1.99  ------ AIG Options
% 11.97/1.99  
% 11.97/1.99  --aig_mode                              false
% 11.97/1.99  
% 11.97/1.99  ------ Instantiation Options
% 11.97/1.99  
% 11.97/1.99  --instantiation_flag                    true
% 11.97/1.99  --inst_sos_flag                         false
% 11.97/1.99  --inst_sos_phase                        true
% 11.97/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.97/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.97/1.99  --inst_lit_sel_side                     num_symb
% 11.97/1.99  --inst_solver_per_active                1400
% 11.97/1.99  --inst_solver_calls_frac                1.
% 11.97/1.99  --inst_passive_queue_type               priority_queues
% 11.97/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.97/1.99  --inst_passive_queues_freq              [25;2]
% 11.97/1.99  --inst_dismatching                      true
% 11.97/1.99  --inst_eager_unprocessed_to_passive     true
% 11.97/1.99  --inst_prop_sim_given                   true
% 11.97/1.99  --inst_prop_sim_new                     false
% 11.97/1.99  --inst_subs_new                         false
% 11.97/1.99  --inst_eq_res_simp                      false
% 11.97/1.99  --inst_subs_given                       false
% 11.97/1.99  --inst_orphan_elimination               true
% 11.97/1.99  --inst_learning_loop_flag               true
% 11.97/1.99  --inst_learning_start                   3000
% 11.97/1.99  --inst_learning_factor                  2
% 11.97/1.99  --inst_start_prop_sim_after_learn       3
% 11.97/1.99  --inst_sel_renew                        solver
% 11.97/1.99  --inst_lit_activity_flag                true
% 11.97/1.99  --inst_restr_to_given                   false
% 11.97/1.99  --inst_activity_threshold               500
% 11.97/1.99  --inst_out_proof                        true
% 11.97/1.99  
% 11.97/1.99  ------ Resolution Options
% 11.97/1.99  
% 11.97/1.99  --resolution_flag                       true
% 11.97/1.99  --res_lit_sel                           adaptive
% 11.97/1.99  --res_lit_sel_side                      none
% 11.97/1.99  --res_ordering                          kbo
% 11.97/1.99  --res_to_prop_solver                    active
% 11.97/1.99  --res_prop_simpl_new                    false
% 11.97/1.99  --res_prop_simpl_given                  true
% 11.97/1.99  --res_passive_queue_type                priority_queues
% 11.97/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.97/1.99  --res_passive_queues_freq               [15;5]
% 11.97/1.99  --res_forward_subs                      full
% 11.97/1.99  --res_backward_subs                     full
% 11.97/1.99  --res_forward_subs_resolution           true
% 11.97/1.99  --res_backward_subs_resolution          true
% 11.97/1.99  --res_orphan_elimination                true
% 11.97/1.99  --res_time_limit                        2.
% 11.97/1.99  --res_out_proof                         true
% 11.97/1.99  
% 11.97/1.99  ------ Superposition Options
% 11.97/1.99  
% 11.97/1.99  --superposition_flag                    true
% 11.97/1.99  --sup_passive_queue_type                priority_queues
% 11.97/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.97/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.97/1.99  --demod_completeness_check              fast
% 11.97/1.99  --demod_use_ground                      true
% 11.97/1.99  --sup_to_prop_solver                    passive
% 11.97/1.99  --sup_prop_simpl_new                    true
% 11.97/1.99  --sup_prop_simpl_given                  true
% 11.97/1.99  --sup_fun_splitting                     false
% 11.97/1.99  --sup_smt_interval                      50000
% 11.97/1.99  
% 11.97/1.99  ------ Superposition Simplification Setup
% 11.97/1.99  
% 11.97/1.99  --sup_indices_passive                   []
% 11.97/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.97/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_full_bw                           [BwDemod]
% 11.97/1.99  --sup_immed_triv                        [TrivRules]
% 11.97/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_immed_bw_main                     []
% 11.97/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.97/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/1.99  
% 11.97/1.99  ------ Combination Options
% 11.97/1.99  
% 11.97/1.99  --comb_res_mult                         3
% 11.97/1.99  --comb_sup_mult                         2
% 11.97/1.99  --comb_inst_mult                        10
% 11.97/1.99  
% 11.97/1.99  ------ Debug Options
% 11.97/1.99  
% 11.97/1.99  --dbg_backtrace                         false
% 11.97/1.99  --dbg_dump_prop_clauses                 false
% 11.97/1.99  --dbg_dump_prop_clauses_file            -
% 11.97/1.99  --dbg_out_stat                          false
% 11.97/1.99  ------ Parsing...
% 11.97/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/1.99  ------ Proving...
% 11.97/1.99  ------ Problem Properties 
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  clauses                                 15
% 11.97/1.99  conjectures                             3
% 11.97/1.99  EPR                                     2
% 11.97/1.99  Horn                                    15
% 11.97/1.99  unary                                   4
% 11.97/1.99  binary                                  8
% 11.97/1.99  lits                                    29
% 11.97/1.99  lits eq                                 10
% 11.97/1.99  fd_pure                                 0
% 11.97/1.99  fd_pseudo                               0
% 11.97/1.99  fd_cond                                 0
% 11.97/1.99  fd_pseudo_cond                          0
% 11.97/1.99  AC symbols                              0
% 11.97/1.99  
% 11.97/1.99  ------ Schedule dynamic 5 is on 
% 11.97/1.99  
% 11.97/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  ------ 
% 11.97/1.99  Current options:
% 11.97/1.99  ------ 
% 11.97/1.99  
% 11.97/1.99  ------ Input Options
% 11.97/1.99  
% 11.97/1.99  --out_options                           all
% 11.97/1.99  --tptp_safe_out                         true
% 11.97/1.99  --problem_path                          ""
% 11.97/1.99  --include_path                          ""
% 11.97/1.99  --clausifier                            res/vclausify_rel
% 11.97/1.99  --clausifier_options                    --mode clausify
% 11.97/1.99  --stdin                                 false
% 11.97/1.99  --stats_out                             all
% 11.97/1.99  
% 11.97/1.99  ------ General Options
% 11.97/1.99  
% 11.97/1.99  --fof                                   false
% 11.97/1.99  --time_out_real                         305.
% 11.97/1.99  --time_out_virtual                      -1.
% 11.97/1.99  --symbol_type_check                     false
% 11.97/1.99  --clausify_out                          false
% 11.97/1.99  --sig_cnt_out                           false
% 11.97/1.99  --trig_cnt_out                          false
% 11.97/1.99  --trig_cnt_out_tolerance                1.
% 11.97/1.99  --trig_cnt_out_sk_spl                   false
% 11.97/1.99  --abstr_cl_out                          false
% 11.97/1.99  
% 11.97/1.99  ------ Global Options
% 11.97/1.99  
% 11.97/1.99  --schedule                              default
% 11.97/1.99  --add_important_lit                     false
% 11.97/1.99  --prop_solver_per_cl                    1000
% 11.97/1.99  --min_unsat_core                        false
% 11.97/1.99  --soft_assumptions                      false
% 11.97/1.99  --soft_lemma_size                       3
% 11.97/1.99  --prop_impl_unit_size                   0
% 11.97/1.99  --prop_impl_unit                        []
% 11.97/1.99  --share_sel_clauses                     true
% 11.97/1.99  --reset_solvers                         false
% 11.97/1.99  --bc_imp_inh                            [conj_cone]
% 11.97/1.99  --conj_cone_tolerance                   3.
% 11.97/1.99  --extra_neg_conj                        none
% 11.97/1.99  --large_theory_mode                     true
% 11.97/1.99  --prolific_symb_bound                   200
% 11.97/1.99  --lt_threshold                          2000
% 11.97/1.99  --clause_weak_htbl                      true
% 11.97/1.99  --gc_record_bc_elim                     false
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing Options
% 11.97/1.99  
% 11.97/1.99  --preprocessing_flag                    true
% 11.97/1.99  --time_out_prep_mult                    0.1
% 11.97/1.99  --splitting_mode                        input
% 11.97/1.99  --splitting_grd                         true
% 11.97/1.99  --splitting_cvd                         false
% 11.97/1.99  --splitting_cvd_svl                     false
% 11.97/1.99  --splitting_nvd                         32
% 11.97/1.99  --sub_typing                            true
% 11.97/1.99  --prep_gs_sim                           true
% 11.97/1.99  --prep_unflatten                        true
% 11.97/1.99  --prep_res_sim                          true
% 11.97/1.99  --prep_upred                            true
% 11.97/1.99  --prep_sem_filter                       exhaustive
% 11.97/1.99  --prep_sem_filter_out                   false
% 11.97/1.99  --pred_elim                             true
% 11.97/1.99  --res_sim_input                         true
% 11.97/1.99  --eq_ax_congr_red                       true
% 11.97/1.99  --pure_diseq_elim                       true
% 11.97/1.99  --brand_transform                       false
% 11.97/1.99  --non_eq_to_eq                          false
% 11.97/1.99  --prep_def_merge                        true
% 11.97/1.99  --prep_def_merge_prop_impl              false
% 11.97/1.99  --prep_def_merge_mbd                    true
% 11.97/1.99  --prep_def_merge_tr_red                 false
% 11.97/1.99  --prep_def_merge_tr_cl                  false
% 11.97/1.99  --smt_preprocessing                     true
% 11.97/1.99  --smt_ac_axioms                         fast
% 11.97/1.99  --preprocessed_out                      false
% 11.97/1.99  --preprocessed_stats                    false
% 11.97/1.99  
% 11.97/1.99  ------ Abstraction refinement Options
% 11.97/1.99  
% 11.97/1.99  --abstr_ref                             []
% 11.97/1.99  --abstr_ref_prep                        false
% 11.97/1.99  --abstr_ref_until_sat                   false
% 11.97/1.99  --abstr_ref_sig_restrict                funpre
% 11.97/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.97/1.99  --abstr_ref_under                       []
% 11.97/1.99  
% 11.97/1.99  ------ SAT Options
% 11.97/1.99  
% 11.97/1.99  --sat_mode                              false
% 11.97/1.99  --sat_fm_restart_options                ""
% 11.97/1.99  --sat_gr_def                            false
% 11.97/1.99  --sat_epr_types                         true
% 11.97/1.99  --sat_non_cyclic_types                  false
% 11.97/1.99  --sat_finite_models                     false
% 11.97/1.99  --sat_fm_lemmas                         false
% 11.97/1.99  --sat_fm_prep                           false
% 11.97/1.99  --sat_fm_uc_incr                        true
% 11.97/1.99  --sat_out_model                         small
% 11.97/1.99  --sat_out_clauses                       false
% 11.97/1.99  
% 11.97/1.99  ------ QBF Options
% 11.97/1.99  
% 11.97/1.99  --qbf_mode                              false
% 11.97/1.99  --qbf_elim_univ                         false
% 11.97/1.99  --qbf_dom_inst                          none
% 11.97/1.99  --qbf_dom_pre_inst                      false
% 11.97/1.99  --qbf_sk_in                             false
% 11.97/1.99  --qbf_pred_elim                         true
% 11.97/1.99  --qbf_split                             512
% 11.97/1.99  
% 11.97/1.99  ------ BMC1 Options
% 11.97/1.99  
% 11.97/1.99  --bmc1_incremental                      false
% 11.97/1.99  --bmc1_axioms                           reachable_all
% 11.97/1.99  --bmc1_min_bound                        0
% 11.97/1.99  --bmc1_max_bound                        -1
% 11.97/1.99  --bmc1_max_bound_default                -1
% 11.97/1.99  --bmc1_symbol_reachability              true
% 11.97/1.99  --bmc1_property_lemmas                  false
% 11.97/1.99  --bmc1_k_induction                      false
% 11.97/1.99  --bmc1_non_equiv_states                 false
% 11.97/1.99  --bmc1_deadlock                         false
% 11.97/1.99  --bmc1_ucm                              false
% 11.97/1.99  --bmc1_add_unsat_core                   none
% 11.97/1.99  --bmc1_unsat_core_children              false
% 11.97/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.97/1.99  --bmc1_out_stat                         full
% 11.97/1.99  --bmc1_ground_init                      false
% 11.97/1.99  --bmc1_pre_inst_next_state              false
% 11.97/1.99  --bmc1_pre_inst_state                   false
% 11.97/1.99  --bmc1_pre_inst_reach_state             false
% 11.97/1.99  --bmc1_out_unsat_core                   false
% 11.97/1.99  --bmc1_aig_witness_out                  false
% 11.97/1.99  --bmc1_verbose                          false
% 11.97/1.99  --bmc1_dump_clauses_tptp                false
% 11.97/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.97/1.99  --bmc1_dump_file                        -
% 11.97/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.97/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.97/1.99  --bmc1_ucm_extend_mode                  1
% 11.97/1.99  --bmc1_ucm_init_mode                    2
% 11.97/1.99  --bmc1_ucm_cone_mode                    none
% 11.97/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.97/1.99  --bmc1_ucm_relax_model                  4
% 11.97/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.97/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.97/1.99  --bmc1_ucm_layered_model                none
% 11.97/1.99  --bmc1_ucm_max_lemma_size               10
% 11.97/1.99  
% 11.97/1.99  ------ AIG Options
% 11.97/1.99  
% 11.97/1.99  --aig_mode                              false
% 11.97/1.99  
% 11.97/1.99  ------ Instantiation Options
% 11.97/1.99  
% 11.97/1.99  --instantiation_flag                    true
% 11.97/1.99  --inst_sos_flag                         false
% 11.97/1.99  --inst_sos_phase                        true
% 11.97/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.97/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.97/1.99  --inst_lit_sel_side                     none
% 11.97/1.99  --inst_solver_per_active                1400
% 11.97/1.99  --inst_solver_calls_frac                1.
% 11.97/1.99  --inst_passive_queue_type               priority_queues
% 11.97/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.97/1.99  --inst_passive_queues_freq              [25;2]
% 11.97/1.99  --inst_dismatching                      true
% 11.97/1.99  --inst_eager_unprocessed_to_passive     true
% 11.97/1.99  --inst_prop_sim_given                   true
% 11.97/1.99  --inst_prop_sim_new                     false
% 11.97/1.99  --inst_subs_new                         false
% 11.97/1.99  --inst_eq_res_simp                      false
% 11.97/1.99  --inst_subs_given                       false
% 11.97/1.99  --inst_orphan_elimination               true
% 11.97/1.99  --inst_learning_loop_flag               true
% 11.97/1.99  --inst_learning_start                   3000
% 11.97/1.99  --inst_learning_factor                  2
% 11.97/1.99  --inst_start_prop_sim_after_learn       3
% 11.97/1.99  --inst_sel_renew                        solver
% 11.97/1.99  --inst_lit_activity_flag                true
% 11.97/1.99  --inst_restr_to_given                   false
% 11.97/1.99  --inst_activity_threshold               500
% 11.97/1.99  --inst_out_proof                        true
% 11.97/1.99  
% 11.97/1.99  ------ Resolution Options
% 11.97/1.99  
% 11.97/1.99  --resolution_flag                       false
% 11.97/1.99  --res_lit_sel                           adaptive
% 11.97/1.99  --res_lit_sel_side                      none
% 11.97/1.99  --res_ordering                          kbo
% 11.97/1.99  --res_to_prop_solver                    active
% 11.97/1.99  --res_prop_simpl_new                    false
% 11.97/1.99  --res_prop_simpl_given                  true
% 11.97/1.99  --res_passive_queue_type                priority_queues
% 11.97/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.97/1.99  --res_passive_queues_freq               [15;5]
% 11.97/1.99  --res_forward_subs                      full
% 11.97/1.99  --res_backward_subs                     full
% 11.97/1.99  --res_forward_subs_resolution           true
% 11.97/1.99  --res_backward_subs_resolution          true
% 11.97/1.99  --res_orphan_elimination                true
% 11.97/1.99  --res_time_limit                        2.
% 11.97/1.99  --res_out_proof                         true
% 11.97/1.99  
% 11.97/1.99  ------ Superposition Options
% 11.97/1.99  
% 11.97/1.99  --superposition_flag                    true
% 11.97/1.99  --sup_passive_queue_type                priority_queues
% 11.97/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.97/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.97/1.99  --demod_completeness_check              fast
% 11.97/1.99  --demod_use_ground                      true
% 11.97/1.99  --sup_to_prop_solver                    passive
% 11.97/1.99  --sup_prop_simpl_new                    true
% 11.97/1.99  --sup_prop_simpl_given                  true
% 11.97/1.99  --sup_fun_splitting                     false
% 11.97/1.99  --sup_smt_interval                      50000
% 11.97/1.99  
% 11.97/1.99  ------ Superposition Simplification Setup
% 11.97/1.99  
% 11.97/1.99  --sup_indices_passive                   []
% 11.97/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.97/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_full_bw                           [BwDemod]
% 11.97/1.99  --sup_immed_triv                        [TrivRules]
% 11.97/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_immed_bw_main                     []
% 11.97/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.97/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/1.99  
% 11.97/1.99  ------ Combination Options
% 11.97/1.99  
% 11.97/1.99  --comb_res_mult                         3
% 11.97/1.99  --comb_sup_mult                         2
% 11.97/1.99  --comb_inst_mult                        10
% 11.97/1.99  
% 11.97/1.99  ------ Debug Options
% 11.97/1.99  
% 11.97/1.99  --dbg_backtrace                         false
% 11.97/1.99  --dbg_dump_prop_clauses                 false
% 11.97/1.99  --dbg_dump_prop_clauses_file            -
% 11.97/1.99  --dbg_out_stat                          false
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  ------ Proving...
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  % SZS status Theorem for theBenchmark.p
% 11.97/1.99  
% 11.97/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.97/1.99  
% 11.97/1.99  fof(f15,conjecture,(
% 11.97/1.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f16,negated_conjecture,(
% 11.97/1.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))))),
% 11.97/1.99    inference(negated_conjecture,[],[f15])).
% 11.97/1.99  
% 11.97/1.99  fof(f31,plain,(
% 11.97/1.99    ? [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 11.97/1.99    inference(ennf_transformation,[],[f16])).
% 11.97/1.99  
% 11.97/1.99  fof(f32,plain,(
% 11.97/1.99    ? [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.97/1.99    inference(flattening,[],[f31])).
% 11.97/1.99  
% 11.97/1.99  fof(f33,plain,(
% 11.97/1.99    ? [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 11.97/1.99    introduced(choice_axiom,[])).
% 11.97/1.99  
% 11.97/1.99  fof(f34,plain,(
% 11.97/1.99    k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 11.97/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f33])).
% 11.97/1.99  
% 11.97/1.99  fof(f51,plain,(
% 11.97/1.99    v1_funct_1(sK2)),
% 11.97/1.99    inference(cnf_transformation,[],[f34])).
% 11.97/1.99  
% 11.97/1.99  fof(f12,axiom,(
% 11.97/1.99    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f26,plain,(
% 11.97/1.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.97/1.99    inference(ennf_transformation,[],[f12])).
% 11.97/1.99  
% 11.97/1.99  fof(f27,plain,(
% 11.97/1.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.97/1.99    inference(flattening,[],[f26])).
% 11.97/1.99  
% 11.97/1.99  fof(f47,plain,(
% 11.97/1.99    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f27])).
% 11.97/1.99  
% 11.97/1.99  fof(f14,axiom,(
% 11.97/1.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f29,plain,(
% 11.97/1.99    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.97/1.99    inference(ennf_transformation,[],[f14])).
% 11.97/1.99  
% 11.97/1.99  fof(f30,plain,(
% 11.97/1.99    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.97/1.99    inference(flattening,[],[f29])).
% 11.97/1.99  
% 11.97/1.99  fof(f49,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f30])).
% 11.97/1.99  
% 11.97/1.99  fof(f3,axiom,(
% 11.97/1.99    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f37,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f3])).
% 11.97/1.99  
% 11.97/1.99  fof(f2,axiom,(
% 11.97/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f36,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f2])).
% 11.97/1.99  
% 11.97/1.99  fof(f53,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f37,f36])).
% 11.97/1.99  
% 11.97/1.99  fof(f59,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f49,f53])).
% 11.97/1.99  
% 11.97/1.99  fof(f4,axiom,(
% 11.97/1.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f17,plain,(
% 11.97/1.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 11.97/1.99    inference(ennf_transformation,[],[f4])).
% 11.97/1.99  
% 11.97/1.99  fof(f38,plain,(
% 11.97/1.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f17])).
% 11.97/1.99  
% 11.97/1.99  fof(f50,plain,(
% 11.97/1.99    v1_relat_1(sK2)),
% 11.97/1.99    inference(cnf_transformation,[],[f34])).
% 11.97/1.99  
% 11.97/1.99  fof(f7,axiom,(
% 11.97/1.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f21,plain,(
% 11.97/1.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 11.97/1.99    inference(ennf_transformation,[],[f7])).
% 11.97/1.99  
% 11.97/1.99  fof(f41,plain,(
% 11.97/1.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f21])).
% 11.97/1.99  
% 11.97/1.99  fof(f8,axiom,(
% 11.97/1.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f22,plain,(
% 11.97/1.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 11.97/1.99    inference(ennf_transformation,[],[f8])).
% 11.97/1.99  
% 11.97/1.99  fof(f42,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f22])).
% 11.97/1.99  
% 11.97/1.99  fof(f10,axiom,(
% 11.97/1.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f24,plain,(
% 11.97/1.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 11.97/1.99    inference(ennf_transformation,[],[f10])).
% 11.97/1.99  
% 11.97/1.99  fof(f44,plain,(
% 11.97/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f24])).
% 11.97/1.99  
% 11.97/1.99  fof(f6,axiom,(
% 11.97/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f19,plain,(
% 11.97/1.99    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 11.97/1.99    inference(ennf_transformation,[],[f6])).
% 11.97/1.99  
% 11.97/1.99  fof(f20,plain,(
% 11.97/1.99    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 11.97/1.99    inference(flattening,[],[f19])).
% 11.97/1.99  
% 11.97/1.99  fof(f40,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f20])).
% 11.97/1.99  
% 11.97/1.99  fof(f9,axiom,(
% 11.97/1.99    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f23,plain,(
% 11.97/1.99    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.97/1.99    inference(ennf_transformation,[],[f9])).
% 11.97/1.99  
% 11.97/1.99  fof(f43,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f23])).
% 11.97/1.99  
% 11.97/1.99  fof(f56,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f43,f53])).
% 11.97/1.99  
% 11.97/1.99  fof(f11,axiom,(
% 11.97/1.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f25,plain,(
% 11.97/1.99    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 11.97/1.99    inference(ennf_transformation,[],[f11])).
% 11.97/1.99  
% 11.97/1.99  fof(f45,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f25])).
% 11.97/1.99  
% 11.97/1.99  fof(f57,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f45,f53])).
% 11.97/1.99  
% 11.97/1.99  fof(f5,axiom,(
% 11.97/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f18,plain,(
% 11.97/1.99    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 11.97/1.99    inference(ennf_transformation,[],[f5])).
% 11.97/1.99  
% 11.97/1.99  fof(f39,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f18])).
% 11.97/1.99  
% 11.97/1.99  fof(f55,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f39,f53])).
% 11.97/1.99  
% 11.97/1.99  fof(f13,axiom,(
% 11.97/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f28,plain,(
% 11.97/1.99    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 11.97/1.99    inference(ennf_transformation,[],[f13])).
% 11.97/1.99  
% 11.97/1.99  fof(f48,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f28])).
% 11.97/1.99  
% 11.97/1.99  fof(f58,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f48,f53])).
% 11.97/1.99  
% 11.97/1.99  fof(f1,axiom,(
% 11.97/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f35,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f1])).
% 11.97/1.99  
% 11.97/1.99  fof(f54,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f35,f36,f36])).
% 11.97/1.99  
% 11.97/1.99  fof(f52,plain,(
% 11.97/1.99    k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),
% 11.97/1.99    inference(cnf_transformation,[],[f34])).
% 11.97/1.99  
% 11.97/1.99  fof(f60,plain,(
% 11.97/1.99    k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))))),
% 11.97/1.99    inference(definition_unfolding,[],[f52,f53,f53])).
% 11.97/1.99  
% 11.97/1.99  cnf(c_14,negated_conjecture,
% 11.97/1.99      ( v1_funct_1(sK2) ),
% 11.97/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_308,negated_conjecture,
% 11.97/1.99      ( v1_funct_1(sK2) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_14]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_624,plain,
% 11.97/1.99      ( v1_funct_1(sK2) = iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_9,plain,
% 11.97/1.99      ( ~ v1_funct_1(X0)
% 11.97/1.99      | v1_funct_1(k7_relat_1(X0,X1))
% 11.97/1.99      | ~ v1_relat_1(X0) ),
% 11.97/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_312,plain,
% 11.97/1.99      ( ~ v1_funct_1(X0_41)
% 11.97/1.99      | v1_funct_1(k7_relat_1(X0_41,X0_42))
% 11.97/1.99      | ~ v1_relat_1(X0_41) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_9]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_621,plain,
% 11.97/1.99      ( v1_funct_1(X0_41) != iProver_top
% 11.97/1.99      | v1_funct_1(k7_relat_1(X0_41,X0_42)) = iProver_top
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_12,plain,
% 11.97/1.99      ( ~ v1_funct_1(X0)
% 11.97/1.99      | ~ v1_relat_1(X0)
% 11.97/1.99      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 11.97/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_310,plain,
% 11.97/1.99      ( ~ v1_funct_1(X0_41)
% 11.97/1.99      | ~ v1_relat_1(X0_41)
% 11.97/1.99      | k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(X0_41,k1_relat_1(X0_41)))) = k9_relat_1(X0_41,k10_relat_1(X0_41,X0_42)) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_12]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_623,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(X0_41,k1_relat_1(X0_41)))) = k9_relat_1(X0_41,k10_relat_1(X0_41,X0_42))
% 11.97/1.99      | v1_funct_1(X0_41) != iProver_top
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1635,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(X0_41,X1_42),k1_relat_1(k7_relat_1(X0_41,X1_42))))) = k9_relat_1(k7_relat_1(X0_41,X1_42),k10_relat_1(k7_relat_1(X0_41,X1_42),X0_42))
% 11.97/1.99      | v1_funct_1(X0_41) != iProver_top
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top
% 11.97/1.99      | v1_relat_1(k7_relat_1(X0_41,X1_42)) != iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_621,c_623]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 11.97/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_320,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0_41) | v1_relat_1(k7_relat_1(X0_41,X0_42)) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_1]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_613,plain,
% 11.97/1.99      ( v1_relat_1(X0_41) != iProver_top
% 11.97/1.99      | v1_relat_1(k7_relat_1(X0_41,X0_42)) = iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_41445,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(X0_41,X1_42),k1_relat_1(k7_relat_1(X0_41,X1_42))))) = k9_relat_1(k7_relat_1(X0_41,X1_42),k10_relat_1(k7_relat_1(X0_41,X1_42),X0_42))
% 11.97/1.99      | v1_funct_1(X0_41) != iProver_top
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(forward_subsumption_resolution,
% 11.97/1.99                [status(thm)],
% 11.97/1.99                [c_1635,c_613]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_41449,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(sK2,X1_42),k1_relat_1(k7_relat_1(sK2,X1_42))))) = k9_relat_1(k7_relat_1(sK2,X1_42),k10_relat_1(k7_relat_1(sK2,X1_42),X0_42))
% 11.97/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_624,c_41445]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_15,negated_conjecture,
% 11.97/1.99      ( v1_relat_1(sK2) ),
% 11.97/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_307,negated_conjecture,
% 11.97/1.99      ( v1_relat_1(sK2) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_15]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_625,plain,
% 11.97/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_4,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0)
% 11.97/1.99      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 11.97/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_317,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0_41)
% 11.97/1.99      | k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_4]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_616,plain,
% 11.97/1.99      ( k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41)
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_794,plain,
% 11.97/1.99      ( k9_relat_1(k7_relat_1(X0_41,X0_42),k1_relat_1(k7_relat_1(X0_41,X0_42))) = k2_relat_1(k7_relat_1(X0_41,X0_42))
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_613,c_616]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2180,plain,
% 11.97/1.99      ( k9_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k2_relat_1(k7_relat_1(sK2,X0_42)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_794]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_5,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0)
% 11.97/1.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.97/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_316,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0_41)
% 11.97/1.99      | k2_relat_1(k7_relat_1(X0_41,X0_42)) = k9_relat_1(X0_41,X0_42) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_5]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_617,plain,
% 11.97/1.99      ( k2_relat_1(k7_relat_1(X0_41,X0_42)) = k9_relat_1(X0_41,X0_42)
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_869,plain,
% 11.97/1.99      ( k2_relat_1(k7_relat_1(sK2,X0_42)) = k9_relat_1(sK2,X0_42) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_617]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2190,plain,
% 11.97/1.99      ( k9_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k9_relat_1(sK2,X0_42) ),
% 11.97/1.99      inference(light_normalisation,[status(thm)],[c_2180,c_869]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_7,plain,
% 11.97/1.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 11.97/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_314,plain,
% 11.97/1.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),X0_42)
% 11.97/1.99      | ~ v1_relat_1(X0_41) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_7]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_619,plain,
% 11.97/1.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),X0_42) = iProver_top
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_3,plain,
% 11.97/1.99      ( ~ r1_tarski(X0,X1)
% 11.97/1.99      | ~ v1_relat_1(X2)
% 11.97/1.99      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
% 11.97/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_318,plain,
% 11.97/1.99      ( ~ r1_tarski(X0_42,X1_42)
% 11.97/1.99      | ~ v1_relat_1(X0_41)
% 11.97/1.99      | k7_relat_1(k7_relat_1(X0_41,X1_42),X0_42) = k7_relat_1(X0_41,X0_42) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_3]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_615,plain,
% 11.97/1.99      ( k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) = k7_relat_1(X0_41,X1_42)
% 11.97/1.99      | r1_tarski(X1_42,X0_42) != iProver_top
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1463,plain,
% 11.97/1.99      ( k7_relat_1(k7_relat_1(X0_41,X0_42),k1_relat_1(k7_relat_1(X1_41,X0_42))) = k7_relat_1(X0_41,k1_relat_1(k7_relat_1(X1_41,X0_42)))
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top
% 11.97/1.99      | v1_relat_1(X1_41) != iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_619,c_615]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_29762,plain,
% 11.97/1.99      ( k7_relat_1(k7_relat_1(X0_41,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK2,X0_42)))
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_1463]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_31540,plain,
% 11.97/1.99      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0_42))) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_29762]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_6,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0)
% 11.97/1.99      | k7_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
% 11.97/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_315,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0_41)
% 11.97/1.99      | k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),X0_42))) = k7_relat_1(X0_41,X0_42) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_6]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_618,plain,
% 11.97/1.99      ( k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),X0_42))) = k7_relat_1(X0_41,X0_42)
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1549,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0_42))) = k7_relat_1(sK2,X0_42) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_618]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_8,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0)
% 11.97/1.99      | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 11.97/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_313,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0_41)
% 11.97/1.99      | k1_setfam_1(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),X0_42)) = k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_8]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_620,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),X0_42)) = k1_relat_1(k7_relat_1(X0_41,X0_42))
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_946,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0_42)) = k1_relat_1(k7_relat_1(sK2,X0_42)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_620]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1556,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0_42))) = k7_relat_1(sK2,X0_42) ),
% 11.97/1.99      inference(light_normalisation,[status(thm)],[c_1549,c_946]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_31559,plain,
% 11.97/1.99      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k7_relat_1(sK2,X0_42) ),
% 11.97/1.99      inference(light_normalisation,[status(thm)],[c_31540,c_1556]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0)
% 11.97/1.99      | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 11.97/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_319,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0_41)
% 11.97/1.99      | k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_2]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_614,plain,
% 11.97/1.99      ( k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_854,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_614]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_11,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0)
% 11.97/1.99      | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 11.97/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_311,plain,
% 11.97/1.99      ( ~ v1_relat_1(X0_41)
% 11.97/1.99      | k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(X0_41,X1_42))) = k10_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_11]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_622,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(X0_41,X1_42))) = k10_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1565,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(sK2,X1_42))) = k10_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_622]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1661,plain,
% 11.97/1.99      ( k7_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(sK2,X1_42)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_1565,c_854]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2641,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))),X2_42)) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k10_relat_1(sK2,X2_42)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_854,c_1661]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1796,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42))) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_854,c_1556]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_0,plain,
% 11.97/1.99      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 11.97/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_321,plain,
% 11.97/1.99      ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_0]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1094,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_321,c_854]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1818,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42))) = k7_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
% 11.97/1.99      inference(light_normalisation,[status(thm)],[c_1796,c_1094]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2643,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42))),X2_42)) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),k10_relat_1(sK2,X2_42)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_1818,c_1661]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2670,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42)) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k10_relat_1(sK2,X2_42)) ),
% 11.97/1.99      inference(light_normalisation,[status(thm)],[c_2643,c_1818]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2675,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))),X2_42)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42)) ),
% 11.97/1.99      inference(light_normalisation,[status(thm)],[c_2641,c_2670]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2677,plain,
% 11.97/1.99      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),X2_42)) ),
% 11.97/1.99      inference(light_normalisation,[status(thm)],[c_2675,c_1094]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_22936,plain,
% 11.97/1.99      ( k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),X2_42)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_2677,c_869]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_31607,plain,
% 11.97/1.99      ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0_42))),X0_42),X1_42)) = k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42))) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_31559,c_22936]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_31895,plain,
% 11.97/1.99      ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42)) = k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42))) ),
% 11.97/1.99      inference(light_normalisation,[status(thm)],[c_31607,c_1556]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_31896,plain,
% 11.97/1.99      ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) ),
% 11.97/1.99      inference(demodulation,[status(thm)],[c_31895,c_869]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1566,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(k7_relat_1(X0_41,X1_42),X2_42))) = k10_relat_1(k7_relat_1(k7_relat_1(X0_41,X1_42),X0_42),X2_42)
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_613,c_622]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_37288,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(k7_relat_1(sK2,X1_42),X2_42))) = k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),X2_42) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_1566]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_870,plain,
% 11.97/1.99      ( k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)) = k9_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
% 11.97/1.99      | v1_relat_1(X0_41) != iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_613,c_617]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_4418,plain,
% 11.97/1.99      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k9_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_625,c_870]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1099,plain,
% 11.97/1.99      ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_854,c_869]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_4563,plain,
% 11.97/1.99      ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k9_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
% 11.97/1.99      inference(demodulation,[status(thm)],[c_4418,c_1099]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_37540,plain,
% 11.97/1.99      ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X1_42),X2_42)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X0_42),X2_42)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_37288,c_4563]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_41466,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(sK2,X1_42))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_42),X0_42))
% 11.97/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.97/1.99      inference(demodulation,
% 11.97/1.99                [status(thm)],
% 11.97/1.99                [c_41449,c_2190,c_31896,c_37540]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_16,plain,
% 11.97/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_42643,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(sK2,X1_42))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_42),X0_42)) ),
% 11.97/1.99      inference(global_propositional_subsumption,
% 11.97/1.99                [status(thm)],
% 11.97/1.99                [c_41466,c_16]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_13,negated_conjecture,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
% 11.97/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_309,negated_conjecture,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
% 11.97/1.99      inference(subtyping,[status(esa)],[c_13]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_721,plain,
% 11.97/1.99      ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 11.97/1.99      inference(demodulation,[status(thm)],[c_321,c_309]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1656,plain,
% 11.97/1.99      ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 11.97/1.99      inference(demodulation,[status(thm)],[c_1565,c_721]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_42647,plain,
% 11.97/1.99      ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 11.97/1.99      inference(demodulation,[status(thm)],[c_42643,c_1656]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_325,plain,( X0_43 = X0_43 ),theory(equality) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_7616,plain,
% 11.97/1.99      ( k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) = k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_325]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_332,plain,
% 11.97/1.99      ( X0_43 != X1_43 | k1_setfam_1(X0_43) = k1_setfam_1(X1_43) ),
% 11.97/1.99      theory(equality) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_4998,plain,
% 11.97/1.99      ( X0_43 != k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))
% 11.97/1.99      | k1_setfam_1(X0_43) = k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_332]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_7615,plain,
% 11.97/1.99      ( k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) != k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))
% 11.97/1.99      | k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) = k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_4998]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(contradiction,plain,
% 11.97/1.99      ( $false ),
% 11.97/1.99      inference(minisat,[status(thm)],[c_42647,c_7616,c_7615]) ).
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.97/1.99  
% 11.97/1.99  ------                               Statistics
% 11.97/1.99  
% 11.97/1.99  ------ General
% 11.97/1.99  
% 11.97/1.99  abstr_ref_over_cycles:                  0
% 11.97/1.99  abstr_ref_under_cycles:                 0
% 11.97/1.99  gc_basic_clause_elim:                   0
% 11.97/1.99  forced_gc_time:                         0
% 11.97/1.99  parsing_time:                           0.01
% 11.97/1.99  unif_index_cands_time:                  0.
% 11.97/1.99  unif_index_add_time:                    0.
% 11.97/1.99  orderings_time:                         0.
% 11.97/1.99  out_proof_time:                         0.011
% 11.97/1.99  total_time:                             1.388
% 11.97/1.99  num_of_symbols:                         44
% 11.97/1.99  num_of_terms:                           62726
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing
% 11.97/1.99  
% 11.97/1.99  num_of_splits:                          0
% 11.97/1.99  num_of_split_atoms:                     0
% 11.97/1.99  num_of_reused_defs:                     0
% 11.97/1.99  num_eq_ax_congr_red:                    3
% 11.97/1.99  num_of_sem_filtered_clauses:            1
% 11.97/1.99  num_of_subtypes:                        3
% 11.97/1.99  monotx_restored_types:                  0
% 11.97/1.99  sat_num_of_epr_types:                   0
% 11.97/1.99  sat_num_of_non_cyclic_types:            0
% 11.97/1.99  sat_guarded_non_collapsed_types:        0
% 11.97/1.99  num_pure_diseq_elim:                    0
% 11.97/1.99  simp_replaced_by:                       0
% 11.97/1.99  res_preprocessed:                       93
% 11.97/1.99  prep_upred:                             0
% 11.97/1.99  prep_unflattend:                        4
% 11.97/1.99  smt_new_axioms:                         0
% 11.97/1.99  pred_elim_cands:                        3
% 11.97/1.99  pred_elim:                              0
% 11.97/1.99  pred_elim_cl:                           0
% 11.97/1.99  pred_elim_cycles:                       2
% 11.97/1.99  merged_defs:                            0
% 11.97/1.99  merged_defs_ncl:                        0
% 11.97/1.99  bin_hyper_res:                          0
% 11.97/1.99  prep_cycles:                            4
% 11.97/1.99  pred_elim_time:                         0.001
% 11.97/1.99  splitting_time:                         0.
% 11.97/1.99  sem_filter_time:                        0.
% 11.97/1.99  monotx_time:                            0.
% 11.97/1.99  subtype_inf_time:                       0.
% 11.97/1.99  
% 11.97/1.99  ------ Problem properties
% 11.97/1.99  
% 11.97/1.99  clauses:                                15
% 11.97/1.99  conjectures:                            3
% 11.97/1.99  epr:                                    2
% 11.97/1.99  horn:                                   15
% 11.97/1.99  ground:                                 3
% 11.97/1.99  unary:                                  4
% 11.97/1.99  binary:                                 8
% 11.97/1.99  lits:                                   29
% 11.97/1.99  lits_eq:                                10
% 11.97/1.99  fd_pure:                                0
% 11.97/2.00  fd_pseudo:                              0
% 11.97/2.00  fd_cond:                                0
% 11.97/2.00  fd_pseudo_cond:                         0
% 11.97/2.00  ac_symbols:                             0
% 11.97/2.00  
% 11.97/2.00  ------ Propositional Solver
% 11.97/2.00  
% 11.97/2.00  prop_solver_calls:                      33
% 11.97/2.00  prop_fast_solver_calls:                 690
% 11.97/2.00  smt_solver_calls:                       0
% 11.97/2.00  smt_fast_solver_calls:                  0
% 11.97/2.00  prop_num_of_clauses:                    10430
% 11.97/2.00  prop_preprocess_simplified:             14328
% 11.97/2.00  prop_fo_subsumed:                       8
% 11.97/2.00  prop_solver_time:                       0.
% 11.97/2.00  smt_solver_time:                        0.
% 11.97/2.00  smt_fast_solver_time:                   0.
% 11.97/2.00  prop_fast_solver_time:                  0.
% 11.97/2.00  prop_unsat_core_time:                   0.001
% 11.97/2.00  
% 11.97/2.00  ------ QBF
% 11.97/2.00  
% 11.97/2.00  qbf_q_res:                              0
% 11.97/2.00  qbf_num_tautologies:                    0
% 11.97/2.00  qbf_prep_cycles:                        0
% 11.97/2.00  
% 11.97/2.00  ------ BMC1
% 11.97/2.00  
% 11.97/2.00  bmc1_current_bound:                     -1
% 11.97/2.00  bmc1_last_solved_bound:                 -1
% 11.97/2.00  bmc1_unsat_core_size:                   -1
% 11.97/2.00  bmc1_unsat_core_parents_size:           -1
% 11.97/2.00  bmc1_merge_next_fun:                    0
% 11.97/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.97/2.00  
% 11.97/2.00  ------ Instantiation
% 11.97/2.00  
% 11.97/2.00  inst_num_of_clauses:                    2465
% 11.97/2.00  inst_num_in_passive:                    1272
% 11.97/2.00  inst_num_in_active:                     986
% 11.97/2.00  inst_num_in_unprocessed:                207
% 11.97/2.00  inst_num_of_loops:                      1020
% 11.97/2.00  inst_num_of_learning_restarts:          0
% 11.97/2.00  inst_num_moves_active_passive:          27
% 11.97/2.00  inst_lit_activity:                      0
% 11.97/2.00  inst_lit_activity_moves:                0
% 11.97/2.00  inst_num_tautologies:                   0
% 11.97/2.00  inst_num_prop_implied:                  0
% 11.97/2.00  inst_num_existing_simplified:           0
% 11.97/2.00  inst_num_eq_res_simplified:             0
% 11.97/2.00  inst_num_child_elim:                    0
% 11.97/2.00  inst_num_of_dismatching_blockings:      2529
% 11.97/2.00  inst_num_of_non_proper_insts:           4277
% 11.97/2.00  inst_num_of_duplicates:                 0
% 11.97/2.00  inst_inst_num_from_inst_to_res:         0
% 11.97/2.00  inst_dismatching_checking_time:         0.
% 11.97/2.00  
% 11.97/2.00  ------ Resolution
% 11.97/2.00  
% 11.97/2.00  res_num_of_clauses:                     0
% 11.97/2.00  res_num_in_passive:                     0
% 11.97/2.00  res_num_in_active:                      0
% 11.97/2.00  res_num_of_loops:                       97
% 11.97/2.00  res_forward_subset_subsumed:            797
% 11.97/2.00  res_backward_subset_subsumed:           2
% 11.97/2.00  res_forward_subsumed:                   0
% 11.97/2.00  res_backward_subsumed:                  0
% 11.97/2.00  res_forward_subsumption_resolution:     0
% 11.97/2.00  res_backward_subsumption_resolution:    0
% 11.97/2.00  res_clause_to_clause_subsumption:       21002
% 11.97/2.00  res_orphan_elimination:                 0
% 11.97/2.00  res_tautology_del:                      743
% 11.97/2.00  res_num_eq_res_simplified:              0
% 11.97/2.00  res_num_sel_changes:                    0
% 11.97/2.00  res_moves_from_active_to_pass:          0
% 11.97/2.00  
% 11.97/2.00  ------ Superposition
% 11.97/2.00  
% 11.97/2.00  sup_time_total:                         0.
% 11.97/2.00  sup_time_generating:                    0.
% 11.97/2.00  sup_time_sim_full:                      0.
% 11.97/2.00  sup_time_sim_immed:                     0.
% 11.97/2.00  
% 11.97/2.00  sup_num_of_clauses:                     3369
% 11.97/2.00  sup_num_in_active:                      168
% 11.97/2.00  sup_num_in_passive:                     3201
% 11.97/2.00  sup_num_of_loops:                       203
% 11.97/2.00  sup_fw_superposition:                   5840
% 11.97/2.00  sup_bw_superposition:                   2745
% 11.97/2.00  sup_immediate_simplified:               4582
% 11.97/2.00  sup_given_eliminated:                   16
% 11.97/2.00  comparisons_done:                       0
% 11.97/2.00  comparisons_avoided:                    0
% 11.97/2.00  
% 11.97/2.00  ------ Simplifications
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  sim_fw_subset_subsumed:                 59
% 11.97/2.00  sim_bw_subset_subsumed:                 23
% 11.97/2.00  sim_fw_subsumed:                        283
% 11.97/2.00  sim_bw_subsumed:                        131
% 11.97/2.00  sim_fw_subsumption_res:                 3
% 11.97/2.00  sim_bw_subsumption_res:                 3
% 11.97/2.00  sim_tautology_del:                      6
% 11.97/2.00  sim_eq_tautology_del:                   178
% 11.97/2.00  sim_eq_res_simp:                        0
% 11.97/2.00  sim_fw_demodulated:                     1950
% 11.97/2.00  sim_bw_demodulated:                     624
% 11.97/2.00  sim_light_normalised:                   2317
% 11.97/2.00  sim_joinable_taut:                      0
% 11.97/2.00  sim_joinable_simp:                      0
% 11.97/2.00  sim_ac_normalised:                      0
% 11.97/2.00  sim_smt_subsumption:                    0
% 11.97/2.00  
%------------------------------------------------------------------------------
