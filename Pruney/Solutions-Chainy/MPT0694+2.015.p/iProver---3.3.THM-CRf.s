%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:58 EST 2020

% Result     : Theorem 15.37s
% Output     : CNFRefutation 15.37s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 330 expanded)
%              Number of clauses        :   64 (  80 expanded)
%              Number of leaves         :   18 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          :  276 ( 657 expanded)
%              Number of equality atoms :  111 ( 250 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f33,f53,f53])).

fof(f51,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f51,f53,f53])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f43,f53,f53])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_509,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_520,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_513,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1233,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_509,c_513])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_519,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1251,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k10_relat_1(k7_relat_1(sK2,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_519])).

cnf(c_1418,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK2,X0),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_520,c_1251])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_515,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2029,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,X1),X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_515])).

cnf(c_21410,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_509,c_2029])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_512,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_21681,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) = iProver_top
    | v1_funct_1(k7_relat_1(sK2,X0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21410,c_512])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_518,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_511,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_688,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_511])).

cnf(c_1245,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1233,c_688])).

cnf(c_2229,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_518,c_1245])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_47,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_51,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_621,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_622,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) = iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_262,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_757,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_268,plain,
    ( X0 != X1
    | X2 != X3
    | k9_relat_1(X0,X2) = k9_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_662,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(X0,X1)
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_779,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_781,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_780,plain,
    ( ~ v1_relat_1(sK2)
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1))) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_690,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),X0)
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_905,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_907,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) = iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_905])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_906,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_909,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_266,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_712,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),X2)
    | X2 != X1
    | k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != X0 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_1101,plain,
    ( ~ r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),X1)
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),X2)
    | X2 != X1
    | k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_15417,plain,
    ( ~ r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),X1)
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_17393,plain,
    ( ~ r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_15417])).

cnf(c_17394,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | sK1 != sK1
    | r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17393])).

cnf(c_17396,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | sK1 != sK1
    | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_17394])).

cnf(c_34043,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2229,c_15,c_16,c_18,c_47,c_51,c_622,c_757,c_781,c_780,c_907,c_909,c_17396])).

cnf(c_34048,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21681,c_34043])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_10561,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_10562,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10561])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3696,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3697,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK0)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3696])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34048,c_10562,c_3697,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:16:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.37/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.37/2.48  
% 15.37/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.37/2.48  
% 15.37/2.48  ------  iProver source info
% 15.37/2.48  
% 15.37/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.37/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.37/2.48  git: non_committed_changes: false
% 15.37/2.48  git: last_make_outside_of_git: false
% 15.37/2.48  
% 15.37/2.48  ------ 
% 15.37/2.48  
% 15.37/2.48  ------ Input Options
% 15.37/2.48  
% 15.37/2.48  --out_options                           all
% 15.37/2.48  --tptp_safe_out                         true
% 15.37/2.48  --problem_path                          ""
% 15.37/2.48  --include_path                          ""
% 15.37/2.48  --clausifier                            res/vclausify_rel
% 15.37/2.48  --clausifier_options                    --mode clausify
% 15.37/2.48  --stdin                                 false
% 15.37/2.48  --stats_out                             all
% 15.37/2.48  
% 15.37/2.48  ------ General Options
% 15.37/2.48  
% 15.37/2.48  --fof                                   false
% 15.37/2.48  --time_out_real                         305.
% 15.37/2.48  --time_out_virtual                      -1.
% 15.37/2.48  --symbol_type_check                     false
% 15.37/2.48  --clausify_out                          false
% 15.37/2.48  --sig_cnt_out                           false
% 15.37/2.48  --trig_cnt_out                          false
% 15.37/2.48  --trig_cnt_out_tolerance                1.
% 15.37/2.48  --trig_cnt_out_sk_spl                   false
% 15.37/2.48  --abstr_cl_out                          false
% 15.37/2.48  
% 15.37/2.48  ------ Global Options
% 15.37/2.48  
% 15.37/2.48  --schedule                              default
% 15.37/2.48  --add_important_lit                     false
% 15.37/2.48  --prop_solver_per_cl                    1000
% 15.37/2.48  --min_unsat_core                        false
% 15.37/2.48  --soft_assumptions                      false
% 15.37/2.48  --soft_lemma_size                       3
% 15.37/2.48  --prop_impl_unit_size                   0
% 15.37/2.48  --prop_impl_unit                        []
% 15.37/2.48  --share_sel_clauses                     true
% 15.37/2.48  --reset_solvers                         false
% 15.37/2.48  --bc_imp_inh                            [conj_cone]
% 15.37/2.48  --conj_cone_tolerance                   3.
% 15.37/2.48  --extra_neg_conj                        none
% 15.37/2.48  --large_theory_mode                     true
% 15.37/2.48  --prolific_symb_bound                   200
% 15.37/2.48  --lt_threshold                          2000
% 15.37/2.48  --clause_weak_htbl                      true
% 15.37/2.48  --gc_record_bc_elim                     false
% 15.37/2.48  
% 15.37/2.48  ------ Preprocessing Options
% 15.37/2.48  
% 15.37/2.48  --preprocessing_flag                    true
% 15.37/2.48  --time_out_prep_mult                    0.1
% 15.37/2.48  --splitting_mode                        input
% 15.37/2.48  --splitting_grd                         true
% 15.37/2.48  --splitting_cvd                         false
% 15.37/2.48  --splitting_cvd_svl                     false
% 15.37/2.48  --splitting_nvd                         32
% 15.37/2.48  --sub_typing                            true
% 15.37/2.48  --prep_gs_sim                           true
% 15.37/2.48  --prep_unflatten                        true
% 15.37/2.48  --prep_res_sim                          true
% 15.37/2.48  --prep_upred                            true
% 15.37/2.48  --prep_sem_filter                       exhaustive
% 15.37/2.48  --prep_sem_filter_out                   false
% 15.37/2.48  --pred_elim                             true
% 15.37/2.48  --res_sim_input                         true
% 15.37/2.48  --eq_ax_congr_red                       true
% 15.37/2.48  --pure_diseq_elim                       true
% 15.37/2.48  --brand_transform                       false
% 15.37/2.48  --non_eq_to_eq                          false
% 15.37/2.48  --prep_def_merge                        true
% 15.37/2.48  --prep_def_merge_prop_impl              false
% 15.37/2.48  --prep_def_merge_mbd                    true
% 15.37/2.48  --prep_def_merge_tr_red                 false
% 15.37/2.48  --prep_def_merge_tr_cl                  false
% 15.37/2.48  --smt_preprocessing                     true
% 15.37/2.48  --smt_ac_axioms                         fast
% 15.37/2.48  --preprocessed_out                      false
% 15.37/2.48  --preprocessed_stats                    false
% 15.37/2.48  
% 15.37/2.48  ------ Abstraction refinement Options
% 15.37/2.48  
% 15.37/2.48  --abstr_ref                             []
% 15.37/2.48  --abstr_ref_prep                        false
% 15.37/2.48  --abstr_ref_until_sat                   false
% 15.37/2.48  --abstr_ref_sig_restrict                funpre
% 15.37/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.37/2.48  --abstr_ref_under                       []
% 15.37/2.48  
% 15.37/2.48  ------ SAT Options
% 15.37/2.48  
% 15.37/2.48  --sat_mode                              false
% 15.37/2.48  --sat_fm_restart_options                ""
% 15.37/2.48  --sat_gr_def                            false
% 15.37/2.48  --sat_epr_types                         true
% 15.37/2.48  --sat_non_cyclic_types                  false
% 15.37/2.48  --sat_finite_models                     false
% 15.37/2.48  --sat_fm_lemmas                         false
% 15.37/2.48  --sat_fm_prep                           false
% 15.37/2.48  --sat_fm_uc_incr                        true
% 15.37/2.48  --sat_out_model                         small
% 15.37/2.48  --sat_out_clauses                       false
% 15.37/2.48  
% 15.37/2.48  ------ QBF Options
% 15.37/2.48  
% 15.37/2.48  --qbf_mode                              false
% 15.37/2.48  --qbf_elim_univ                         false
% 15.37/2.48  --qbf_dom_inst                          none
% 15.37/2.48  --qbf_dom_pre_inst                      false
% 15.37/2.48  --qbf_sk_in                             false
% 15.37/2.48  --qbf_pred_elim                         true
% 15.37/2.48  --qbf_split                             512
% 15.37/2.48  
% 15.37/2.48  ------ BMC1 Options
% 15.37/2.48  
% 15.37/2.48  --bmc1_incremental                      false
% 15.37/2.48  --bmc1_axioms                           reachable_all
% 15.37/2.48  --bmc1_min_bound                        0
% 15.37/2.48  --bmc1_max_bound                        -1
% 15.37/2.48  --bmc1_max_bound_default                -1
% 15.37/2.48  --bmc1_symbol_reachability              true
% 15.37/2.48  --bmc1_property_lemmas                  false
% 15.37/2.48  --bmc1_k_induction                      false
% 15.37/2.48  --bmc1_non_equiv_states                 false
% 15.37/2.48  --bmc1_deadlock                         false
% 15.37/2.48  --bmc1_ucm                              false
% 15.37/2.48  --bmc1_add_unsat_core                   none
% 15.37/2.48  --bmc1_unsat_core_children              false
% 15.37/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.37/2.48  --bmc1_out_stat                         full
% 15.37/2.48  --bmc1_ground_init                      false
% 15.37/2.48  --bmc1_pre_inst_next_state              false
% 15.37/2.48  --bmc1_pre_inst_state                   false
% 15.37/2.48  --bmc1_pre_inst_reach_state             false
% 15.37/2.48  --bmc1_out_unsat_core                   false
% 15.37/2.48  --bmc1_aig_witness_out                  false
% 15.37/2.48  --bmc1_verbose                          false
% 15.37/2.48  --bmc1_dump_clauses_tptp                false
% 15.37/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.37/2.48  --bmc1_dump_file                        -
% 15.37/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.37/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.37/2.48  --bmc1_ucm_extend_mode                  1
% 15.37/2.48  --bmc1_ucm_init_mode                    2
% 15.37/2.48  --bmc1_ucm_cone_mode                    none
% 15.37/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.37/2.48  --bmc1_ucm_relax_model                  4
% 15.37/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.37/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.37/2.48  --bmc1_ucm_layered_model                none
% 15.37/2.48  --bmc1_ucm_max_lemma_size               10
% 15.37/2.48  
% 15.37/2.48  ------ AIG Options
% 15.37/2.48  
% 15.37/2.48  --aig_mode                              false
% 15.37/2.48  
% 15.37/2.48  ------ Instantiation Options
% 15.37/2.48  
% 15.37/2.48  --instantiation_flag                    true
% 15.37/2.48  --inst_sos_flag                         false
% 15.37/2.48  --inst_sos_phase                        true
% 15.37/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.37/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.37/2.48  --inst_lit_sel_side                     num_symb
% 15.37/2.48  --inst_solver_per_active                1400
% 15.37/2.48  --inst_solver_calls_frac                1.
% 15.37/2.48  --inst_passive_queue_type               priority_queues
% 15.37/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.37/2.48  --inst_passive_queues_freq              [25;2]
% 15.37/2.48  --inst_dismatching                      true
% 15.37/2.48  --inst_eager_unprocessed_to_passive     true
% 15.37/2.48  --inst_prop_sim_given                   true
% 15.37/2.48  --inst_prop_sim_new                     false
% 15.37/2.48  --inst_subs_new                         false
% 15.37/2.48  --inst_eq_res_simp                      false
% 15.37/2.48  --inst_subs_given                       false
% 15.37/2.48  --inst_orphan_elimination               true
% 15.37/2.48  --inst_learning_loop_flag               true
% 15.37/2.48  --inst_learning_start                   3000
% 15.37/2.48  --inst_learning_factor                  2
% 15.37/2.48  --inst_start_prop_sim_after_learn       3
% 15.37/2.48  --inst_sel_renew                        solver
% 15.37/2.48  --inst_lit_activity_flag                true
% 15.37/2.48  --inst_restr_to_given                   false
% 15.37/2.48  --inst_activity_threshold               500
% 15.37/2.48  --inst_out_proof                        true
% 15.37/2.48  
% 15.37/2.48  ------ Resolution Options
% 15.37/2.48  
% 15.37/2.48  --resolution_flag                       true
% 15.37/2.48  --res_lit_sel                           adaptive
% 15.37/2.48  --res_lit_sel_side                      none
% 15.37/2.48  --res_ordering                          kbo
% 15.37/2.48  --res_to_prop_solver                    active
% 15.37/2.48  --res_prop_simpl_new                    false
% 15.37/2.48  --res_prop_simpl_given                  true
% 15.37/2.48  --res_passive_queue_type                priority_queues
% 15.37/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.37/2.48  --res_passive_queues_freq               [15;5]
% 15.37/2.48  --res_forward_subs                      full
% 15.37/2.48  --res_backward_subs                     full
% 15.37/2.48  --res_forward_subs_resolution           true
% 15.37/2.48  --res_backward_subs_resolution          true
% 15.37/2.48  --res_orphan_elimination                true
% 15.37/2.48  --res_time_limit                        2.
% 15.37/2.48  --res_out_proof                         true
% 15.37/2.48  
% 15.37/2.48  ------ Superposition Options
% 15.37/2.48  
% 15.37/2.48  --superposition_flag                    true
% 15.37/2.48  --sup_passive_queue_type                priority_queues
% 15.37/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.37/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.37/2.48  --demod_completeness_check              fast
% 15.37/2.48  --demod_use_ground                      true
% 15.37/2.48  --sup_to_prop_solver                    passive
% 15.37/2.48  --sup_prop_simpl_new                    true
% 15.37/2.48  --sup_prop_simpl_given                  true
% 15.37/2.48  --sup_fun_splitting                     false
% 15.37/2.48  --sup_smt_interval                      50000
% 15.37/2.48  
% 15.37/2.48  ------ Superposition Simplification Setup
% 15.37/2.48  
% 15.37/2.48  --sup_indices_passive                   []
% 15.37/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.37/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.37/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.37/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.37/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.37/2.48  --sup_full_bw                           [BwDemod]
% 15.37/2.48  --sup_immed_triv                        [TrivRules]
% 15.37/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.37/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.37/2.48  --sup_immed_bw_main                     []
% 15.37/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.37/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.37/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.37/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.37/2.48  
% 15.37/2.48  ------ Combination Options
% 15.37/2.48  
% 15.37/2.48  --comb_res_mult                         3
% 15.37/2.48  --comb_sup_mult                         2
% 15.37/2.48  --comb_inst_mult                        10
% 15.37/2.48  
% 15.37/2.48  ------ Debug Options
% 15.37/2.48  
% 15.37/2.48  --dbg_backtrace                         false
% 15.37/2.48  --dbg_dump_prop_clauses                 false
% 15.37/2.48  --dbg_dump_prop_clauses_file            -
% 15.37/2.48  --dbg_out_stat                          false
% 15.37/2.48  ------ Parsing...
% 15.37/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.37/2.48  
% 15.37/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.37/2.48  
% 15.37/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.37/2.48  
% 15.37/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.37/2.48  ------ Proving...
% 15.37/2.48  ------ Problem Properties 
% 15.37/2.48  
% 15.37/2.48  
% 15.37/2.48  clauses                                 14
% 15.37/2.48  conjectures                             3
% 15.37/2.48  EPR                                     4
% 15.37/2.48  Horn                                    14
% 15.37/2.48  unary                                   5
% 15.37/2.48  binary                                  4
% 15.37/2.48  lits                                    28
% 15.37/2.48  lits eq                                 4
% 15.37/2.48  fd_pure                                 0
% 15.37/2.48  fd_pseudo                               0
% 15.37/2.48  fd_cond                                 0
% 15.37/2.48  fd_pseudo_cond                          1
% 15.37/2.48  AC symbols                              0
% 15.37/2.48  
% 15.37/2.48  ------ Schedule dynamic 5 is on 
% 15.37/2.48  
% 15.37/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.37/2.48  
% 15.37/2.48  
% 15.37/2.48  ------ 
% 15.37/2.48  Current options:
% 15.37/2.48  ------ 
% 15.37/2.48  
% 15.37/2.48  ------ Input Options
% 15.37/2.48  
% 15.37/2.48  --out_options                           all
% 15.37/2.48  --tptp_safe_out                         true
% 15.37/2.48  --problem_path                          ""
% 15.37/2.48  --include_path                          ""
% 15.37/2.48  --clausifier                            res/vclausify_rel
% 15.37/2.48  --clausifier_options                    --mode clausify
% 15.37/2.48  --stdin                                 false
% 15.37/2.48  --stats_out                             all
% 15.37/2.48  
% 15.37/2.48  ------ General Options
% 15.37/2.48  
% 15.37/2.48  --fof                                   false
% 15.37/2.48  --time_out_real                         305.
% 15.37/2.48  --time_out_virtual                      -1.
% 15.37/2.48  --symbol_type_check                     false
% 15.37/2.48  --clausify_out                          false
% 15.37/2.48  --sig_cnt_out                           false
% 15.37/2.48  --trig_cnt_out                          false
% 15.37/2.48  --trig_cnt_out_tolerance                1.
% 15.37/2.48  --trig_cnt_out_sk_spl                   false
% 15.37/2.48  --abstr_cl_out                          false
% 15.37/2.48  
% 15.37/2.48  ------ Global Options
% 15.37/2.48  
% 15.37/2.48  --schedule                              default
% 15.37/2.48  --add_important_lit                     false
% 15.37/2.48  --prop_solver_per_cl                    1000
% 15.37/2.48  --min_unsat_core                        false
% 15.37/2.48  --soft_assumptions                      false
% 15.37/2.48  --soft_lemma_size                       3
% 15.37/2.48  --prop_impl_unit_size                   0
% 15.37/2.48  --prop_impl_unit                        []
% 15.37/2.48  --share_sel_clauses                     true
% 15.37/2.48  --reset_solvers                         false
% 15.37/2.48  --bc_imp_inh                            [conj_cone]
% 15.37/2.48  --conj_cone_tolerance                   3.
% 15.37/2.48  --extra_neg_conj                        none
% 15.37/2.48  --large_theory_mode                     true
% 15.37/2.48  --prolific_symb_bound                   200
% 15.37/2.48  --lt_threshold                          2000
% 15.37/2.48  --clause_weak_htbl                      true
% 15.37/2.48  --gc_record_bc_elim                     false
% 15.37/2.48  
% 15.37/2.48  ------ Preprocessing Options
% 15.37/2.48  
% 15.37/2.48  --preprocessing_flag                    true
% 15.37/2.48  --time_out_prep_mult                    0.1
% 15.37/2.48  --splitting_mode                        input
% 15.37/2.48  --splitting_grd                         true
% 15.37/2.48  --splitting_cvd                         false
% 15.37/2.48  --splitting_cvd_svl                     false
% 15.37/2.48  --splitting_nvd                         32
% 15.37/2.48  --sub_typing                            true
% 15.37/2.48  --prep_gs_sim                           true
% 15.37/2.48  --prep_unflatten                        true
% 15.37/2.48  --prep_res_sim                          true
% 15.37/2.48  --prep_upred                            true
% 15.37/2.48  --prep_sem_filter                       exhaustive
% 15.37/2.48  --prep_sem_filter_out                   false
% 15.37/2.48  --pred_elim                             true
% 15.37/2.48  --res_sim_input                         true
% 15.37/2.48  --eq_ax_congr_red                       true
% 15.37/2.48  --pure_diseq_elim                       true
% 15.37/2.48  --brand_transform                       false
% 15.37/2.48  --non_eq_to_eq                          false
% 15.37/2.48  --prep_def_merge                        true
% 15.37/2.48  --prep_def_merge_prop_impl              false
% 15.37/2.48  --prep_def_merge_mbd                    true
% 15.37/2.48  --prep_def_merge_tr_red                 false
% 15.37/2.48  --prep_def_merge_tr_cl                  false
% 15.37/2.48  --smt_preprocessing                     true
% 15.37/2.48  --smt_ac_axioms                         fast
% 15.37/2.48  --preprocessed_out                      false
% 15.37/2.48  --preprocessed_stats                    false
% 15.37/2.48  
% 15.37/2.48  ------ Abstraction refinement Options
% 15.37/2.48  
% 15.37/2.48  --abstr_ref                             []
% 15.37/2.48  --abstr_ref_prep                        false
% 15.37/2.48  --abstr_ref_until_sat                   false
% 15.37/2.48  --abstr_ref_sig_restrict                funpre
% 15.37/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.37/2.48  --abstr_ref_under                       []
% 15.37/2.48  
% 15.37/2.48  ------ SAT Options
% 15.37/2.48  
% 15.37/2.48  --sat_mode                              false
% 15.37/2.48  --sat_fm_restart_options                ""
% 15.37/2.48  --sat_gr_def                            false
% 15.37/2.48  --sat_epr_types                         true
% 15.37/2.48  --sat_non_cyclic_types                  false
% 15.37/2.48  --sat_finite_models                     false
% 15.37/2.48  --sat_fm_lemmas                         false
% 15.37/2.48  --sat_fm_prep                           false
% 15.37/2.48  --sat_fm_uc_incr                        true
% 15.37/2.48  --sat_out_model                         small
% 15.37/2.48  --sat_out_clauses                       false
% 15.37/2.48  
% 15.37/2.48  ------ QBF Options
% 15.37/2.48  
% 15.37/2.48  --qbf_mode                              false
% 15.37/2.48  --qbf_elim_univ                         false
% 15.37/2.48  --qbf_dom_inst                          none
% 15.37/2.48  --qbf_dom_pre_inst                      false
% 15.37/2.48  --qbf_sk_in                             false
% 15.37/2.48  --qbf_pred_elim                         true
% 15.37/2.48  --qbf_split                             512
% 15.37/2.48  
% 15.37/2.48  ------ BMC1 Options
% 15.37/2.48  
% 15.37/2.48  --bmc1_incremental                      false
% 15.37/2.48  --bmc1_axioms                           reachable_all
% 15.37/2.48  --bmc1_min_bound                        0
% 15.37/2.48  --bmc1_max_bound                        -1
% 15.37/2.48  --bmc1_max_bound_default                -1
% 15.37/2.48  --bmc1_symbol_reachability              true
% 15.37/2.48  --bmc1_property_lemmas                  false
% 15.37/2.48  --bmc1_k_induction                      false
% 15.37/2.48  --bmc1_non_equiv_states                 false
% 15.37/2.48  --bmc1_deadlock                         false
% 15.37/2.48  --bmc1_ucm                              false
% 15.37/2.48  --bmc1_add_unsat_core                   none
% 15.37/2.48  --bmc1_unsat_core_children              false
% 15.37/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.37/2.48  --bmc1_out_stat                         full
% 15.37/2.48  --bmc1_ground_init                      false
% 15.37/2.48  --bmc1_pre_inst_next_state              false
% 15.37/2.48  --bmc1_pre_inst_state                   false
% 15.37/2.48  --bmc1_pre_inst_reach_state             false
% 15.37/2.48  --bmc1_out_unsat_core                   false
% 15.37/2.48  --bmc1_aig_witness_out                  false
% 15.37/2.48  --bmc1_verbose                          false
% 15.37/2.48  --bmc1_dump_clauses_tptp                false
% 15.37/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.37/2.48  --bmc1_dump_file                        -
% 15.37/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.37/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.37/2.48  --bmc1_ucm_extend_mode                  1
% 15.37/2.48  --bmc1_ucm_init_mode                    2
% 15.37/2.48  --bmc1_ucm_cone_mode                    none
% 15.37/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.37/2.48  --bmc1_ucm_relax_model                  4
% 15.37/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.37/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.37/2.48  --bmc1_ucm_layered_model                none
% 15.37/2.48  --bmc1_ucm_max_lemma_size               10
% 15.37/2.48  
% 15.37/2.48  ------ AIG Options
% 15.37/2.48  
% 15.37/2.48  --aig_mode                              false
% 15.37/2.48  
% 15.37/2.48  ------ Instantiation Options
% 15.37/2.48  
% 15.37/2.48  --instantiation_flag                    true
% 15.37/2.48  --inst_sos_flag                         false
% 15.37/2.48  --inst_sos_phase                        true
% 15.37/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.37/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.37/2.48  --inst_lit_sel_side                     none
% 15.37/2.48  --inst_solver_per_active                1400
% 15.37/2.48  --inst_solver_calls_frac                1.
% 15.37/2.48  --inst_passive_queue_type               priority_queues
% 15.37/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.37/2.48  --inst_passive_queues_freq              [25;2]
% 15.37/2.48  --inst_dismatching                      true
% 15.37/2.48  --inst_eager_unprocessed_to_passive     true
% 15.37/2.48  --inst_prop_sim_given                   true
% 15.37/2.48  --inst_prop_sim_new                     false
% 15.37/2.48  --inst_subs_new                         false
% 15.37/2.48  --inst_eq_res_simp                      false
% 15.37/2.48  --inst_subs_given                       false
% 15.37/2.48  --inst_orphan_elimination               true
% 15.37/2.48  --inst_learning_loop_flag               true
% 15.37/2.48  --inst_learning_start                   3000
% 15.37/2.48  --inst_learning_factor                  2
% 15.37/2.48  --inst_start_prop_sim_after_learn       3
% 15.37/2.48  --inst_sel_renew                        solver
% 15.37/2.48  --inst_lit_activity_flag                true
% 15.37/2.48  --inst_restr_to_given                   false
% 15.37/2.48  --inst_activity_threshold               500
% 15.37/2.48  --inst_out_proof                        true
% 15.37/2.48  
% 15.37/2.48  ------ Resolution Options
% 15.37/2.48  
% 15.37/2.48  --resolution_flag                       false
% 15.37/2.48  --res_lit_sel                           adaptive
% 15.37/2.48  --res_lit_sel_side                      none
% 15.37/2.48  --res_ordering                          kbo
% 15.37/2.48  --res_to_prop_solver                    active
% 15.37/2.48  --res_prop_simpl_new                    false
% 15.37/2.48  --res_prop_simpl_given                  true
% 15.37/2.48  --res_passive_queue_type                priority_queues
% 15.37/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.37/2.48  --res_passive_queues_freq               [15;5]
% 15.37/2.48  --res_forward_subs                      full
% 15.37/2.48  --res_backward_subs                     full
% 15.37/2.48  --res_forward_subs_resolution           true
% 15.37/2.48  --res_backward_subs_resolution          true
% 15.37/2.48  --res_orphan_elimination                true
% 15.37/2.48  --res_time_limit                        2.
% 15.37/2.48  --res_out_proof                         true
% 15.37/2.48  
% 15.37/2.48  ------ Superposition Options
% 15.37/2.48  
% 15.37/2.48  --superposition_flag                    true
% 15.37/2.48  --sup_passive_queue_type                priority_queues
% 15.37/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.37/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.37/2.48  --demod_completeness_check              fast
% 15.37/2.48  --demod_use_ground                      true
% 15.37/2.48  --sup_to_prop_solver                    passive
% 15.37/2.48  --sup_prop_simpl_new                    true
% 15.37/2.48  --sup_prop_simpl_given                  true
% 15.37/2.48  --sup_fun_splitting                     false
% 15.37/2.48  --sup_smt_interval                      50000
% 15.37/2.48  
% 15.37/2.48  ------ Superposition Simplification Setup
% 15.37/2.48  
% 15.37/2.48  --sup_indices_passive                   []
% 15.37/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.37/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.37/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.37/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.37/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.37/2.48  --sup_full_bw                           [BwDemod]
% 15.37/2.48  --sup_immed_triv                        [TrivRules]
% 15.37/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.37/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.37/2.48  --sup_immed_bw_main                     []
% 15.37/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.37/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.37/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.37/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.37/2.48  
% 15.37/2.48  ------ Combination Options
% 15.37/2.48  
% 15.37/2.48  --comb_res_mult                         3
% 15.37/2.48  --comb_sup_mult                         2
% 15.37/2.48  --comb_inst_mult                        10
% 15.37/2.48  
% 15.37/2.48  ------ Debug Options
% 15.37/2.48  
% 15.37/2.48  --dbg_backtrace                         false
% 15.37/2.48  --dbg_dump_prop_clauses                 false
% 15.37/2.48  --dbg_dump_prop_clauses_file            -
% 15.37/2.48  --dbg_out_stat                          false
% 15.37/2.48  
% 15.37/2.48  
% 15.37/2.48  
% 15.37/2.48  
% 15.37/2.48  ------ Proving...
% 15.37/2.48  
% 15.37/2.48  
% 15.37/2.48  % SZS status Theorem for theBenchmark.p
% 15.37/2.48  
% 15.37/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.37/2.48  
% 15.37/2.48  fof(f14,conjecture,(
% 15.37/2.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f15,negated_conjecture,(
% 15.37/2.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 15.37/2.48    inference(negated_conjecture,[],[f14])).
% 15.37/2.48  
% 15.37/2.48  fof(f27,plain,(
% 15.37/2.48    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 15.37/2.48    inference(ennf_transformation,[],[f15])).
% 15.37/2.48  
% 15.37/2.48  fof(f28,plain,(
% 15.37/2.48    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 15.37/2.48    inference(flattening,[],[f27])).
% 15.37/2.48  
% 15.37/2.48  fof(f31,plain,(
% 15.37/2.48    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 15.37/2.48    introduced(choice_axiom,[])).
% 15.37/2.48  
% 15.37/2.48  fof(f32,plain,(
% 15.37/2.48    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 15.37/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).
% 15.37/2.48  
% 15.37/2.48  fof(f49,plain,(
% 15.37/2.48    v1_relat_1(sK2)),
% 15.37/2.48    inference(cnf_transformation,[],[f32])).
% 15.37/2.48  
% 15.37/2.48  fof(f2,axiom,(
% 15.37/2.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f29,plain,(
% 15.37/2.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.37/2.48    inference(nnf_transformation,[],[f2])).
% 15.37/2.48  
% 15.37/2.48  fof(f30,plain,(
% 15.37/2.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.37/2.48    inference(flattening,[],[f29])).
% 15.37/2.48  
% 15.37/2.48  fof(f34,plain,(
% 15.37/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.37/2.48    inference(cnf_transformation,[],[f30])).
% 15.37/2.48  
% 15.37/2.48  fof(f61,plain,(
% 15.37/2.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.37/2.48    inference(equality_resolution,[],[f34])).
% 15.37/2.48  
% 15.37/2.48  fof(f12,axiom,(
% 15.37/2.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f24,plain,(
% 15.37/2.48    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 15.37/2.48    inference(ennf_transformation,[],[f12])).
% 15.37/2.48  
% 15.37/2.48  fof(f47,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f24])).
% 15.37/2.48  
% 15.37/2.48  fof(f7,axiom,(
% 15.37/2.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f41,plain,(
% 15.37/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.37/2.48    inference(cnf_transformation,[],[f7])).
% 15.37/2.48  
% 15.37/2.48  fof(f5,axiom,(
% 15.37/2.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f39,plain,(
% 15.37/2.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f5])).
% 15.37/2.48  
% 15.37/2.48  fof(f6,axiom,(
% 15.37/2.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f40,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f6])).
% 15.37/2.48  
% 15.37/2.48  fof(f52,plain,(
% 15.37/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.37/2.48    inference(definition_unfolding,[],[f39,f40])).
% 15.37/2.48  
% 15.37/2.48  fof(f53,plain,(
% 15.37/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 15.37/2.48    inference(definition_unfolding,[],[f41,f52])).
% 15.37/2.48  
% 15.37/2.48  fof(f58,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 15.37/2.48    inference(definition_unfolding,[],[f47,f53])).
% 15.37/2.48  
% 15.37/2.48  fof(f3,axiom,(
% 15.37/2.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f16,plain,(
% 15.37/2.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 15.37/2.48    inference(ennf_transformation,[],[f3])).
% 15.37/2.48  
% 15.37/2.48  fof(f37,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 15.37/2.48    inference(cnf_transformation,[],[f16])).
% 15.37/2.48  
% 15.37/2.48  fof(f55,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) )),
% 15.37/2.48    inference(definition_unfolding,[],[f37,f53])).
% 15.37/2.48  
% 15.37/2.48  fof(f10,axiom,(
% 15.37/2.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f21,plain,(
% 15.37/2.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 15.37/2.48    inference(ennf_transformation,[],[f10])).
% 15.37/2.48  
% 15.37/2.48  fof(f44,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f21])).
% 15.37/2.48  
% 15.37/2.48  fof(f13,axiom,(
% 15.37/2.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f25,plain,(
% 15.37/2.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.37/2.48    inference(ennf_transformation,[],[f13])).
% 15.37/2.48  
% 15.37/2.48  fof(f26,plain,(
% 15.37/2.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.37/2.48    inference(flattening,[],[f25])).
% 15.37/2.48  
% 15.37/2.48  fof(f48,plain,(
% 15.37/2.48    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f26])).
% 15.37/2.48  
% 15.37/2.48  fof(f4,axiom,(
% 15.37/2.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f17,plain,(
% 15.37/2.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 15.37/2.48    inference(ennf_transformation,[],[f4])).
% 15.37/2.48  
% 15.37/2.48  fof(f18,plain,(
% 15.37/2.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 15.37/2.48    inference(flattening,[],[f17])).
% 15.37/2.48  
% 15.37/2.48  fof(f38,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f18])).
% 15.37/2.48  
% 15.37/2.48  fof(f56,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.37/2.48    inference(definition_unfolding,[],[f38,f53])).
% 15.37/2.48  
% 15.37/2.48  fof(f1,axiom,(
% 15.37/2.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f33,plain,(
% 15.37/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f1])).
% 15.37/2.48  
% 15.37/2.48  fof(f54,plain,(
% 15.37/2.48    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 15.37/2.48    inference(definition_unfolding,[],[f33,f53,f53])).
% 15.37/2.48  
% 15.37/2.48  fof(f51,plain,(
% 15.37/2.48    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 15.37/2.48    inference(cnf_transformation,[],[f32])).
% 15.37/2.48  
% 15.37/2.48  fof(f59,plain,(
% 15.37/2.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 15.37/2.48    inference(definition_unfolding,[],[f51,f53,f53])).
% 15.37/2.48  
% 15.37/2.48  fof(f36,plain,(
% 15.37/2.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f30])).
% 15.37/2.48  
% 15.37/2.48  fof(f9,axiom,(
% 15.37/2.48    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f20,plain,(
% 15.37/2.48    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 15.37/2.48    inference(ennf_transformation,[],[f9])).
% 15.37/2.48  
% 15.37/2.48  fof(f43,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f20])).
% 15.37/2.48  
% 15.37/2.48  fof(f57,plain,(
% 15.37/2.48    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_setfam_1(k2_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | ~v1_relat_1(X2)) )),
% 15.37/2.48    inference(definition_unfolding,[],[f43,f53,f53])).
% 15.37/2.48  
% 15.37/2.48  fof(f8,axiom,(
% 15.37/2.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f19,plain,(
% 15.37/2.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 15.37/2.48    inference(ennf_transformation,[],[f8])).
% 15.37/2.48  
% 15.37/2.48  fof(f42,plain,(
% 15.37/2.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f19])).
% 15.37/2.48  
% 15.37/2.48  fof(f11,axiom,(
% 15.37/2.48    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 15.37/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.48  
% 15.37/2.48  fof(f22,plain,(
% 15.37/2.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.37/2.48    inference(ennf_transformation,[],[f11])).
% 15.37/2.48  
% 15.37/2.48  fof(f23,plain,(
% 15.37/2.48    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.37/2.48    inference(flattening,[],[f22])).
% 15.37/2.48  
% 15.37/2.48  fof(f46,plain,(
% 15.37/2.48    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.37/2.48    inference(cnf_transformation,[],[f23])).
% 15.37/2.48  
% 15.37/2.48  fof(f50,plain,(
% 15.37/2.48    v1_funct_1(sK2)),
% 15.37/2.48    inference(cnf_transformation,[],[f32])).
% 15.37/2.48  
% 15.37/2.48  cnf(c_15,negated_conjecture,
% 15.37/2.48      ( v1_relat_1(sK2) ),
% 15.37/2.48      inference(cnf_transformation,[],[f49]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_509,plain,
% 15.37/2.48      ( v1_relat_1(sK2) = iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_3,plain,
% 15.37/2.48      ( r1_tarski(X0,X0) ),
% 15.37/2.48      inference(cnf_transformation,[],[f61]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_520,plain,
% 15.37/2.48      ( r1_tarski(X0,X0) = iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_11,plain,
% 15.37/2.48      ( ~ v1_relat_1(X0)
% 15.37/2.48      | k1_setfam_1(k2_enumset1(X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 15.37/2.48      inference(cnf_transformation,[],[f58]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_513,plain,
% 15.37/2.48      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 15.37/2.48      | v1_relat_1(X1) != iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_1233,plain,
% 15.37/2.48      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 15.37/2.48      inference(superposition,[status(thm)],[c_509,c_513]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_4,plain,
% 15.37/2.48      ( r1_tarski(X0,X1)
% 15.37/2.48      | ~ r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
% 15.37/2.48      inference(cnf_transformation,[],[f55]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_519,plain,
% 15.37/2.48      ( r1_tarski(X0,X1) = iProver_top
% 15.37/2.48      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) != iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_1251,plain,
% 15.37/2.48      ( r1_tarski(X0,X1) = iProver_top
% 15.37/2.48      | r1_tarski(X0,k10_relat_1(k7_relat_1(sK2,X1),X2)) != iProver_top ),
% 15.37/2.48      inference(superposition,[status(thm)],[c_1233,c_519]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_1418,plain,
% 15.37/2.48      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,X0),X1),X0) = iProver_top ),
% 15.37/2.48      inference(superposition,[status(thm)],[c_520,c_1251]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_8,plain,
% 15.37/2.48      ( ~ r1_tarski(X0,X1)
% 15.37/2.48      | ~ v1_relat_1(X2)
% 15.37/2.48      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 15.37/2.48      inference(cnf_transformation,[],[f44]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_515,plain,
% 15.37/2.48      ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 15.37/2.48      | r1_tarski(X2,X1) != iProver_top
% 15.37/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_2029,plain,
% 15.37/2.48      ( k9_relat_1(k7_relat_1(X0,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,X1),X2))
% 15.37/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.37/2.48      inference(superposition,[status(thm)],[c_1418,c_515]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_21410,plain,
% 15.37/2.48      ( k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) ),
% 15.37/2.48      inference(superposition,[status(thm)],[c_509,c_2029]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_12,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 15.37/2.48      | ~ v1_funct_1(X0)
% 15.37/2.48      | ~ v1_relat_1(X0) ),
% 15.37/2.48      inference(cnf_transformation,[],[f48]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_512,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 15.37/2.48      | v1_funct_1(X0) != iProver_top
% 15.37/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_21681,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) = iProver_top
% 15.37/2.48      | v1_funct_1(k7_relat_1(sK2,X0)) != iProver_top
% 15.37/2.48      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 15.37/2.48      inference(superposition,[status(thm)],[c_21410,c_512]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_5,plain,
% 15.37/2.48      ( ~ r1_tarski(X0,X1)
% 15.37/2.48      | ~ r1_tarski(X0,X2)
% 15.37/2.48      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
% 15.37/2.48      inference(cnf_transformation,[],[f56]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_518,plain,
% 15.37/2.48      ( r1_tarski(X0,X1) != iProver_top
% 15.37/2.48      | r1_tarski(X0,X2) != iProver_top
% 15.37/2.48      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_0,plain,
% 15.37/2.48      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 15.37/2.48      inference(cnf_transformation,[],[f54]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_13,negated_conjecture,
% 15.37/2.48      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
% 15.37/2.48      inference(cnf_transformation,[],[f59]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_511,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_688,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 15.37/2.48      inference(demodulation,[status(thm)],[c_0,c_511]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_1245,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 15.37/2.48      inference(demodulation,[status(thm)],[c_1233,c_688]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_2229,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) != iProver_top
% 15.37/2.48      | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
% 15.37/2.48      inference(superposition,[status(thm)],[c_518,c_1245]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_16,plain,
% 15.37/2.48      ( v1_relat_1(sK2) = iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_18,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_47,plain,
% 15.37/2.48      ( r1_tarski(sK2,sK2) ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_3]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_1,plain,
% 15.37/2.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.37/2.48      inference(cnf_transformation,[],[f36]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_51,plain,
% 15.37/2.48      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_1]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_621,plain,
% 15.37/2.48      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 15.37/2.48      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))
% 15.37/2.48      | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_5]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_622,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
% 15.37/2.48      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) = iProver_top
% 15.37/2.48      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_262,plain,( X0 = X0 ),theory(equality) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_757,plain,
% 15.37/2.48      ( sK1 = sK1 ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_262]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_268,plain,
% 15.37/2.48      ( X0 != X1 | X2 != X3 | k9_relat_1(X0,X2) = k9_relat_1(X1,X3) ),
% 15.37/2.48      theory(equality) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_662,plain,
% 15.37/2.48      ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(X0,X1)
% 15.37/2.48      | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != X1
% 15.37/2.48      | sK2 != X0 ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_268]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_779,plain,
% 15.37/2.48      ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 15.37/2.48      | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 15.37/2.48      | sK2 != X0 ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_662]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_781,plain,
% 15.37/2.48      ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 15.37/2.48      | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 15.37/2.48      | sK2 != sK2 ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_779]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_780,plain,
% 15.37/2.48      ( ~ v1_relat_1(sK2)
% 15.37/2.48      | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1))) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_11]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_690,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),X0)
% 15.37/2.48      | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_4]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_905,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 15.37/2.48      | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_690]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_907,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) = iProver_top
% 15.37/2.48      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) != iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_905]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_7,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k1_setfam_1(k2_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
% 15.37/2.48      | ~ v1_relat_1(X0) ),
% 15.37/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_906,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))))
% 15.37/2.48      | ~ v1_relat_1(sK2) ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_7]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_909,plain,
% 15.37/2.48      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) = iProver_top
% 15.37/2.48      | v1_relat_1(sK2) != iProver_top ),
% 15.37/2.48      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_266,plain,
% 15.37/2.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.37/2.48      theory(equality) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_712,plain,
% 15.37/2.48      ( ~ r1_tarski(X0,X1)
% 15.37/2.48      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),X2)
% 15.37/2.48      | X2 != X1
% 15.37/2.48      | k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != X0 ),
% 15.37/2.48      inference(instantiation,[status(thm)],[c_266]) ).
% 15.37/2.48  
% 15.37/2.48  cnf(c_1101,plain,
% 15.37/2.48      ( ~ r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),X1)
% 15.37/2.48      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),X2)
% 15.37/2.49      | X2 != X1
% 15.37/2.49      | k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_712]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_15417,plain,
% 15.37/2.49      ( ~ r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),X1)
% 15.37/2.49      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
% 15.37/2.49      | k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 15.37/2.49      | sK1 != X1 ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_1101]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_17393,plain,
% 15.37/2.49      ( ~ r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
% 15.37/2.49      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
% 15.37/2.49      | k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 15.37/2.49      | sK1 != sK1 ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_15417]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_17394,plain,
% 15.37/2.49      ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 15.37/2.49      | sK1 != sK1
% 15.37/2.49      | r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top
% 15.37/2.49      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_17393]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_17396,plain,
% 15.37/2.49      ( k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 15.37/2.49      | sK1 != sK1
% 15.37/2.49      | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top
% 15.37/2.49      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) = iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_17394]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_34043,plain,
% 15.37/2.49      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
% 15.37/2.49      inference(global_propositional_subsumption,
% 15.37/2.49                [status(thm)],
% 15.37/2.49                [c_2229,c_15,c_16,c_18,c_47,c_51,c_622,c_757,c_781,c_780,
% 15.37/2.49                 c_907,c_909,c_17396]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_34048,plain,
% 15.37/2.49      ( v1_funct_1(k7_relat_1(sK2,sK0)) != iProver_top
% 15.37/2.49      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_21681,c_34043]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_6,plain,
% 15.37/2.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 15.37/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_10561,plain,
% 15.37/2.49      ( v1_relat_1(k7_relat_1(sK2,sK0)) | ~ v1_relat_1(sK2) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_6]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_10562,plain,
% 15.37/2.49      ( v1_relat_1(k7_relat_1(sK2,sK0)) = iProver_top
% 15.37/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_10561]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_9,plain,
% 15.37/2.49      ( ~ v1_funct_1(X0)
% 15.37/2.49      | v1_funct_1(k7_relat_1(X0,X1))
% 15.37/2.49      | ~ v1_relat_1(X0) ),
% 15.37/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_3696,plain,
% 15.37/2.49      ( v1_funct_1(k7_relat_1(sK2,sK0))
% 15.37/2.49      | ~ v1_funct_1(sK2)
% 15.37/2.49      | ~ v1_relat_1(sK2) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_3697,plain,
% 15.37/2.49      ( v1_funct_1(k7_relat_1(sK2,sK0)) = iProver_top
% 15.37/2.49      | v1_funct_1(sK2) != iProver_top
% 15.37/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_3696]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_14,negated_conjecture,
% 15.37/2.49      ( v1_funct_1(sK2) ),
% 15.37/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_17,plain,
% 15.37/2.49      ( v1_funct_1(sK2) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(contradiction,plain,
% 15.37/2.49      ( $false ),
% 15.37/2.49      inference(minisat,[status(thm)],[c_34048,c_10562,c_3697,c_17,c_16]) ).
% 15.37/2.49  
% 15.37/2.49  
% 15.37/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.37/2.49  
% 15.37/2.49  ------                               Statistics
% 15.37/2.49  
% 15.37/2.49  ------ General
% 15.37/2.49  
% 15.37/2.49  abstr_ref_over_cycles:                  0
% 15.37/2.49  abstr_ref_under_cycles:                 0
% 15.37/2.49  gc_basic_clause_elim:                   0
% 15.37/2.49  forced_gc_time:                         0
% 15.37/2.49  parsing_time:                           0.008
% 15.37/2.49  unif_index_cands_time:                  0.
% 15.37/2.49  unif_index_add_time:                    0.
% 15.37/2.49  orderings_time:                         0.
% 15.37/2.49  out_proof_time:                         0.01
% 15.37/2.49  total_time:                             1.506
% 15.37/2.49  num_of_symbols:                         42
% 15.37/2.49  num_of_terms:                           41175
% 15.37/2.49  
% 15.37/2.49  ------ Preprocessing
% 15.37/2.49  
% 15.37/2.49  num_of_splits:                          0
% 15.37/2.49  num_of_split_atoms:                     0
% 15.37/2.49  num_of_reused_defs:                     0
% 15.37/2.49  num_eq_ax_congr_red:                    6
% 15.37/2.49  num_of_sem_filtered_clauses:            1
% 15.37/2.49  num_of_subtypes:                        0
% 15.37/2.49  monotx_restored_types:                  0
% 15.37/2.49  sat_num_of_epr_types:                   0
% 15.37/2.49  sat_num_of_non_cyclic_types:            0
% 15.37/2.49  sat_guarded_non_collapsed_types:        0
% 15.37/2.49  num_pure_diseq_elim:                    0
% 15.37/2.49  simp_replaced_by:                       0
% 15.37/2.49  res_preprocessed:                       75
% 15.37/2.49  prep_upred:                             0
% 15.37/2.49  prep_unflattend:                        0
% 15.37/2.49  smt_new_axioms:                         0
% 15.37/2.49  pred_elim_cands:                        3
% 15.37/2.49  pred_elim:                              0
% 15.37/2.49  pred_elim_cl:                           0
% 15.37/2.49  pred_elim_cycles:                       2
% 15.37/2.49  merged_defs:                            0
% 15.37/2.49  merged_defs_ncl:                        0
% 15.37/2.49  bin_hyper_res:                          0
% 15.37/2.49  prep_cycles:                            4
% 15.37/2.49  pred_elim_time:                         0.
% 15.37/2.49  splitting_time:                         0.
% 15.37/2.49  sem_filter_time:                        0.
% 15.37/2.49  monotx_time:                            0.
% 15.37/2.49  subtype_inf_time:                       0.
% 15.37/2.49  
% 15.37/2.49  ------ Problem properties
% 15.37/2.49  
% 15.37/2.49  clauses:                                14
% 15.37/2.49  conjectures:                            3
% 15.37/2.49  epr:                                    4
% 15.37/2.49  horn:                                   14
% 15.37/2.49  ground:                                 3
% 15.37/2.49  unary:                                  5
% 15.37/2.49  binary:                                 4
% 15.37/2.49  lits:                                   28
% 15.37/2.49  lits_eq:                                4
% 15.37/2.49  fd_pure:                                0
% 15.37/2.49  fd_pseudo:                              0
% 15.37/2.49  fd_cond:                                0
% 15.37/2.49  fd_pseudo_cond:                         1
% 15.37/2.49  ac_symbols:                             0
% 15.37/2.49  
% 15.37/2.49  ------ Propositional Solver
% 15.37/2.49  
% 15.37/2.49  prop_solver_calls:                      32
% 15.37/2.49  prop_fast_solver_calls:                 690
% 15.37/2.49  smt_solver_calls:                       0
% 15.37/2.49  smt_fast_solver_calls:                  0
% 15.37/2.49  prop_num_of_clauses:                    11759
% 15.37/2.49  prop_preprocess_simplified:             15844
% 15.37/2.49  prop_fo_subsumed:                       3
% 15.37/2.49  prop_solver_time:                       0.
% 15.37/2.49  smt_solver_time:                        0.
% 15.37/2.49  smt_fast_solver_time:                   0.
% 15.37/2.49  prop_fast_solver_time:                  0.
% 15.37/2.49  prop_unsat_core_time:                   0.001
% 15.37/2.49  
% 15.37/2.49  ------ QBF
% 15.37/2.49  
% 15.37/2.49  qbf_q_res:                              0
% 15.37/2.49  qbf_num_tautologies:                    0
% 15.37/2.49  qbf_prep_cycles:                        0
% 15.37/2.49  
% 15.37/2.49  ------ BMC1
% 15.37/2.49  
% 15.37/2.49  bmc1_current_bound:                     -1
% 15.37/2.49  bmc1_last_solved_bound:                 -1
% 15.37/2.49  bmc1_unsat_core_size:                   -1
% 15.37/2.49  bmc1_unsat_core_parents_size:           -1
% 15.37/2.49  bmc1_merge_next_fun:                    0
% 15.37/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.37/2.49  
% 15.37/2.49  ------ Instantiation
% 15.37/2.49  
% 15.37/2.49  inst_num_of_clauses:                    2260
% 15.37/2.49  inst_num_in_passive:                    769
% 15.37/2.49  inst_num_in_active:                     931
% 15.37/2.49  inst_num_in_unprocessed:                560
% 15.37/2.49  inst_num_of_loops:                      990
% 15.37/2.49  inst_num_of_learning_restarts:          0
% 15.37/2.49  inst_num_moves_active_passive:          56
% 15.37/2.49  inst_lit_activity:                      0
% 15.37/2.49  inst_lit_activity_moves:                1
% 15.37/2.49  inst_num_tautologies:                   0
% 15.37/2.49  inst_num_prop_implied:                  0
% 15.37/2.49  inst_num_existing_simplified:           0
% 15.37/2.49  inst_num_eq_res_simplified:             0
% 15.37/2.49  inst_num_child_elim:                    0
% 15.37/2.49  inst_num_of_dismatching_blockings:      5704
% 15.37/2.49  inst_num_of_non_proper_insts:           3608
% 15.37/2.49  inst_num_of_duplicates:                 0
% 15.37/2.49  inst_inst_num_from_inst_to_res:         0
% 15.37/2.49  inst_dismatching_checking_time:         0.
% 15.37/2.49  
% 15.37/2.49  ------ Resolution
% 15.37/2.49  
% 15.37/2.49  res_num_of_clauses:                     0
% 15.37/2.49  res_num_in_passive:                     0
% 15.37/2.49  res_num_in_active:                      0
% 15.37/2.49  res_num_of_loops:                       79
% 15.37/2.49  res_forward_subset_subsumed:            345
% 15.37/2.49  res_backward_subset_subsumed:           0
% 15.37/2.49  res_forward_subsumed:                   0
% 15.37/2.49  res_backward_subsumed:                  0
% 15.37/2.49  res_forward_subsumption_resolution:     0
% 15.37/2.49  res_backward_subsumption_resolution:    0
% 15.37/2.49  res_clause_to_clause_subsumption:       9759
% 15.37/2.49  res_orphan_elimination:                 0
% 15.37/2.49  res_tautology_del:                      122
% 15.37/2.49  res_num_eq_res_simplified:              0
% 15.37/2.49  res_num_sel_changes:                    0
% 15.37/2.49  res_moves_from_active_to_pass:          0
% 15.37/2.49  
% 15.37/2.49  ------ Superposition
% 15.37/2.49  
% 15.37/2.49  sup_time_total:                         0.
% 15.37/2.49  sup_time_generating:                    0.
% 15.37/2.49  sup_time_sim_full:                      0.
% 15.37/2.49  sup_time_sim_immed:                     0.
% 15.37/2.49  
% 15.37/2.49  sup_num_of_clauses:                     1412
% 15.37/2.49  sup_num_in_active:                      181
% 15.37/2.49  sup_num_in_passive:                     1231
% 15.37/2.49  sup_num_of_loops:                       197
% 15.37/2.49  sup_fw_superposition:                   1828
% 15.37/2.49  sup_bw_superposition:                   1618
% 15.37/2.49  sup_immediate_simplified:               318
% 15.37/2.49  sup_given_eliminated:                   0
% 15.37/2.49  comparisons_done:                       0
% 15.37/2.49  comparisons_avoided:                    0
% 15.37/2.49  
% 15.37/2.49  ------ Simplifications
% 15.37/2.49  
% 15.37/2.49  
% 15.37/2.49  sim_fw_subset_subsumed:                 1
% 15.37/2.49  sim_bw_subset_subsumed:                 0
% 15.37/2.49  sim_fw_subsumed:                        115
% 15.37/2.49  sim_bw_subsumed:                        7
% 15.37/2.49  sim_fw_subsumption_res:                 0
% 15.37/2.49  sim_bw_subsumption_res:                 0
% 15.37/2.49  sim_tautology_del:                      6
% 15.37/2.49  sim_eq_tautology_del:                   2
% 15.37/2.49  sim_eq_res_simp:                        0
% 15.37/2.49  sim_fw_demodulated:                     174
% 15.37/2.49  sim_bw_demodulated:                     20
% 15.37/2.49  sim_light_normalised:                   30
% 15.37/2.49  sim_joinable_taut:                      0
% 15.37/2.49  sim_joinable_simp:                      0
% 15.37/2.49  sim_ac_normalised:                      0
% 15.37/2.49  sim_smt_subsumption:                    0
% 15.37/2.49  
%------------------------------------------------------------------------------
