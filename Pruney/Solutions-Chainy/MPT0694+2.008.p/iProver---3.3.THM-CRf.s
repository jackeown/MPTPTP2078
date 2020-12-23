%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:57 EST 2020

% Result     : Theorem 51.67s
% Output     : CNFRefutation 51.67s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 352 expanded)
%              Number of clauses        :   38 (  47 expanded)
%              Number of leaves         :   19 ( 106 expanded)
%              Depth                    :   21
%              Number of atoms          :  179 ( 525 expanded)
%              Number of equality atoms :   55 ( 271 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f54,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f50,f50])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f51])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f27])).

fof(f45,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k6_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f45,f51,f51])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_92,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_90,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1042,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_92,c_90])).

cnf(c_94,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_1177,plain,
    ( ~ r1_tarski(k1_setfam_1(X0),X1)
    | r1_tarski(k1_setfam_1(X2),X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1042,c_94])).

cnf(c_2290,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)
    | r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X2) ),
    inference(resolution,[status(thm)],[c_4,c_1177])).

cnf(c_2,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_121298,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) ),
    inference(resolution,[status(thm)],[c_2290,c_2])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k6_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2525,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(resolution,[status(thm)],[c_7,c_3])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_268,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_269,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_266,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k6_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_701,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4,c_266])).

cnf(c_1154,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_269,c_701])).

cnf(c_1301,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_268,c_1154])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1304,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1301,c_10])).

cnf(c_1305,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1304])).

cnf(c_270,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1310,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1305,c_270])).

cnf(c_1311,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1310])).

cnf(c_2528,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2525,c_1311])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1172,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_1042,c_1])).

cnf(c_1317,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_0,c_1172])).

cnf(c_1329,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k9_relat_1(X2,X1),X3)
    | r1_tarski(k9_relat_1(X2,X0),X3)
    | ~ v1_relat_1(X2) ),
    inference(resolution,[status(thm)],[c_1317,c_5])).

cnf(c_6,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14220,plain,
    ( ~ r1_tarski(X0,k10_relat_1(X1,X2))
    | r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_1329,c_6])).

cnf(c_15389,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_2528,c_14220])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15885,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15389,c_9,c_8])).

cnf(c_121365,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_121298,c_15885])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n023.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 19:12:05 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 51.67/6.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.67/6.98  
% 51.67/6.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.67/6.98  
% 51.67/6.98  ------  iProver source info
% 51.67/6.98  
% 51.67/6.98  git: date: 2020-06-30 10:37:57 +0100
% 51.67/6.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.67/6.98  git: non_committed_changes: false
% 51.67/6.98  git: last_make_outside_of_git: false
% 51.67/6.98  
% 51.67/6.98  ------ 
% 51.67/6.98  ------ Parsing...
% 51.67/6.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.67/6.98  
% 51.67/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 51.67/6.98  
% 51.67/6.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.67/6.98  
% 51.67/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.67/6.98  ------ Proving...
% 51.67/6.98  ------ Problem Properties 
% 51.67/6.98  
% 51.67/6.98  
% 51.67/6.98  clauses                                 10
% 51.67/6.98  conjectures                             3
% 51.67/6.98  EPR                                     2
% 51.67/6.98  Horn                                    10
% 51.67/6.98  unary                                   5
% 51.67/6.98  binary                                  2
% 51.67/6.98  lits                                    18
% 51.67/6.98  lits eq                                 2
% 51.67/6.98  fd_pure                                 0
% 51.67/6.98  fd_pseudo                               0
% 51.67/6.98  fd_cond                                 0
% 51.67/6.98  fd_pseudo_cond                          0
% 51.67/6.98  AC symbols                              0
% 51.67/6.98  
% 51.67/6.98  ------ Input Options Time Limit: Unbounded
% 51.67/6.98  
% 51.67/6.98  
% 51.67/6.98  ------ 
% 51.67/6.98  Current options:
% 51.67/6.98  ------ 
% 51.67/6.98  
% 51.67/6.98  
% 51.67/6.98  
% 51.67/6.98  
% 51.67/6.98  ------ Proving...
% 51.67/6.98  
% 51.67/6.98  
% 51.67/6.98  % SZS status Theorem for theBenchmark.p
% 51.67/6.98  
% 51.67/6.98   Resolution empty clause
% 51.67/6.98  
% 51.67/6.98  % SZS output start CNFRefutation for theBenchmark.p
% 51.67/6.98  
% 51.67/6.98  fof(f5,axiom,(
% 51.67/6.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f33,plain,(
% 51.67/6.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f5])).
% 51.67/6.98  
% 51.67/6.98  fof(f6,axiom,(
% 51.67/6.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f34,plain,(
% 51.67/6.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f6])).
% 51.67/6.98  
% 51.67/6.98  fof(f7,axiom,(
% 51.67/6.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f35,plain,(
% 51.67/6.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f7])).
% 51.67/6.98  
% 51.67/6.98  fof(f8,axiom,(
% 51.67/6.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f36,plain,(
% 51.67/6.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f8])).
% 51.67/6.98  
% 51.67/6.98  fof(f9,axiom,(
% 51.67/6.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f37,plain,(
% 51.67/6.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f9])).
% 51.67/6.98  
% 51.67/6.98  fof(f10,axiom,(
% 51.67/6.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f38,plain,(
% 51.67/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f10])).
% 51.67/6.98  
% 51.67/6.98  fof(f11,axiom,(
% 51.67/6.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f39,plain,(
% 51.67/6.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f11])).
% 51.67/6.98  
% 51.67/6.98  fof(f46,plain,(
% 51.67/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 51.67/6.98    inference(definition_unfolding,[],[f38,f39])).
% 51.67/6.98  
% 51.67/6.98  fof(f47,plain,(
% 51.67/6.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 51.67/6.98    inference(definition_unfolding,[],[f37,f46])).
% 51.67/6.98  
% 51.67/6.98  fof(f48,plain,(
% 51.67/6.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 51.67/6.98    inference(definition_unfolding,[],[f36,f47])).
% 51.67/6.98  
% 51.67/6.98  fof(f49,plain,(
% 51.67/6.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 51.67/6.98    inference(definition_unfolding,[],[f35,f48])).
% 51.67/6.98  
% 51.67/6.98  fof(f50,plain,(
% 51.67/6.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 51.67/6.98    inference(definition_unfolding,[],[f34,f49])).
% 51.67/6.98  
% 51.67/6.98  fof(f54,plain,(
% 51.67/6.98    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 51.67/6.98    inference(definition_unfolding,[],[f33,f50,f50])).
% 51.67/6.98  
% 51.67/6.98  fof(f3,axiom,(
% 51.67/6.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f31,plain,(
% 51.67/6.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f3])).
% 51.67/6.98  
% 51.67/6.98  fof(f12,axiom,(
% 51.67/6.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f40,plain,(
% 51.67/6.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 51.67/6.98    inference(cnf_transformation,[],[f12])).
% 51.67/6.98  
% 51.67/6.98  fof(f51,plain,(
% 51.67/6.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 51.67/6.98    inference(definition_unfolding,[],[f40,f50])).
% 51.67/6.98  
% 51.67/6.98  fof(f52,plain,(
% 51.67/6.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 51.67/6.98    inference(definition_unfolding,[],[f31,f51])).
% 51.67/6.98  
% 51.67/6.98  fof(f15,conjecture,(
% 51.67/6.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f16,negated_conjecture,(
% 51.67/6.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 51.67/6.98    inference(negated_conjecture,[],[f15])).
% 51.67/6.98  
% 51.67/6.98  fof(f25,plain,(
% 51.67/6.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 51.67/6.98    inference(ennf_transformation,[],[f16])).
% 51.67/6.98  
% 51.67/6.98  fof(f26,plain,(
% 51.67/6.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 51.67/6.98    inference(flattening,[],[f25])).
% 51.67/6.98  
% 51.67/6.98  fof(f27,plain,(
% 51.67/6.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 51.67/6.98    introduced(choice_axiom,[])).
% 51.67/6.98  
% 51.67/6.98  fof(f28,plain,(
% 51.67/6.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 51.67/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f27])).
% 51.67/6.98  
% 51.67/6.98  fof(f45,plain,(
% 51.67/6.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 51.67/6.98    inference(cnf_transformation,[],[f28])).
% 51.67/6.98  
% 51.67/6.98  fof(f55,plain,(
% 51.67/6.98    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k6_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 51.67/6.98    inference(definition_unfolding,[],[f45,f51,f51])).
% 51.67/6.98  
% 51.67/6.98  fof(f4,axiom,(
% 51.67/6.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f19,plain,(
% 51.67/6.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 51.67/6.98    inference(ennf_transformation,[],[f4])).
% 51.67/6.98  
% 51.67/6.98  fof(f20,plain,(
% 51.67/6.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 51.67/6.98    inference(flattening,[],[f19])).
% 51.67/6.98  
% 51.67/6.98  fof(f32,plain,(
% 51.67/6.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f20])).
% 51.67/6.98  
% 51.67/6.98  fof(f53,plain,(
% 51.67/6.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 51.67/6.98    inference(definition_unfolding,[],[f32,f51])).
% 51.67/6.98  
% 51.67/6.98  fof(f13,axiom,(
% 51.67/6.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f21,plain,(
% 51.67/6.98    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 51.67/6.98    inference(ennf_transformation,[],[f13])).
% 51.67/6.98  
% 51.67/6.98  fof(f22,plain,(
% 51.67/6.98    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 51.67/6.98    inference(flattening,[],[f21])).
% 51.67/6.98  
% 51.67/6.98  fof(f41,plain,(
% 51.67/6.98    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f22])).
% 51.67/6.98  
% 51.67/6.98  fof(f43,plain,(
% 51.67/6.98    v1_relat_1(sK2)),
% 51.67/6.98    inference(cnf_transformation,[],[f28])).
% 51.67/6.98  
% 51.67/6.98  fof(f1,axiom,(
% 51.67/6.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f17,plain,(
% 51.67/6.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 51.67/6.98    inference(ennf_transformation,[],[f1])).
% 51.67/6.98  
% 51.67/6.98  fof(f29,plain,(
% 51.67/6.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f17])).
% 51.67/6.98  
% 51.67/6.98  fof(f2,axiom,(
% 51.67/6.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f18,plain,(
% 51.67/6.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 51.67/6.98    inference(ennf_transformation,[],[f2])).
% 51.67/6.98  
% 51.67/6.98  fof(f30,plain,(
% 51.67/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f18])).
% 51.67/6.98  
% 51.67/6.98  fof(f14,axiom,(
% 51.67/6.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 51.67/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.67/6.98  
% 51.67/6.98  fof(f23,plain,(
% 51.67/6.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 51.67/6.98    inference(ennf_transformation,[],[f14])).
% 51.67/6.98  
% 51.67/6.98  fof(f24,plain,(
% 51.67/6.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 51.67/6.98    inference(flattening,[],[f23])).
% 51.67/6.98  
% 51.67/6.98  fof(f42,plain,(
% 51.67/6.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 51.67/6.98    inference(cnf_transformation,[],[f24])).
% 51.67/6.98  
% 51.67/6.98  fof(f44,plain,(
% 51.67/6.98    v1_funct_1(sK2)),
% 51.67/6.98    inference(cnf_transformation,[],[f28])).
% 51.67/6.98  
% 51.67/6.98  cnf(c_4,plain,
% 51.67/6.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 51.67/6.98      inference(cnf_transformation,[],[f54]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_92,plain,
% 51.67/6.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.67/6.98      theory(equality) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_90,plain,( X0 = X0 ),theory(equality) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1042,plain,
% 51.67/6.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_92,c_90]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_94,plain,
% 51.67/6.98      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 51.67/6.98      theory(equality) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1177,plain,
% 51.67/6.98      ( ~ r1_tarski(k1_setfam_1(X0),X1)
% 51.67/6.98      | r1_tarski(k1_setfam_1(X2),X1)
% 51.67/6.98      | X2 != X0 ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_1042,c_94]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_2290,plain,
% 51.67/6.98      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)
% 51.67/6.98      | r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X2) ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_4,c_1177]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_2,plain,
% 51.67/6.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 51.67/6.98      inference(cnf_transformation,[],[f52]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_121298,plain,
% 51.67/6.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_2290,c_2]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_7,negated_conjecture,
% 51.67/6.98      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k6_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
% 51.67/6.98      inference(cnf_transformation,[],[f55]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_3,plain,
% 51.67/6.98      ( ~ r1_tarski(X0,X1)
% 51.67/6.98      | ~ r1_tarski(X0,X2)
% 51.67/6.98      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 51.67/6.98      inference(cnf_transformation,[],[f53]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_2525,plain,
% 51.67/6.98      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 51.67/6.98      | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_7,c_3]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_5,plain,
% 51.67/6.98      ( ~ r1_tarski(X0,X1)
% 51.67/6.98      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 51.67/6.98      | ~ v1_relat_1(X2) ),
% 51.67/6.98      inference(cnf_transformation,[],[f41]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_268,plain,
% 51.67/6.98      ( r1_tarski(X0,X1) != iProver_top
% 51.67/6.98      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 51.67/6.98      | v1_relat_1(X2) != iProver_top ),
% 51.67/6.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_269,plain,
% 51.67/6.98      ( r1_tarski(X0,X1) != iProver_top
% 51.67/6.98      | r1_tarski(X0,X2) != iProver_top
% 51.67/6.98      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 51.67/6.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_266,plain,
% 51.67/6.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k6_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
% 51.67/6.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_701,plain,
% 51.67/6.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 51.67/6.98      inference(demodulation,[status(thm)],[c_4,c_266]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1154,plain,
% 51.67/6.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
% 51.67/6.98      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 51.67/6.98      inference(superposition,[status(thm)],[c_269,c_701]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1301,plain,
% 51.67/6.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
% 51.67/6.98      | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top
% 51.67/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.67/6.98      inference(superposition,[status(thm)],[c_268,c_1154]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_9,negated_conjecture,
% 51.67/6.98      ( v1_relat_1(sK2) ),
% 51.67/6.98      inference(cnf_transformation,[],[f43]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_10,plain,
% 51.67/6.98      ( v1_relat_1(sK2) = iProver_top ),
% 51.67/6.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1304,plain,
% 51.67/6.98      ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top
% 51.67/6.98      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 51.67/6.98      inference(global_propositional_subsumption,[status(thm)],[c_1301,c_10]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1305,plain,
% 51.67/6.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
% 51.67/6.98      | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top ),
% 51.67/6.98      inference(renaming,[status(thm)],[c_1304]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_270,plain,
% 51.67/6.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 51.67/6.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1310,plain,
% 51.67/6.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 51.67/6.98      inference(forward_subsumption_resolution,[status(thm)],[c_1305,c_270]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1311,plain,
% 51.67/6.98      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 51.67/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_1310]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_2528,plain,
% 51.67/6.98      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 51.67/6.98      inference(global_propositional_subsumption,[status(thm)],[c_2525,c_1311]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_0,plain,
% 51.67/6.98      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 51.67/6.98      inference(cnf_transformation,[],[f29]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1,plain,
% 51.67/6.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 51.67/6.98      inference(cnf_transformation,[],[f30]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1172,plain,
% 51.67/6.98      ( ~ r1_tarski(X0,X1)
% 51.67/6.98      | ~ r1_tarski(X2,X0)
% 51.67/6.98      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_1042,c_1]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1317,plain,
% 51.67/6.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_0,c_1172]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_1329,plain,
% 51.67/6.98      ( ~ r1_tarski(X0,X1)
% 51.67/6.98      | ~ r1_tarski(k9_relat_1(X2,X1),X3)
% 51.67/6.98      | r1_tarski(k9_relat_1(X2,X0),X3)
% 51.67/6.98      | ~ v1_relat_1(X2) ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_1317,c_5]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_6,plain,
% 51.67/6.98      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 51.67/6.98      | ~ v1_funct_1(X0)
% 51.67/6.98      | ~ v1_relat_1(X0) ),
% 51.67/6.98      inference(cnf_transformation,[],[f42]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_14220,plain,
% 51.67/6.98      ( ~ r1_tarski(X0,k10_relat_1(X1,X2))
% 51.67/6.98      | r1_tarski(k9_relat_1(X1,X0),X2)
% 51.67/6.98      | ~ v1_funct_1(X1)
% 51.67/6.98      | ~ v1_relat_1(X1) ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_1329,c_6]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_15389,plain,
% 51.67/6.98      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
% 51.67/6.98      | ~ v1_funct_1(sK2)
% 51.67/6.98      | ~ v1_relat_1(sK2) ),
% 51.67/6.98      inference(resolution,[status(thm)],[c_2528,c_14220]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_8,negated_conjecture,
% 51.67/6.98      ( v1_funct_1(sK2) ),
% 51.67/6.98      inference(cnf_transformation,[],[f44]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_15885,plain,
% 51.67/6.98      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
% 51.67/6.98      inference(global_propositional_subsumption,
% 51.67/6.98                [status(thm)],
% 51.67/6.98                [c_15389,c_9,c_8]) ).
% 51.67/6.98  
% 51.67/6.98  cnf(c_121365,plain,
% 51.67/6.98      ( $false ),
% 51.67/6.98      inference(backward_subsumption_resolution,
% 51.67/6.98                [status(thm)],
% 51.67/6.98                [c_121298,c_15885]) ).
% 51.67/6.98  
% 51.67/6.98  
% 51.67/6.98  % SZS output end CNFRefutation for theBenchmark.p
% 51.67/6.98  
% 51.67/6.98  ------                               Statistics
% 51.67/6.98  
% 51.67/6.98  ------ Selected
% 51.67/6.98  
% 51.67/6.98  total_time:                             6.292
% 51.67/6.98  
%------------------------------------------------------------------------------
