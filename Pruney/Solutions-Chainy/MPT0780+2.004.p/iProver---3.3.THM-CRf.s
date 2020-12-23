%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:22 EST 2020

% Result     : Theorem 51.34s
% Output     : CNFRefutation 51.34s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 953 expanded)
%              Number of clauses        :  113 ( 385 expanded)
%              Number of leaves         :   20 ( 190 expanded)
%              Depth                    :   21
%              Number of atoms          :  358 (1954 expanded)
%              Number of equality atoms :  204 ( 898 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f31])).

fof(f48,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f54,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_293,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_124251,plain,
    ( X0_43 != X1_43
    | k2_wellord1(sK2,sK0) != X1_43
    | k2_wellord1(sK2,sK0) = X0_43 ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_124262,plain,
    ( X0_43 != k2_wellord1(sK2,sK0)
    | k2_wellord1(sK2,sK0) = X0_43
    | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_124251])).

cnf(c_124592,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),X0_42)
    | k7_relat_1(k2_wellord1(sK2,sK0),X0_42) != k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_124262])).

cnf(c_174580,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | k7_relat_1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_124592])).

cnf(c_124933,plain,
    ( X0_43 != k7_relat_1(k2_wellord1(sK2,sK0),X0_42)
    | k2_wellord1(sK2,sK0) = X0_43
    | k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42) ),
    inference(instantiation,[status(thm)],[c_124251])).

cnf(c_125421,plain,
    ( k2_wellord1(sK2,sK0) = k7_relat_1(X0_43,X0_42)
    | k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42)
    | k7_relat_1(X0_43,X0_42) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42) ),
    inference(instantiation,[status(thm)],[c_124933])).

cnf(c_144462,plain,
    ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42)
    | k2_wellord1(sK2,sK0) = k7_relat_1(k8_relat_1(X1_42,k2_wellord1(sK2,sK0)),X0_42)
    | k7_relat_1(k8_relat_1(X1_42,k2_wellord1(sK2,sK0)),X0_42) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42) ),
    inference(instantiation,[status(thm)],[c_125421])).

cnf(c_151927,plain,
    ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | k2_wellord1(sK2,sK0) = k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1)
    | k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_144462])).

cnf(c_300,plain,
    ( X0_43 != X1_43
    | k7_relat_1(X0_43,X0_42) = k7_relat_1(X1_43,X0_42) ),
    theory(equality)).

cnf(c_4344,plain,
    ( k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k7_relat_1(X1_43,X0_42)
    | k8_relat_1(X0_42,X0_43) != X1_43 ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_83730,plain,
    ( k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | k8_relat_1(sK1,k2_wellord1(sK2,sK0)) != k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_4344])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_275,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_534,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_284,plain,
    ( ~ v1_relat_1(X0_43)
    | k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_526,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_843,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_534,c_526])).

cnf(c_2,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_285,plain,
    ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_286,plain,
    ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X0_42,X0_42,X1_42))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_525,plain,
    ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X0_42,X0_42,X1_42))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_659,plain,
    ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X1_42,X1_42,X0_42))) = iProver_top ),
    inference(superposition,[status(thm)],[c_285,c_525])).

cnf(c_999,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_843,c_659])).

cnf(c_6,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_283,plain,
    ( ~ r1_tarski(k2_relat_1(X0_43),X0_42)
    | ~ v1_relat_1(X0_43)
    | k8_relat_1(X0_42,X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_527,plain,
    ( k8_relat_1(X0_42,X0_43) = X0_43
    | r1_tarski(k2_relat_1(X0_43),X0_42) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_1212,plain,
    ( k8_relat_1(k3_relat_1(sK2),sK2) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_527])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1296,plain,
    ( k8_relat_1(k3_relat_1(sK2),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1212,c_16])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_281,plain,
    ( ~ v1_relat_1(X0_43)
    | k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k2_wellord1(X0_43,X0_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_529,plain,
    ( k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k2_wellord1(X0_43,X0_42)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_771,plain,
    ( k7_relat_1(k8_relat_1(X0_42,sK2),X0_42) = k2_wellord1(sK2,X0_42) ),
    inference(superposition,[status(thm)],[c_534,c_529])).

cnf(c_1298,plain,
    ( k2_wellord1(sK2,k3_relat_1(sK2)) = k7_relat_1(sK2,k3_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1296,c_771])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_278,plain,
    ( ~ v1_relat_1(X0_43)
    | k2_wellord1(k2_wellord1(X0_43,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_532,plain,
    ( k2_wellord1(k2_wellord1(X0_43,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_913,plain,
    ( k2_wellord1(k2_wellord1(sK2,X0_42),X1_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_534,c_532])).

cnf(c_1485,plain,
    ( k2_wellord1(k7_relat_1(sK2,k3_relat_1(sK2)),X0_42) = k2_wellord1(k2_wellord1(sK2,X0_42),k3_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1298,c_913])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_282,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k2_wellord1(X0_43,X0_42)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_528,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_wellord1(X0_43,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_1494,plain,
    ( v1_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),k3_relat_1(sK2))) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,k3_relat_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_528])).

cnf(c_1484,plain,
    ( v1_relat_1(k7_relat_1(sK2,k3_relat_1(sK2))) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_528])).

cnf(c_4036,plain,
    ( v1_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),k3_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1494,c_16,c_1484])).

cnf(c_998,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_843,c_525])).

cnf(c_3,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_167,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_274,plain,
    ( ~ r1_tarski(k1_relat_1(X0_43),X0_42)
    | ~ v1_relat_1(X0_43)
    | k7_relat_1(X0_43,X0_42) = X0_43 ),
    inference(subtyping,[status(esa)],[c_167])).

cnf(c_535,plain,
    ( k7_relat_1(X0_43,X0_42) = X0_43
    | r1_tarski(k1_relat_1(X0_43),X0_42) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_2092,plain,
    ( k7_relat_1(sK2,k3_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_535])).

cnf(c_2910,plain,
    ( k7_relat_1(sK2,k3_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2092,c_16])).

cnf(c_2915,plain,
    ( k2_wellord1(k2_wellord1(sK2,X0_42),k3_relat_1(sK2)) = k2_wellord1(sK2,X0_42) ),
    inference(demodulation,[status(thm)],[c_2910,c_1485])).

cnf(c_4042,plain,
    ( v1_relat_1(k2_wellord1(sK2,X0_42)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4036,c_2915])).

cnf(c_4053,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k2_relat_1(k2_wellord1(sK2,X0_42)))) = k3_relat_1(k2_wellord1(sK2,X0_42)) ),
    inference(superposition,[status(thm)],[c_4042,c_526])).

cnf(c_33407,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_659])).

cnf(c_33425,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33407])).

cnf(c_33406,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_525])).

cnf(c_33422,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33406])).

cnf(c_629,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),X0_42)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k8_relat_1(X0_42,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_4843,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_4846,plain,
    ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
    | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) != iProver_top
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4843])).

cnf(c_623,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),X0_42)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k7_relat_1(k2_wellord1(sK2,sK0),X0_42) = k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_4832,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_4835,plain,
    ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0)
    | r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) != iProver_top
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4832])).

cnf(c_571,plain,
    ( k2_wellord1(X0_43,X0_42) != X1_43
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X1_43
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(X0_43,X0_42) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_3272,plain,
    ( k2_wellord1(X0_43,X0_42) != k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,X1_42)),sK1)
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(X0_43,X0_42)
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,X1_42)),sK1) ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_3273,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(sK2,sK0)
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1)
    | k2_wellord1(sK2,sK0) != k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) ),
    inference(instantiation,[status(thm)],[c_3272])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_287,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X2_42,X0_42)
    | r1_tarski(X2_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1092,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(k2_relat_1(k2_wellord1(X0_43,X2_42)),X0_42)
    | r1_tarski(k2_relat_1(k2_wellord1(X0_43,X2_42)),X1_42) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_1707,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
    | r1_tarski(k2_relat_1(k2_wellord1(X1_43,X1_42)),X0_42)
    | ~ r1_tarski(k2_relat_1(k2_wellord1(X1_43,X1_42)),k3_relat_1(k2_wellord1(X0_43,X0_42))) ),
    inference(instantiation,[status(thm)],[c_1092])).

cnf(c_1708,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(X1_43,X1_42)),X0_42) = iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(X1_43,X1_42)),k3_relat_1(k2_wellord1(X0_43,X0_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1707])).

cnf(c_1710,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_1697,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(X0_43,X0_42)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_wellord1(X0_43,X0_42)),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1092])).

cnf(c_1698,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(X0_43,X0_42)),sK1) = iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(X0_43,X0_42)),sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1697])).

cnf(c_1700,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_1078,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(k1_relat_1(k2_wellord1(X0_43,X2_42)),X0_42)
    | r1_tarski(k1_relat_1(k2_wellord1(X0_43,X2_42)),X1_42) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_1683,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
    | r1_tarski(k1_relat_1(k2_wellord1(X1_43,X1_42)),X0_42)
    | ~ r1_tarski(k1_relat_1(k2_wellord1(X1_43,X1_42)),k3_relat_1(k2_wellord1(X0_43,X0_42))) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1684,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42) != iProver_top
    | r1_tarski(k1_relat_1(k2_wellord1(X1_43,X1_42)),X0_42) = iProver_top
    | r1_tarski(k1_relat_1(k2_wellord1(X1_43,X1_42)),k3_relat_1(k2_wellord1(X0_43,X0_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1683])).

cnf(c_1686,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
    | r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_1673,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK1)
    | ~ r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1674,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK1) = iProver_top
    | r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1673])).

cnf(c_1676,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top
    | r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_1405,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_610,plain,
    ( X0_43 != X1_43
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X1_43
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = X0_43 ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_673,plain,
    ( X0_43 != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = X0_43
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_977,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1)
    | k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_665,plain,
    ( ~ v1_relat_1(sK2)
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_550,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X0_43
    | k2_wellord1(sK2,sK0) != X0_43
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_555,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(sK2,sK0)
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_13,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_277,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_10,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_280,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_328,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_330,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_322,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_wellord1(X0_43,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_324,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_323,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_290,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_311,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_289,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_310,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_289])).

cnf(c_301,plain,
    ( X0_43 != X1_43
    | k2_wellord1(X0_43,X0_42) = k2_wellord1(X1_43,X1_42)
    | X0_42 != X1_42 ),
    theory(equality)).

cnf(c_308,plain,
    ( k2_wellord1(sK2,sK0) = k2_wellord1(sK2,sK0)
    | sK2 != sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_174580,c_151927,c_83730,c_33425,c_33422,c_4846,c_4835,c_3273,c_1710,c_1700,c_1686,c_1676,c_1405,c_977,c_665,c_555,c_277,c_330,c_324,c_323,c_311,c_310,c_308,c_17,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:36:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 51.34/6.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.34/6.98  
% 51.34/6.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.34/6.98  
% 51.34/6.98  ------  iProver source info
% 51.34/6.98  
% 51.34/6.98  git: date: 2020-06-30 10:37:57 +0100
% 51.34/6.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.34/6.98  git: non_committed_changes: false
% 51.34/6.98  git: last_make_outside_of_git: false
% 51.34/6.98  
% 51.34/6.98  ------ 
% 51.34/6.98  
% 51.34/6.98  ------ Input Options
% 51.34/6.98  
% 51.34/6.98  --out_options                           all
% 51.34/6.98  --tptp_safe_out                         true
% 51.34/6.98  --problem_path                          ""
% 51.34/6.98  --include_path                          ""
% 51.34/6.98  --clausifier                            res/vclausify_rel
% 51.34/6.98  --clausifier_options                    ""
% 51.34/6.98  --stdin                                 false
% 51.34/6.98  --stats_out                             all
% 51.34/6.98  
% 51.34/6.98  ------ General Options
% 51.34/6.98  
% 51.34/6.98  --fof                                   false
% 51.34/6.98  --time_out_real                         305.
% 51.34/6.98  --time_out_virtual                      -1.
% 51.34/6.98  --symbol_type_check                     false
% 51.34/6.98  --clausify_out                          false
% 51.34/6.98  --sig_cnt_out                           false
% 51.34/6.98  --trig_cnt_out                          false
% 51.34/6.98  --trig_cnt_out_tolerance                1.
% 51.34/6.98  --trig_cnt_out_sk_spl                   false
% 51.34/6.98  --abstr_cl_out                          false
% 51.34/6.98  
% 51.34/6.98  ------ Global Options
% 51.34/6.98  
% 51.34/6.98  --schedule                              default
% 51.34/6.98  --add_important_lit                     false
% 51.34/6.98  --prop_solver_per_cl                    1000
% 51.34/6.98  --min_unsat_core                        false
% 51.34/6.98  --soft_assumptions                      false
% 51.34/6.98  --soft_lemma_size                       3
% 51.34/6.98  --prop_impl_unit_size                   0
% 51.34/6.98  --prop_impl_unit                        []
% 51.34/6.98  --share_sel_clauses                     true
% 51.34/6.98  --reset_solvers                         false
% 51.34/6.98  --bc_imp_inh                            [conj_cone]
% 51.34/6.98  --conj_cone_tolerance                   3.
% 51.34/6.98  --extra_neg_conj                        none
% 51.34/6.98  --large_theory_mode                     true
% 51.34/6.98  --prolific_symb_bound                   200
% 51.34/6.98  --lt_threshold                          2000
% 51.34/6.98  --clause_weak_htbl                      true
% 51.34/6.98  --gc_record_bc_elim                     false
% 51.34/6.98  
% 51.34/6.98  ------ Preprocessing Options
% 51.34/6.98  
% 51.34/6.98  --preprocessing_flag                    true
% 51.34/6.98  --time_out_prep_mult                    0.1
% 51.34/6.98  --splitting_mode                        input
% 51.34/6.98  --splitting_grd                         true
% 51.34/6.98  --splitting_cvd                         false
% 51.34/6.98  --splitting_cvd_svl                     false
% 51.34/6.98  --splitting_nvd                         32
% 51.34/6.98  --sub_typing                            true
% 51.34/6.98  --prep_gs_sim                           true
% 51.34/6.98  --prep_unflatten                        true
% 51.34/6.98  --prep_res_sim                          true
% 51.34/6.98  --prep_upred                            true
% 51.34/6.98  --prep_sem_filter                       exhaustive
% 51.34/6.98  --prep_sem_filter_out                   false
% 51.34/6.98  --pred_elim                             true
% 51.34/6.98  --res_sim_input                         true
% 51.34/6.98  --eq_ax_congr_red                       true
% 51.34/6.98  --pure_diseq_elim                       true
% 51.34/6.98  --brand_transform                       false
% 51.34/6.98  --non_eq_to_eq                          false
% 51.34/6.98  --prep_def_merge                        true
% 51.34/6.98  --prep_def_merge_prop_impl              false
% 51.34/6.98  --prep_def_merge_mbd                    true
% 51.34/6.98  --prep_def_merge_tr_red                 false
% 51.34/6.98  --prep_def_merge_tr_cl                  false
% 51.34/6.98  --smt_preprocessing                     true
% 51.34/6.98  --smt_ac_axioms                         fast
% 51.34/6.98  --preprocessed_out                      false
% 51.34/6.98  --preprocessed_stats                    false
% 51.34/6.98  
% 51.34/6.98  ------ Abstraction refinement Options
% 51.34/6.98  
% 51.34/6.98  --abstr_ref                             []
% 51.34/6.98  --abstr_ref_prep                        false
% 51.34/6.98  --abstr_ref_until_sat                   false
% 51.34/6.98  --abstr_ref_sig_restrict                funpre
% 51.34/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 51.34/6.98  --abstr_ref_under                       []
% 51.34/6.98  
% 51.34/6.98  ------ SAT Options
% 51.34/6.98  
% 51.34/6.98  --sat_mode                              false
% 51.34/6.98  --sat_fm_restart_options                ""
% 51.34/6.98  --sat_gr_def                            false
% 51.34/6.98  --sat_epr_types                         true
% 51.34/6.98  --sat_non_cyclic_types                  false
% 51.34/6.98  --sat_finite_models                     false
% 51.34/6.98  --sat_fm_lemmas                         false
% 51.34/6.98  --sat_fm_prep                           false
% 51.34/6.98  --sat_fm_uc_incr                        true
% 51.34/6.98  --sat_out_model                         small
% 51.34/6.98  --sat_out_clauses                       false
% 51.34/6.98  
% 51.34/6.98  ------ QBF Options
% 51.34/6.98  
% 51.34/6.98  --qbf_mode                              false
% 51.34/6.98  --qbf_elim_univ                         false
% 51.34/6.98  --qbf_dom_inst                          none
% 51.34/6.98  --qbf_dom_pre_inst                      false
% 51.34/6.98  --qbf_sk_in                             false
% 51.34/6.98  --qbf_pred_elim                         true
% 51.34/6.98  --qbf_split                             512
% 51.34/6.98  
% 51.34/6.98  ------ BMC1 Options
% 51.34/6.98  
% 51.34/6.98  --bmc1_incremental                      false
% 51.34/6.98  --bmc1_axioms                           reachable_all
% 51.34/6.98  --bmc1_min_bound                        0
% 51.34/6.98  --bmc1_max_bound                        -1
% 51.34/6.98  --bmc1_max_bound_default                -1
% 51.34/6.98  --bmc1_symbol_reachability              true
% 51.34/6.98  --bmc1_property_lemmas                  false
% 51.34/6.98  --bmc1_k_induction                      false
% 51.34/6.98  --bmc1_non_equiv_states                 false
% 51.34/6.98  --bmc1_deadlock                         false
% 51.34/6.98  --bmc1_ucm                              false
% 51.34/6.98  --bmc1_add_unsat_core                   none
% 51.34/6.98  --bmc1_unsat_core_children              false
% 51.34/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 51.34/6.98  --bmc1_out_stat                         full
% 51.34/6.98  --bmc1_ground_init                      false
% 51.34/6.98  --bmc1_pre_inst_next_state              false
% 51.34/6.98  --bmc1_pre_inst_state                   false
% 51.34/6.98  --bmc1_pre_inst_reach_state             false
% 51.34/6.98  --bmc1_out_unsat_core                   false
% 51.34/6.98  --bmc1_aig_witness_out                  false
% 51.34/6.98  --bmc1_verbose                          false
% 51.34/6.98  --bmc1_dump_clauses_tptp                false
% 51.34/6.98  --bmc1_dump_unsat_core_tptp             false
% 51.34/6.98  --bmc1_dump_file                        -
% 51.34/6.98  --bmc1_ucm_expand_uc_limit              128
% 51.34/6.98  --bmc1_ucm_n_expand_iterations          6
% 51.34/6.98  --bmc1_ucm_extend_mode                  1
% 51.34/6.98  --bmc1_ucm_init_mode                    2
% 51.34/6.98  --bmc1_ucm_cone_mode                    none
% 51.34/6.98  --bmc1_ucm_reduced_relation_type        0
% 51.34/6.98  --bmc1_ucm_relax_model                  4
% 51.34/6.98  --bmc1_ucm_full_tr_after_sat            true
% 51.34/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 51.34/6.98  --bmc1_ucm_layered_model                none
% 51.34/6.98  --bmc1_ucm_max_lemma_size               10
% 51.34/6.98  
% 51.34/6.98  ------ AIG Options
% 51.34/6.98  
% 51.34/6.98  --aig_mode                              false
% 51.34/6.98  
% 51.34/6.98  ------ Instantiation Options
% 51.34/6.98  
% 51.34/6.98  --instantiation_flag                    true
% 51.34/6.98  --inst_sos_flag                         true
% 51.34/6.98  --inst_sos_phase                        true
% 51.34/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.34/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.34/6.98  --inst_lit_sel_side                     num_symb
% 51.34/6.98  --inst_solver_per_active                1400
% 51.34/6.98  --inst_solver_calls_frac                1.
% 51.34/6.98  --inst_passive_queue_type               priority_queues
% 51.34/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.34/6.98  --inst_passive_queues_freq              [25;2]
% 51.34/6.98  --inst_dismatching                      true
% 51.34/6.98  --inst_eager_unprocessed_to_passive     true
% 51.34/6.98  --inst_prop_sim_given                   true
% 51.34/6.98  --inst_prop_sim_new                     false
% 51.34/6.98  --inst_subs_new                         false
% 51.34/6.98  --inst_eq_res_simp                      false
% 51.34/6.98  --inst_subs_given                       false
% 51.34/6.98  --inst_orphan_elimination               true
% 51.34/6.98  --inst_learning_loop_flag               true
% 51.34/6.98  --inst_learning_start                   3000
% 51.34/6.98  --inst_learning_factor                  2
% 51.34/6.98  --inst_start_prop_sim_after_learn       3
% 51.34/6.98  --inst_sel_renew                        solver
% 51.34/6.98  --inst_lit_activity_flag                true
% 51.34/6.98  --inst_restr_to_given                   false
% 51.34/6.98  --inst_activity_threshold               500
% 51.34/6.98  --inst_out_proof                        true
% 51.34/6.98  
% 51.34/6.98  ------ Resolution Options
% 51.34/6.98  
% 51.34/6.98  --resolution_flag                       true
% 51.34/6.98  --res_lit_sel                           adaptive
% 51.34/6.98  --res_lit_sel_side                      none
% 51.34/6.98  --res_ordering                          kbo
% 51.34/6.98  --res_to_prop_solver                    active
% 51.34/6.98  --res_prop_simpl_new                    false
% 51.34/6.98  --res_prop_simpl_given                  true
% 51.34/6.98  --res_passive_queue_type                priority_queues
% 51.34/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.34/6.98  --res_passive_queues_freq               [15;5]
% 51.34/6.98  --res_forward_subs                      full
% 51.34/6.98  --res_backward_subs                     full
% 51.34/6.98  --res_forward_subs_resolution           true
% 51.34/6.98  --res_backward_subs_resolution          true
% 51.34/6.98  --res_orphan_elimination                true
% 51.34/6.98  --res_time_limit                        2.
% 51.34/6.98  --res_out_proof                         true
% 51.34/6.98  
% 51.34/6.98  ------ Superposition Options
% 51.34/6.98  
% 51.34/6.98  --superposition_flag                    true
% 51.34/6.98  --sup_passive_queue_type                priority_queues
% 51.34/6.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.34/6.98  --sup_passive_queues_freq               [8;1;4]
% 51.34/6.98  --demod_completeness_check              fast
% 51.34/6.98  --demod_use_ground                      true
% 51.34/6.98  --sup_to_prop_solver                    passive
% 51.34/6.98  --sup_prop_simpl_new                    true
% 51.34/6.98  --sup_prop_simpl_given                  true
% 51.34/6.98  --sup_fun_splitting                     true
% 51.34/6.98  --sup_smt_interval                      50000
% 51.34/6.98  
% 51.34/6.98  ------ Superposition Simplification Setup
% 51.34/6.98  
% 51.34/6.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.34/6.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.34/6.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.34/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.34/6.98  --sup_full_triv                         [TrivRules;PropSubs]
% 51.34/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.34/6.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.34/6.98  --sup_immed_triv                        [TrivRules]
% 51.34/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/6.98  --sup_immed_bw_main                     []
% 51.34/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.34/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 51.34/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/6.98  --sup_input_bw                          []
% 51.34/6.98  
% 51.34/6.98  ------ Combination Options
% 51.34/6.98  
% 51.34/6.98  --comb_res_mult                         3
% 51.34/6.98  --comb_sup_mult                         2
% 51.34/6.98  --comb_inst_mult                        10
% 51.34/6.98  
% 51.34/6.98  ------ Debug Options
% 51.34/6.98  
% 51.34/6.98  --dbg_backtrace                         false
% 51.34/6.98  --dbg_dump_prop_clauses                 false
% 51.34/6.98  --dbg_dump_prop_clauses_file            -
% 51.34/6.98  --dbg_out_stat                          false
% 51.34/6.98  ------ Parsing...
% 51.34/6.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.34/6.98  
% 51.34/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.34/6.98  
% 51.34/6.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.34/6.98  
% 51.34/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.34/6.98  ------ Proving...
% 51.34/6.98  ------ Problem Properties 
% 51.34/6.98  
% 51.34/6.98  
% 51.34/6.98  clauses                                 14
% 51.34/6.98  conjectures                             3
% 51.34/6.98  EPR                                     3
% 51.34/6.98  Horn                                    14
% 51.34/6.98  unary                                   5
% 51.34/6.98  binary                                  6
% 51.34/6.98  lits                                    26
% 51.34/6.98  lits eq                                 7
% 51.34/6.98  fd_pure                                 0
% 51.34/6.98  fd_pseudo                               0
% 51.34/6.98  fd_cond                                 0
% 51.34/6.98  fd_pseudo_cond                          0
% 51.34/6.98  AC symbols                              0
% 51.34/6.98  
% 51.34/6.98  ------ Schedule dynamic 5 is on 
% 51.34/6.98  
% 51.34/6.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.34/6.98  
% 51.34/6.98  
% 51.34/6.98  ------ 
% 51.34/6.98  Current options:
% 51.34/6.98  ------ 
% 51.34/6.98  
% 51.34/6.98  ------ Input Options
% 51.34/6.98  
% 51.34/6.98  --out_options                           all
% 51.34/6.98  --tptp_safe_out                         true
% 51.34/6.98  --problem_path                          ""
% 51.34/6.98  --include_path                          ""
% 51.34/6.98  --clausifier                            res/vclausify_rel
% 51.34/6.98  --clausifier_options                    ""
% 51.34/6.98  --stdin                                 false
% 51.34/6.98  --stats_out                             all
% 51.34/6.98  
% 51.34/6.98  ------ General Options
% 51.34/6.98  
% 51.34/6.98  --fof                                   false
% 51.34/6.98  --time_out_real                         305.
% 51.34/6.98  --time_out_virtual                      -1.
% 51.34/6.98  --symbol_type_check                     false
% 51.34/6.98  --clausify_out                          false
% 51.34/6.98  --sig_cnt_out                           false
% 51.34/6.98  --trig_cnt_out                          false
% 51.34/6.98  --trig_cnt_out_tolerance                1.
% 51.34/6.98  --trig_cnt_out_sk_spl                   false
% 51.34/6.98  --abstr_cl_out                          false
% 51.34/6.98  
% 51.34/6.98  ------ Global Options
% 51.34/6.98  
% 51.34/6.98  --schedule                              default
% 51.34/6.98  --add_important_lit                     false
% 51.34/6.98  --prop_solver_per_cl                    1000
% 51.34/6.98  --min_unsat_core                        false
% 51.34/6.98  --soft_assumptions                      false
% 51.34/6.98  --soft_lemma_size                       3
% 51.34/6.98  --prop_impl_unit_size                   0
% 51.34/6.98  --prop_impl_unit                        []
% 51.34/6.98  --share_sel_clauses                     true
% 51.34/6.98  --reset_solvers                         false
% 51.34/6.98  --bc_imp_inh                            [conj_cone]
% 51.34/6.98  --conj_cone_tolerance                   3.
% 51.34/6.98  --extra_neg_conj                        none
% 51.34/6.98  --large_theory_mode                     true
% 51.34/6.98  --prolific_symb_bound                   200
% 51.34/6.98  --lt_threshold                          2000
% 51.34/6.98  --clause_weak_htbl                      true
% 51.34/6.98  --gc_record_bc_elim                     false
% 51.34/6.98  
% 51.34/6.98  ------ Preprocessing Options
% 51.34/6.98  
% 51.34/6.98  --preprocessing_flag                    true
% 51.34/6.98  --time_out_prep_mult                    0.1
% 51.34/6.98  --splitting_mode                        input
% 51.34/6.98  --splitting_grd                         true
% 51.34/6.98  --splitting_cvd                         false
% 51.34/6.98  --splitting_cvd_svl                     false
% 51.34/6.98  --splitting_nvd                         32
% 51.34/6.98  --sub_typing                            true
% 51.34/6.98  --prep_gs_sim                           true
% 51.34/6.98  --prep_unflatten                        true
% 51.34/6.98  --prep_res_sim                          true
% 51.34/6.98  --prep_upred                            true
% 51.34/6.98  --prep_sem_filter                       exhaustive
% 51.34/6.98  --prep_sem_filter_out                   false
% 51.34/6.98  --pred_elim                             true
% 51.34/6.98  --res_sim_input                         true
% 51.34/6.98  --eq_ax_congr_red                       true
% 51.34/6.98  --pure_diseq_elim                       true
% 51.34/6.98  --brand_transform                       false
% 51.34/6.98  --non_eq_to_eq                          false
% 51.34/6.98  --prep_def_merge                        true
% 51.34/6.98  --prep_def_merge_prop_impl              false
% 51.34/6.98  --prep_def_merge_mbd                    true
% 51.34/6.98  --prep_def_merge_tr_red                 false
% 51.34/6.98  --prep_def_merge_tr_cl                  false
% 51.34/6.98  --smt_preprocessing                     true
% 51.34/6.98  --smt_ac_axioms                         fast
% 51.34/6.98  --preprocessed_out                      false
% 51.34/6.98  --preprocessed_stats                    false
% 51.34/6.98  
% 51.34/6.98  ------ Abstraction refinement Options
% 51.34/6.98  
% 51.34/6.98  --abstr_ref                             []
% 51.34/6.98  --abstr_ref_prep                        false
% 51.34/6.98  --abstr_ref_until_sat                   false
% 51.34/6.98  --abstr_ref_sig_restrict                funpre
% 51.34/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 51.34/6.98  --abstr_ref_under                       []
% 51.34/6.98  
% 51.34/6.98  ------ SAT Options
% 51.34/6.98  
% 51.34/6.98  --sat_mode                              false
% 51.34/6.98  --sat_fm_restart_options                ""
% 51.34/6.98  --sat_gr_def                            false
% 51.34/6.98  --sat_epr_types                         true
% 51.34/6.98  --sat_non_cyclic_types                  false
% 51.34/6.98  --sat_finite_models                     false
% 51.34/6.98  --sat_fm_lemmas                         false
% 51.34/6.98  --sat_fm_prep                           false
% 51.34/6.98  --sat_fm_uc_incr                        true
% 51.34/6.98  --sat_out_model                         small
% 51.34/6.98  --sat_out_clauses                       false
% 51.34/6.98  
% 51.34/6.98  ------ QBF Options
% 51.34/6.98  
% 51.34/6.98  --qbf_mode                              false
% 51.34/6.98  --qbf_elim_univ                         false
% 51.34/6.98  --qbf_dom_inst                          none
% 51.34/6.98  --qbf_dom_pre_inst                      false
% 51.34/6.98  --qbf_sk_in                             false
% 51.34/6.98  --qbf_pred_elim                         true
% 51.34/6.98  --qbf_split                             512
% 51.34/6.98  
% 51.34/6.98  ------ BMC1 Options
% 51.34/6.98  
% 51.34/6.98  --bmc1_incremental                      false
% 51.34/6.98  --bmc1_axioms                           reachable_all
% 51.34/6.98  --bmc1_min_bound                        0
% 51.34/6.98  --bmc1_max_bound                        -1
% 51.34/6.98  --bmc1_max_bound_default                -1
% 51.34/6.98  --bmc1_symbol_reachability              true
% 51.34/6.98  --bmc1_property_lemmas                  false
% 51.34/6.98  --bmc1_k_induction                      false
% 51.34/6.98  --bmc1_non_equiv_states                 false
% 51.34/6.98  --bmc1_deadlock                         false
% 51.34/6.98  --bmc1_ucm                              false
% 51.34/6.98  --bmc1_add_unsat_core                   none
% 51.34/6.98  --bmc1_unsat_core_children              false
% 51.34/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 51.34/6.98  --bmc1_out_stat                         full
% 51.34/6.98  --bmc1_ground_init                      false
% 51.34/6.98  --bmc1_pre_inst_next_state              false
% 51.34/6.98  --bmc1_pre_inst_state                   false
% 51.34/6.98  --bmc1_pre_inst_reach_state             false
% 51.34/6.98  --bmc1_out_unsat_core                   false
% 51.34/6.98  --bmc1_aig_witness_out                  false
% 51.34/6.98  --bmc1_verbose                          false
% 51.34/6.98  --bmc1_dump_clauses_tptp                false
% 51.34/6.98  --bmc1_dump_unsat_core_tptp             false
% 51.34/6.98  --bmc1_dump_file                        -
% 51.34/6.98  --bmc1_ucm_expand_uc_limit              128
% 51.34/6.98  --bmc1_ucm_n_expand_iterations          6
% 51.34/6.98  --bmc1_ucm_extend_mode                  1
% 51.34/6.98  --bmc1_ucm_init_mode                    2
% 51.34/6.98  --bmc1_ucm_cone_mode                    none
% 51.34/6.98  --bmc1_ucm_reduced_relation_type        0
% 51.34/6.98  --bmc1_ucm_relax_model                  4
% 51.34/6.98  --bmc1_ucm_full_tr_after_sat            true
% 51.34/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 51.34/6.98  --bmc1_ucm_layered_model                none
% 51.34/6.98  --bmc1_ucm_max_lemma_size               10
% 51.34/6.98  
% 51.34/6.98  ------ AIG Options
% 51.34/6.98  
% 51.34/6.98  --aig_mode                              false
% 51.34/6.98  
% 51.34/6.98  ------ Instantiation Options
% 51.34/6.98  
% 51.34/6.98  --instantiation_flag                    true
% 51.34/6.98  --inst_sos_flag                         true
% 51.34/6.98  --inst_sos_phase                        true
% 51.34/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.34/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.34/6.98  --inst_lit_sel_side                     none
% 51.34/6.98  --inst_solver_per_active                1400
% 51.34/6.98  --inst_solver_calls_frac                1.
% 51.34/6.98  --inst_passive_queue_type               priority_queues
% 51.34/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.34/6.98  --inst_passive_queues_freq              [25;2]
% 51.34/6.98  --inst_dismatching                      true
% 51.34/6.98  --inst_eager_unprocessed_to_passive     true
% 51.34/6.98  --inst_prop_sim_given                   true
% 51.34/6.98  --inst_prop_sim_new                     false
% 51.34/6.98  --inst_subs_new                         false
% 51.34/6.98  --inst_eq_res_simp                      false
% 51.34/6.98  --inst_subs_given                       false
% 51.34/6.98  --inst_orphan_elimination               true
% 51.34/6.98  --inst_learning_loop_flag               true
% 51.34/6.98  --inst_learning_start                   3000
% 51.34/6.98  --inst_learning_factor                  2
% 51.34/6.98  --inst_start_prop_sim_after_learn       3
% 51.34/6.98  --inst_sel_renew                        solver
% 51.34/6.98  --inst_lit_activity_flag                true
% 51.34/6.98  --inst_restr_to_given                   false
% 51.34/6.98  --inst_activity_threshold               500
% 51.34/6.98  --inst_out_proof                        true
% 51.34/6.98  
% 51.34/6.98  ------ Resolution Options
% 51.34/6.98  
% 51.34/6.98  --resolution_flag                       false
% 51.34/6.98  --res_lit_sel                           adaptive
% 51.34/6.98  --res_lit_sel_side                      none
% 51.34/6.98  --res_ordering                          kbo
% 51.34/6.98  --res_to_prop_solver                    active
% 51.34/6.98  --res_prop_simpl_new                    false
% 51.34/6.98  --res_prop_simpl_given                  true
% 51.34/6.98  --res_passive_queue_type                priority_queues
% 51.34/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.34/6.98  --res_passive_queues_freq               [15;5]
% 51.34/6.98  --res_forward_subs                      full
% 51.34/6.98  --res_backward_subs                     full
% 51.34/6.98  --res_forward_subs_resolution           true
% 51.34/6.98  --res_backward_subs_resolution          true
% 51.34/6.98  --res_orphan_elimination                true
% 51.34/6.98  --res_time_limit                        2.
% 51.34/6.98  --res_out_proof                         true
% 51.34/6.98  
% 51.34/6.98  ------ Superposition Options
% 51.34/6.98  
% 51.34/6.98  --superposition_flag                    true
% 51.34/6.98  --sup_passive_queue_type                priority_queues
% 51.34/6.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.34/6.98  --sup_passive_queues_freq               [8;1;4]
% 51.34/6.98  --demod_completeness_check              fast
% 51.34/6.98  --demod_use_ground                      true
% 51.34/6.98  --sup_to_prop_solver                    passive
% 51.34/6.98  --sup_prop_simpl_new                    true
% 51.34/6.98  --sup_prop_simpl_given                  true
% 51.34/6.98  --sup_fun_splitting                     true
% 51.34/6.98  --sup_smt_interval                      50000
% 51.34/6.98  
% 51.34/6.98  ------ Superposition Simplification Setup
% 51.34/6.98  
% 51.34/6.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.34/6.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.34/6.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.34/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.34/6.98  --sup_full_triv                         [TrivRules;PropSubs]
% 51.34/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.34/6.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.34/6.98  --sup_immed_triv                        [TrivRules]
% 51.34/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/6.98  --sup_immed_bw_main                     []
% 51.34/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.34/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 51.34/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/6.98  --sup_input_bw                          []
% 51.34/6.98  
% 51.34/6.98  ------ Combination Options
% 51.34/6.98  
% 51.34/6.98  --comb_res_mult                         3
% 51.34/6.98  --comb_sup_mult                         2
% 51.34/6.98  --comb_inst_mult                        10
% 51.34/6.98  
% 51.34/6.98  ------ Debug Options
% 51.34/6.98  
% 51.34/6.98  --dbg_backtrace                         false
% 51.34/6.98  --dbg_dump_prop_clauses                 false
% 51.34/6.98  --dbg_dump_prop_clauses_file            -
% 51.34/6.98  --dbg_out_stat                          false
% 51.34/6.98  
% 51.34/6.98  
% 51.34/6.98  
% 51.34/6.98  
% 51.34/6.98  ------ Proving...
% 51.34/6.98  
% 51.34/6.98  
% 51.34/6.98  % SZS status Theorem for theBenchmark.p
% 51.34/6.98  
% 51.34/6.98  % SZS output start CNFRefutation for theBenchmark.p
% 51.34/6.98  
% 51.34/6.98  fof(f14,conjecture,(
% 51.34/6.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f15,negated_conjecture,(
% 51.34/6.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 51.34/6.98    inference(negated_conjecture,[],[f14])).
% 51.34/6.98  
% 51.34/6.98  fof(f28,plain,(
% 51.34/6.98    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 51.34/6.98    inference(ennf_transformation,[],[f15])).
% 51.34/6.98  
% 51.34/6.98  fof(f29,plain,(
% 51.34/6.98    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 51.34/6.98    inference(flattening,[],[f28])).
% 51.34/6.98  
% 51.34/6.98  fof(f31,plain,(
% 51.34/6.98    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 51.34/6.98    introduced(choice_axiom,[])).
% 51.34/6.98  
% 51.34/6.98  fof(f32,plain,(
% 51.34/6.98    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 51.34/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f31])).
% 51.34/6.98  
% 51.34/6.98  fof(f48,plain,(
% 51.34/6.98    v1_relat_1(sK2)),
% 51.34/6.98    inference(cnf_transformation,[],[f32])).
% 51.34/6.98  
% 51.34/6.98  fof(f7,axiom,(
% 51.34/6.98    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f19,plain,(
% 51.34/6.98    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 51.34/6.98    inference(ennf_transformation,[],[f7])).
% 51.34/6.98  
% 51.34/6.98  fof(f40,plain,(
% 51.34/6.98    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f19])).
% 51.34/6.98  
% 51.34/6.98  fof(f5,axiom,(
% 51.34/6.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f37,plain,(
% 51.34/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 51.34/6.98    inference(cnf_transformation,[],[f5])).
% 51.34/6.98  
% 51.34/6.98  fof(f4,axiom,(
% 51.34/6.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f36,plain,(
% 51.34/6.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f4])).
% 51.34/6.98  
% 51.34/6.98  fof(f51,plain,(
% 51.34/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 51.34/6.98    inference(definition_unfolding,[],[f37,f36])).
% 51.34/6.98  
% 51.34/6.98  fof(f54,plain,(
% 51.34/6.98    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 51.34/6.98    inference(definition_unfolding,[],[f40,f51])).
% 51.34/6.98  
% 51.34/6.98  fof(f3,axiom,(
% 51.34/6.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f35,plain,(
% 51.34/6.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f3])).
% 51.34/6.98  
% 51.34/6.98  fof(f53,plain,(
% 51.34/6.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 51.34/6.98    inference(definition_unfolding,[],[f35,f36,f36])).
% 51.34/6.98  
% 51.34/6.98  fof(f2,axiom,(
% 51.34/6.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f34,plain,(
% 51.34/6.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 51.34/6.98    inference(cnf_transformation,[],[f2])).
% 51.34/6.98  
% 51.34/6.98  fof(f52,plain,(
% 51.34/6.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 51.34/6.98    inference(definition_unfolding,[],[f34,f51])).
% 51.34/6.98  
% 51.34/6.98  fof(f8,axiom,(
% 51.34/6.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f20,plain,(
% 51.34/6.98    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 51.34/6.98    inference(ennf_transformation,[],[f8])).
% 51.34/6.98  
% 51.34/6.98  fof(f21,plain,(
% 51.34/6.98    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 51.34/6.98    inference(flattening,[],[f20])).
% 51.34/6.98  
% 51.34/6.98  fof(f41,plain,(
% 51.34/6.98    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f21])).
% 51.34/6.98  
% 51.34/6.98  fof(f11,axiom,(
% 51.34/6.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f25,plain,(
% 51.34/6.98    ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 51.34/6.98    inference(ennf_transformation,[],[f11])).
% 51.34/6.98  
% 51.34/6.98  fof(f44,plain,(
% 51.34/6.98    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f25])).
% 51.34/6.98  
% 51.34/6.98  fof(f13,axiom,(
% 51.34/6.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f27,plain,(
% 51.34/6.98    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 51.34/6.98    inference(ennf_transformation,[],[f13])).
% 51.34/6.98  
% 51.34/6.98  fof(f47,plain,(
% 51.34/6.98    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f27])).
% 51.34/6.98  
% 51.34/6.98  fof(f10,axiom,(
% 51.34/6.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f24,plain,(
% 51.34/6.98    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 51.34/6.98    inference(ennf_transformation,[],[f10])).
% 51.34/6.98  
% 51.34/6.98  fof(f43,plain,(
% 51.34/6.98    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f24])).
% 51.34/6.98  
% 51.34/6.98  fof(f6,axiom,(
% 51.34/6.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f18,plain,(
% 51.34/6.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 51.34/6.98    inference(ennf_transformation,[],[f6])).
% 51.34/6.98  
% 51.34/6.98  fof(f30,plain,(
% 51.34/6.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 51.34/6.98    inference(nnf_transformation,[],[f18])).
% 51.34/6.98  
% 51.34/6.98  fof(f39,plain,(
% 51.34/6.98    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f30])).
% 51.34/6.98  
% 51.34/6.98  fof(f9,axiom,(
% 51.34/6.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f22,plain,(
% 51.34/6.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 51.34/6.98    inference(ennf_transformation,[],[f9])).
% 51.34/6.98  
% 51.34/6.98  fof(f23,plain,(
% 51.34/6.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 51.34/6.98    inference(flattening,[],[f22])).
% 51.34/6.98  
% 51.34/6.98  fof(f42,plain,(
% 51.34/6.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f23])).
% 51.34/6.98  
% 51.34/6.98  fof(f1,axiom,(
% 51.34/6.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f16,plain,(
% 51.34/6.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 51.34/6.98    inference(ennf_transformation,[],[f1])).
% 51.34/6.98  
% 51.34/6.98  fof(f17,plain,(
% 51.34/6.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 51.34/6.98    inference(flattening,[],[f16])).
% 51.34/6.98  
% 51.34/6.98  fof(f33,plain,(
% 51.34/6.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f17])).
% 51.34/6.98  
% 51.34/6.98  fof(f50,plain,(
% 51.34/6.98    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 51.34/6.98    inference(cnf_transformation,[],[f32])).
% 51.34/6.98  
% 51.34/6.98  fof(f12,axiom,(
% 51.34/6.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 51.34/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/6.98  
% 51.34/6.98  fof(f26,plain,(
% 51.34/6.98    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 51.34/6.98    inference(ennf_transformation,[],[f12])).
% 51.34/6.98  
% 51.34/6.98  fof(f46,plain,(
% 51.34/6.98    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 51.34/6.98    inference(cnf_transformation,[],[f26])).
% 51.34/6.98  
% 51.34/6.98  fof(f49,plain,(
% 51.34/6.98    r1_tarski(sK0,sK1)),
% 51.34/6.98    inference(cnf_transformation,[],[f32])).
% 51.34/6.98  
% 51.34/6.98  cnf(c_293,plain,
% 51.34/6.98      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 51.34/6.98      theory(equality) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_124251,plain,
% 51.34/6.98      ( X0_43 != X1_43
% 51.34/6.98      | k2_wellord1(sK2,sK0) != X1_43
% 51.34/6.98      | k2_wellord1(sK2,sK0) = X0_43 ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_293]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_124262,plain,
% 51.34/6.98      ( X0_43 != k2_wellord1(sK2,sK0)
% 51.34/6.98      | k2_wellord1(sK2,sK0) = X0_43
% 51.34/6.98      | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_124251]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_124592,plain,
% 51.34/6.98      ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
% 51.34/6.98      | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),X0_42)
% 51.34/6.98      | k7_relat_1(k2_wellord1(sK2,sK0),X0_42) != k2_wellord1(sK2,sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_124262]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_174580,plain,
% 51.34/6.98      ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
% 51.34/6.98      | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
% 51.34/6.98      | k7_relat_1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_124592]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_124933,plain,
% 51.34/6.98      ( X0_43 != k7_relat_1(k2_wellord1(sK2,sK0),X0_42)
% 51.34/6.98      | k2_wellord1(sK2,sK0) = X0_43
% 51.34/6.98      | k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_124251]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_125421,plain,
% 51.34/6.98      ( k2_wellord1(sK2,sK0) = k7_relat_1(X0_43,X0_42)
% 51.34/6.98      | k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42)
% 51.34/6.98      | k7_relat_1(X0_43,X0_42) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_124933]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_144462,plain,
% 51.34/6.98      ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42)
% 51.34/6.98      | k2_wellord1(sK2,sK0) = k7_relat_1(k8_relat_1(X1_42,k2_wellord1(sK2,sK0)),X0_42)
% 51.34/6.98      | k7_relat_1(k8_relat_1(X1_42,k2_wellord1(sK2,sK0)),X0_42) != k7_relat_1(k2_wellord1(sK2,sK0),X0_42) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_125421]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_151927,plain,
% 51.34/6.98      ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
% 51.34/6.98      | k2_wellord1(sK2,sK0) = k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1)
% 51.34/6.98      | k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_144462]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_300,plain,
% 51.34/6.98      ( X0_43 != X1_43
% 51.34/6.98      | k7_relat_1(X0_43,X0_42) = k7_relat_1(X1_43,X0_42) ),
% 51.34/6.98      theory(equality) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_4344,plain,
% 51.34/6.98      ( k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k7_relat_1(X1_43,X0_42)
% 51.34/6.98      | k8_relat_1(X0_42,X0_43) != X1_43 ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_300]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_83730,plain,
% 51.34/6.98      ( k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
% 51.34/6.98      | k8_relat_1(sK1,k2_wellord1(sK2,sK0)) != k2_wellord1(sK2,sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_4344]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_15,negated_conjecture,
% 51.34/6.98      ( v1_relat_1(sK2) ),
% 51.34/6.98      inference(cnf_transformation,[],[f48]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_275,negated_conjecture,
% 51.34/6.98      ( v1_relat_1(sK2) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_15]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_534,plain,
% 51.34/6.98      ( v1_relat_1(sK2) = iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_5,plain,
% 51.34/6.98      ( ~ v1_relat_1(X0)
% 51.34/6.98      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 51.34/6.98      inference(cnf_transformation,[],[f54]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_284,plain,
% 51.34/6.98      ( ~ v1_relat_1(X0_43)
% 51.34/6.98      | k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_5]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_526,plain,
% 51.34/6.98      ( k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
% 51.34/6.98      | v1_relat_1(X0_43) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_843,plain,
% 51.34/6.98      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_534,c_526]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_2,plain,
% 51.34/6.98      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 51.34/6.98      inference(cnf_transformation,[],[f53]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_285,plain,
% 51.34/6.98      ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_2]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1,plain,
% 51.34/6.98      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 51.34/6.98      inference(cnf_transformation,[],[f52]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_286,plain,
% 51.34/6.98      ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X0_42,X0_42,X1_42))) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_1]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_525,plain,
% 51.34/6.98      ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X0_42,X0_42,X1_42))) = iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_659,plain,
% 51.34/6.98      ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X1_42,X1_42,X0_42))) = iProver_top ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_285,c_525]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_999,plain,
% 51.34/6.98      ( r1_tarski(k2_relat_1(sK2),k3_relat_1(sK2)) = iProver_top ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_843,c_659]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_6,plain,
% 51.34/6.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 51.34/6.98      | ~ v1_relat_1(X0)
% 51.34/6.98      | k8_relat_1(X1,X0) = X0 ),
% 51.34/6.98      inference(cnf_transformation,[],[f41]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_283,plain,
% 51.34/6.98      ( ~ r1_tarski(k2_relat_1(X0_43),X0_42)
% 51.34/6.98      | ~ v1_relat_1(X0_43)
% 51.34/6.98      | k8_relat_1(X0_42,X0_43) = X0_43 ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_6]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_527,plain,
% 51.34/6.98      ( k8_relat_1(X0_42,X0_43) = X0_43
% 51.34/6.98      | r1_tarski(k2_relat_1(X0_43),X0_42) != iProver_top
% 51.34/6.98      | v1_relat_1(X0_43) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1212,plain,
% 51.34/6.98      ( k8_relat_1(k3_relat_1(sK2),sK2) = sK2
% 51.34/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_999,c_527]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_16,plain,
% 51.34/6.98      ( v1_relat_1(sK2) = iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1296,plain,
% 51.34/6.98      ( k8_relat_1(k3_relat_1(sK2),sK2) = sK2 ),
% 51.34/6.98      inference(global_propositional_subsumption,
% 51.34/6.98                [status(thm)],
% 51.34/6.98                [c_1212,c_16]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_9,plain,
% 51.34/6.98      ( ~ v1_relat_1(X0)
% 51.34/6.98      | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
% 51.34/6.98      inference(cnf_transformation,[],[f44]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_281,plain,
% 51.34/6.98      ( ~ v1_relat_1(X0_43)
% 51.34/6.98      | k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k2_wellord1(X0_43,X0_42) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_9]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_529,plain,
% 51.34/6.98      ( k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k2_wellord1(X0_43,X0_42)
% 51.34/6.98      | v1_relat_1(X0_43) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_771,plain,
% 51.34/6.98      ( k7_relat_1(k8_relat_1(X0_42,sK2),X0_42) = k2_wellord1(sK2,X0_42) ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_534,c_529]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1298,plain,
% 51.34/6.98      ( k2_wellord1(sK2,k3_relat_1(sK2)) = k7_relat_1(sK2,k3_relat_1(sK2)) ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_1296,c_771]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_12,plain,
% 51.34/6.98      ( ~ v1_relat_1(X0)
% 51.34/6.98      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 51.34/6.98      inference(cnf_transformation,[],[f47]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_278,plain,
% 51.34/6.98      ( ~ v1_relat_1(X0_43)
% 51.34/6.98      | k2_wellord1(k2_wellord1(X0_43,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_12]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_532,plain,
% 51.34/6.98      ( k2_wellord1(k2_wellord1(X0_43,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42)
% 51.34/6.98      | v1_relat_1(X0_43) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_913,plain,
% 51.34/6.98      ( k2_wellord1(k2_wellord1(sK2,X0_42),X1_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_534,c_532]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1485,plain,
% 51.34/6.98      ( k2_wellord1(k7_relat_1(sK2,k3_relat_1(sK2)),X0_42) = k2_wellord1(k2_wellord1(sK2,X0_42),k3_relat_1(sK2)) ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_1298,c_913]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_8,plain,
% 51.34/6.98      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 51.34/6.98      inference(cnf_transformation,[],[f43]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_282,plain,
% 51.34/6.98      ( ~ v1_relat_1(X0_43) | v1_relat_1(k2_wellord1(X0_43,X0_42)) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_8]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_528,plain,
% 51.34/6.98      ( v1_relat_1(X0_43) != iProver_top
% 51.34/6.98      | v1_relat_1(k2_wellord1(X0_43,X0_42)) = iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1494,plain,
% 51.34/6.98      ( v1_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),k3_relat_1(sK2))) = iProver_top
% 51.34/6.98      | v1_relat_1(k7_relat_1(sK2,k3_relat_1(sK2))) != iProver_top ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_1485,c_528]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1484,plain,
% 51.34/6.98      ( v1_relat_1(k7_relat_1(sK2,k3_relat_1(sK2))) = iProver_top
% 51.34/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_1298,c_528]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_4036,plain,
% 51.34/6.98      ( v1_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),k3_relat_1(sK2))) = iProver_top ),
% 51.34/6.98      inference(global_propositional_subsumption,
% 51.34/6.98                [status(thm)],
% 51.34/6.98                [c_1494,c_16,c_1484]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_998,plain,
% 51.34/6.98      ( r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2)) = iProver_top ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_843,c_525]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_3,plain,
% 51.34/6.98      ( v4_relat_1(X0,X1)
% 51.34/6.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 51.34/6.98      | ~ v1_relat_1(X0) ),
% 51.34/6.98      inference(cnf_transformation,[],[f39]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_7,plain,
% 51.34/6.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 51.34/6.98      inference(cnf_transformation,[],[f42]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_167,plain,
% 51.34/6.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 51.34/6.98      | ~ v1_relat_1(X0)
% 51.34/6.98      | k7_relat_1(X0,X1) = X0 ),
% 51.34/6.98      inference(resolution,[status(thm)],[c_3,c_7]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_274,plain,
% 51.34/6.98      ( ~ r1_tarski(k1_relat_1(X0_43),X0_42)
% 51.34/6.98      | ~ v1_relat_1(X0_43)
% 51.34/6.98      | k7_relat_1(X0_43,X0_42) = X0_43 ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_167]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_535,plain,
% 51.34/6.98      ( k7_relat_1(X0_43,X0_42) = X0_43
% 51.34/6.98      | r1_tarski(k1_relat_1(X0_43),X0_42) != iProver_top
% 51.34/6.98      | v1_relat_1(X0_43) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_2092,plain,
% 51.34/6.98      ( k7_relat_1(sK2,k3_relat_1(sK2)) = sK2
% 51.34/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_998,c_535]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_2910,plain,
% 51.34/6.98      ( k7_relat_1(sK2,k3_relat_1(sK2)) = sK2 ),
% 51.34/6.98      inference(global_propositional_subsumption,
% 51.34/6.98                [status(thm)],
% 51.34/6.98                [c_2092,c_16]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_2915,plain,
% 51.34/6.98      ( k2_wellord1(k2_wellord1(sK2,X0_42),k3_relat_1(sK2)) = k2_wellord1(sK2,X0_42) ),
% 51.34/6.98      inference(demodulation,[status(thm)],[c_2910,c_1485]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_4042,plain,
% 51.34/6.98      ( v1_relat_1(k2_wellord1(sK2,X0_42)) = iProver_top ),
% 51.34/6.98      inference(light_normalisation,[status(thm)],[c_4036,c_2915]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_4053,plain,
% 51.34/6.98      ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k2_relat_1(k2_wellord1(sK2,X0_42)))) = k3_relat_1(k2_wellord1(sK2,X0_42)) ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_4042,c_526]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_33407,plain,
% 51.34/6.98      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_4053,c_659]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_33425,plain,
% 51.34/6.98      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) = iProver_top ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_33407]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_33406,plain,
% 51.34/6.98      ( r1_tarski(k1_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
% 51.34/6.98      inference(superposition,[status(thm)],[c_4053,c_525]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_33422,plain,
% 51.34/6.98      ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) = iProver_top ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_33406]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_629,plain,
% 51.34/6.98      ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),X0_42)
% 51.34/6.98      | ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 51.34/6.98      | k8_relat_1(X0_42,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_283]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_4843,plain,
% 51.34/6.98      ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
% 51.34/6.98      | ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 51.34/6.98      | k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_629]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_4846,plain,
% 51.34/6.98      ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
% 51.34/6.98      | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) != iProver_top
% 51.34/6.98      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_4843]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_623,plain,
% 51.34/6.98      ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),X0_42)
% 51.34/6.98      | ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 51.34/6.98      | k7_relat_1(k2_wellord1(sK2,sK0),X0_42) = k2_wellord1(sK2,sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_274]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_4832,plain,
% 51.34/6.98      ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
% 51.34/6.98      | ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 51.34/6.98      | k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_623]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_4835,plain,
% 51.34/6.98      ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0)
% 51.34/6.98      | r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) != iProver_top
% 51.34/6.98      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_4832]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_571,plain,
% 51.34/6.98      ( k2_wellord1(X0_43,X0_42) != X1_43
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X1_43
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(X0_43,X0_42) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_293]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_3272,plain,
% 51.34/6.98      ( k2_wellord1(X0_43,X0_42) != k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,X1_42)),sK1)
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(X0_43,X0_42)
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,X1_42)),sK1) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_571]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_3273,plain,
% 51.34/6.98      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(sK2,sK0)
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1)
% 51.34/6.98      | k2_wellord1(sK2,sK0) != k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_3272]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_0,plain,
% 51.34/6.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 51.34/6.98      inference(cnf_transformation,[],[f33]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_287,plain,
% 51.34/6.98      ( ~ r1_tarski(X0_42,X1_42)
% 51.34/6.98      | ~ r1_tarski(X2_42,X0_42)
% 51.34/6.98      | r1_tarski(X2_42,X1_42) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_0]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1092,plain,
% 51.34/6.98      ( ~ r1_tarski(X0_42,X1_42)
% 51.34/6.98      | ~ r1_tarski(k2_relat_1(k2_wellord1(X0_43,X2_42)),X0_42)
% 51.34/6.98      | r1_tarski(k2_relat_1(k2_wellord1(X0_43,X2_42)),X1_42) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_287]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1707,plain,
% 51.34/6.98      ( ~ r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
% 51.34/6.98      | r1_tarski(k2_relat_1(k2_wellord1(X1_43,X1_42)),X0_42)
% 51.34/6.98      | ~ r1_tarski(k2_relat_1(k2_wellord1(X1_43,X1_42)),k3_relat_1(k2_wellord1(X0_43,X0_42))) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_1092]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1708,plain,
% 51.34/6.98      ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42) != iProver_top
% 51.34/6.98      | r1_tarski(k2_relat_1(k2_wellord1(X1_43,X1_42)),X0_42) = iProver_top
% 51.34/6.98      | r1_tarski(k2_relat_1(k2_wellord1(X1_43,X1_42)),k3_relat_1(k2_wellord1(X0_43,X0_42))) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_1707]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1710,plain,
% 51.34/6.98      ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
% 51.34/6.98      | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) != iProver_top
% 51.34/6.98      | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_1708]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1697,plain,
% 51.34/6.98      ( r1_tarski(k2_relat_1(k2_wellord1(X0_43,X0_42)),sK1)
% 51.34/6.98      | ~ r1_tarski(k2_relat_1(k2_wellord1(X0_43,X0_42)),sK0)
% 51.34/6.98      | ~ r1_tarski(sK0,sK1) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_1092]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1698,plain,
% 51.34/6.98      ( r1_tarski(k2_relat_1(k2_wellord1(X0_43,X0_42)),sK1) = iProver_top
% 51.34/6.98      | r1_tarski(k2_relat_1(k2_wellord1(X0_43,X0_42)),sK0) != iProver_top
% 51.34/6.98      | r1_tarski(sK0,sK1) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_1697]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1700,plain,
% 51.34/6.98      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top
% 51.34/6.98      | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
% 51.34/6.98      | r1_tarski(sK0,sK1) != iProver_top ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_1698]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1078,plain,
% 51.34/6.98      ( ~ r1_tarski(X0_42,X1_42)
% 51.34/6.98      | ~ r1_tarski(k1_relat_1(k2_wellord1(X0_43,X2_42)),X0_42)
% 51.34/6.98      | r1_tarski(k1_relat_1(k2_wellord1(X0_43,X2_42)),X1_42) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_287]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1683,plain,
% 51.34/6.98      ( ~ r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
% 51.34/6.98      | r1_tarski(k1_relat_1(k2_wellord1(X1_43,X1_42)),X0_42)
% 51.34/6.98      | ~ r1_tarski(k1_relat_1(k2_wellord1(X1_43,X1_42)),k3_relat_1(k2_wellord1(X0_43,X0_42))) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_1078]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1684,plain,
% 51.34/6.98      ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42) != iProver_top
% 51.34/6.98      | r1_tarski(k1_relat_1(k2_wellord1(X1_43,X1_42)),X0_42) = iProver_top
% 51.34/6.98      | r1_tarski(k1_relat_1(k2_wellord1(X1_43,X1_42)),k3_relat_1(k2_wellord1(X0_43,X0_42))) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_1683]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1686,plain,
% 51.34/6.98      ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
% 51.34/6.98      | r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) != iProver_top
% 51.34/6.98      | r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_1684]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1673,plain,
% 51.34/6.98      ( r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK1)
% 51.34/6.98      | ~ r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK0)
% 51.34/6.98      | ~ r1_tarski(sK0,sK1) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_1078]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1674,plain,
% 51.34/6.98      ( r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK1) = iProver_top
% 51.34/6.98      | r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK0) != iProver_top
% 51.34/6.98      | r1_tarski(sK0,sK1) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_1673]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1676,plain,
% 51.34/6.98      ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top
% 51.34/6.98      | r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
% 51.34/6.98      | r1_tarski(sK0,sK1) != iProver_top ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_1674]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_1405,plain,
% 51.34/6.98      ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 51.34/6.98      | k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_281]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_610,plain,
% 51.34/6.98      ( X0_43 != X1_43
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X1_43
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = X0_43 ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_293]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_673,plain,
% 51.34/6.98      ( X0_43 != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = X0_43
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_610]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_977,plain,
% 51.34/6.98      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1)
% 51.34/6.98      | k7_relat_1(k8_relat_1(sK1,k2_wellord1(sK2,sK0)),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_673]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_665,plain,
% 51.34/6.98      ( ~ v1_relat_1(sK2)
% 51.34/6.98      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_278]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_550,plain,
% 51.34/6.98      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X0_43
% 51.34/6.98      | k2_wellord1(sK2,sK0) != X0_43
% 51.34/6.98      | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_293]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_555,plain,
% 51.34/6.98      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(sK2,sK0)
% 51.34/6.98      | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)
% 51.34/6.98      | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_550]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_13,negated_conjecture,
% 51.34/6.98      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 51.34/6.98      inference(cnf_transformation,[],[f50]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_277,negated_conjecture,
% 51.34/6.98      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_13]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_10,plain,
% 51.34/6.98      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 51.34/6.98      inference(cnf_transformation,[],[f46]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_280,plain,
% 51.34/6.98      ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
% 51.34/6.98      | ~ v1_relat_1(X0_43) ),
% 51.34/6.98      inference(subtyping,[status(esa)],[c_10]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_328,plain,
% 51.34/6.98      ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42) = iProver_top
% 51.34/6.98      | v1_relat_1(X0_43) != iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_330,plain,
% 51.34/6.98      ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top
% 51.34/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_328]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_322,plain,
% 51.34/6.98      ( v1_relat_1(X0_43) != iProver_top
% 51.34/6.98      | v1_relat_1(k2_wellord1(X0_43,X0_42)) = iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_324,plain,
% 51.34/6.98      ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
% 51.34/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_322]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_323,plain,
% 51.34/6.98      ( v1_relat_1(k2_wellord1(sK2,sK0)) | ~ v1_relat_1(sK2) ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_282]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_290,plain,( X0_43 = X0_43 ),theory(equality) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_311,plain,
% 51.34/6.98      ( sK2 = sK2 ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_290]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_289,plain,( X0_42 = X0_42 ),theory(equality) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_310,plain,
% 51.34/6.98      ( sK0 = sK0 ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_289]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_301,plain,
% 51.34/6.98      ( X0_43 != X1_43
% 51.34/6.98      | k2_wellord1(X0_43,X0_42) = k2_wellord1(X1_43,X1_42)
% 51.34/6.98      | X0_42 != X1_42 ),
% 51.34/6.98      theory(equality) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_308,plain,
% 51.34/6.98      ( k2_wellord1(sK2,sK0) = k2_wellord1(sK2,sK0)
% 51.34/6.98      | sK2 != sK2
% 51.34/6.98      | sK0 != sK0 ),
% 51.34/6.98      inference(instantiation,[status(thm)],[c_301]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_14,negated_conjecture,
% 51.34/6.98      ( r1_tarski(sK0,sK1) ),
% 51.34/6.98      inference(cnf_transformation,[],[f49]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(c_17,plain,
% 51.34/6.98      ( r1_tarski(sK0,sK1) = iProver_top ),
% 51.34/6.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.34/6.98  
% 51.34/6.98  cnf(contradiction,plain,
% 51.34/6.98      ( $false ),
% 51.34/6.98      inference(minisat,
% 51.34/6.98                [status(thm)],
% 51.34/6.98                [c_174580,c_151927,c_83730,c_33425,c_33422,c_4846,c_4835,
% 51.34/6.98                 c_3273,c_1710,c_1700,c_1686,c_1676,c_1405,c_977,c_665,
% 51.34/6.98                 c_555,c_277,c_330,c_324,c_323,c_311,c_310,c_308,c_17,
% 51.34/6.98                 c_16,c_15]) ).
% 51.34/6.98  
% 51.34/6.98  
% 51.34/6.98  % SZS output end CNFRefutation for theBenchmark.p
% 51.34/6.98  
% 51.34/6.98  ------                               Statistics
% 51.34/6.98  
% 51.34/6.98  ------ General
% 51.34/6.98  
% 51.34/6.98  abstr_ref_over_cycles:                  0
% 51.34/6.98  abstr_ref_under_cycles:                 0
% 51.34/6.98  gc_basic_clause_elim:                   0
% 51.34/6.98  forced_gc_time:                         0
% 51.34/6.98  parsing_time:                           0.008
% 51.34/6.98  unif_index_cands_time:                  0.
% 51.34/6.98  unif_index_add_time:                    0.
% 51.34/6.98  orderings_time:                         0.
% 51.34/6.98  out_proof_time:                         0.016
% 51.34/6.98  total_time:                             6.173
% 51.34/6.98  num_of_symbols:                         45
% 51.34/6.98  num_of_terms:                           164054
% 51.34/6.98  
% 51.34/6.98  ------ Preprocessing
% 51.34/6.98  
% 51.34/6.98  num_of_splits:                          0
% 51.34/6.98  num_of_split_atoms:                     0
% 51.34/6.98  num_of_reused_defs:                     0
% 51.34/6.98  num_eq_ax_congr_red:                    17
% 51.34/6.98  num_of_sem_filtered_clauses:            1
% 51.34/6.98  num_of_subtypes:                        3
% 51.34/6.98  monotx_restored_types:                  0
% 51.34/6.98  sat_num_of_epr_types:                   0
% 51.34/6.98  sat_num_of_non_cyclic_types:            0
% 51.34/6.98  sat_guarded_non_collapsed_types:        1
% 51.34/6.98  num_pure_diseq_elim:                    0
% 51.34/6.98  simp_replaced_by:                       0
% 51.34/6.98  res_preprocessed:                       85
% 51.34/6.98  prep_upred:                             0
% 51.34/6.98  prep_unflattend:                        0
% 51.34/6.98  smt_new_axioms:                         0
% 51.34/6.98  pred_elim_cands:                        2
% 51.34/6.98  pred_elim:                              1
% 51.34/6.98  pred_elim_cl:                           2
% 51.34/6.98  pred_elim_cycles:                       3
% 51.34/6.98  merged_defs:                            0
% 51.34/6.98  merged_defs_ncl:                        0
% 51.34/6.98  bin_hyper_res:                          0
% 51.34/6.98  prep_cycles:                            4
% 51.34/6.98  pred_elim_time:                         0.
% 51.34/6.98  splitting_time:                         0.
% 51.34/6.98  sem_filter_time:                        0.
% 51.34/6.98  monotx_time:                            0.
% 51.34/6.98  subtype_inf_time:                       0.
% 51.34/6.98  
% 51.34/6.98  ------ Problem properties
% 51.34/6.98  
% 51.34/6.98  clauses:                                14
% 51.34/6.98  conjectures:                            3
% 51.34/6.98  epr:                                    3
% 51.34/6.98  horn:                                   14
% 51.34/6.98  ground:                                 3
% 51.34/6.98  unary:                                  5
% 51.34/6.98  binary:                                 6
% 51.34/6.98  lits:                                   26
% 51.34/6.98  lits_eq:                                7
% 51.34/6.98  fd_pure:                                0
% 51.34/6.98  fd_pseudo:                              0
% 51.34/6.98  fd_cond:                                0
% 51.34/6.98  fd_pseudo_cond:                         0
% 51.34/6.98  ac_symbols:                             0
% 51.34/6.98  
% 51.34/6.98  ------ Propositional Solver
% 51.34/6.98  
% 51.34/6.98  prop_solver_calls:                      62
% 51.34/6.98  prop_fast_solver_calls:                 1654
% 51.34/6.98  smt_solver_calls:                       0
% 51.34/6.98  smt_fast_solver_calls:                  0
% 51.34/6.98  prop_num_of_clauses:                    61301
% 51.34/6.98  prop_preprocess_simplified:             61662
% 51.34/6.98  prop_fo_subsumed:                       37
% 51.34/6.98  prop_solver_time:                       0.
% 51.34/6.98  smt_solver_time:                        0.
% 51.34/6.98  smt_fast_solver_time:                   0.
% 51.34/6.98  prop_fast_solver_time:                  0.
% 51.34/6.98  prop_unsat_core_time:                   0.005
% 51.34/6.98  
% 51.34/6.98  ------ QBF
% 51.34/6.98  
% 51.34/6.98  qbf_q_res:                              0
% 51.34/6.98  qbf_num_tautologies:                    0
% 51.34/6.98  qbf_prep_cycles:                        0
% 51.34/6.98  
% 51.34/6.98  ------ BMC1
% 51.34/6.98  
% 51.34/6.98  bmc1_current_bound:                     -1
% 51.34/6.98  bmc1_last_solved_bound:                 -1
% 51.34/6.98  bmc1_unsat_core_size:                   -1
% 51.34/6.98  bmc1_unsat_core_parents_size:           -1
% 51.34/6.98  bmc1_merge_next_fun:                    0
% 51.34/6.98  bmc1_unsat_core_clauses_time:           0.
% 51.34/6.98  
% 51.34/6.98  ------ Instantiation
% 51.34/6.98  
% 51.34/6.98  inst_num_of_clauses:                    3150
% 51.34/6.98  inst_num_in_passive:                    1961
% 51.34/6.98  inst_num_in_active:                     3946
% 51.34/6.98  inst_num_in_unprocessed:                130
% 51.34/6.98  inst_num_of_loops:                      4088
% 51.34/6.98  inst_num_of_learning_restarts:          1
% 51.34/6.98  inst_num_moves_active_passive:          135
% 51.34/6.98  inst_lit_activity:                      0
% 51.34/6.98  inst_lit_activity_moves:                0
% 51.34/6.98  inst_num_tautologies:                   0
% 51.34/6.98  inst_num_prop_implied:                  0
% 51.34/6.98  inst_num_existing_simplified:           0
% 51.34/6.98  inst_num_eq_res_simplified:             0
% 51.34/6.98  inst_num_child_elim:                    0
% 51.34/6.98  inst_num_of_dismatching_blockings:      26719
% 51.34/6.98  inst_num_of_non_proper_insts:           28878
% 51.34/6.98  inst_num_of_duplicates:                 0
% 51.34/6.98  inst_inst_num_from_inst_to_res:         0
% 51.34/6.98  inst_dismatching_checking_time:         0.
% 51.34/6.98  
% 51.34/6.98  ------ Resolution
% 51.34/6.98  
% 51.34/6.98  res_num_of_clauses:                     27
% 51.34/6.98  res_num_in_passive:                     27
% 51.34/6.98  res_num_in_active:                      0
% 51.34/6.98  res_num_of_loops:                       89
% 51.34/6.98  res_forward_subset_subsumed:            1840
% 51.34/6.98  res_backward_subset_subsumed:           10
% 51.34/6.98  res_forward_subsumed:                   0
% 51.34/6.98  res_backward_subsumed:                  0
% 51.34/6.98  res_forward_subsumption_resolution:     0
% 51.34/6.98  res_backward_subsumption_resolution:    0
% 51.34/6.98  res_clause_to_clause_subsumption:       125173
% 51.34/6.98  res_orphan_elimination:                 0
% 51.34/6.98  res_tautology_del:                      5143
% 51.34/6.98  res_num_eq_res_simplified:              0
% 51.34/6.98  res_num_sel_changes:                    0
% 51.34/6.98  res_moves_from_active_to_pass:          0
% 51.34/6.98  
% 51.34/6.98  ------ Superposition
% 51.34/6.98  
% 51.34/6.98  sup_time_total:                         0.
% 51.34/6.98  sup_time_generating:                    0.
% 51.34/6.98  sup_time_sim_full:                      0.
% 51.34/6.98  sup_time_sim_immed:                     0.
% 51.34/6.98  
% 51.34/6.98  sup_num_of_clauses:                     13656
% 51.34/6.98  sup_num_in_active:                      735
% 51.34/6.98  sup_num_in_passive:                     12921
% 51.34/6.98  sup_num_of_loops:                       816
% 51.34/6.98  sup_fw_superposition:                   22605
% 51.34/6.98  sup_bw_superposition:                   12281
% 51.34/6.98  sup_immediate_simplified:               5557
% 51.34/6.98  sup_given_eliminated:                   0
% 51.34/6.98  comparisons_done:                       0
% 51.34/6.98  comparisons_avoided:                    0
% 51.34/6.98  
% 51.34/6.98  ------ Simplifications
% 51.34/6.98  
% 51.34/6.98  
% 51.34/6.98  sim_fw_subset_subsumed:                 712
% 51.34/6.98  sim_bw_subset_subsumed:                 642
% 51.34/6.98  sim_fw_subsumed:                        2846
% 51.34/6.98  sim_bw_subsumed:                        96
% 51.34/6.98  sim_fw_subsumption_res:                 0
% 51.34/6.98  sim_bw_subsumption_res:                 0
% 51.34/6.98  sim_tautology_del:                      74
% 51.34/6.98  sim_eq_tautology_del:                   132
% 51.34/6.98  sim_eq_res_simp:                        0
% 51.34/6.98  sim_fw_demodulated:                     637
% 51.34/6.98  sim_bw_demodulated:                     38
% 51.34/6.98  sim_light_normalised:                   1571
% 51.34/6.98  sim_joinable_taut:                      0
% 51.34/6.98  sim_joinable_simp:                      0
% 51.34/6.98  sim_ac_normalised:                      0
% 51.34/6.98  sim_smt_subsumption:                    0
% 51.34/6.98  
%------------------------------------------------------------------------------
