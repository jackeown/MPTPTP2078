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
% DateTime   : Thu Dec  3 11:45:53 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 163 expanded)
%              Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 222 expanded)
%              Number of equality atoms :   97 ( 171 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f54])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f63,plain,(
    ! [X0,X1] : o_0_0_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f44,f32,f59])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f57])).

fof(f61,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f35,f32,f58,f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f34,f32,f58])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f50,f32,f32])).

fof(f18,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f18])).

fof(f27,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK1,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    k1_xboole_0 != k8_relat_1(sK1,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f30])).

fof(f51,plain,(
    k1_xboole_0 != k8_relat_1(sK1,k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    o_0_0_xboole_0 != k8_relat_1(sK1,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f51,f32,f32])).

cnf(c_3,plain,
    ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_589,plain,
    ( k2_xboole_0(k6_enumset1(sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0)),o_0_0_xboole_0) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_569,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,sK1))) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_436,plain,
    ( r1_tarski(X0,sK1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_438,plain,
    ( r1_tarski(o_0_0_xboole_0,sK1)
    | k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,sK1))) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_232,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_370,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X1)
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_409,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_relat_1(o_0_0_xboole_0),sK1)
    | k2_relat_1(o_0_0_xboole_0) != X0 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_411,plain,
    ( r1_tarski(k2_relat_1(o_0_0_xboole_0),sK1)
    | ~ r1_tarski(o_0_0_xboole_0,sK1)
    | k2_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_6,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_391,plain,
    ( ~ r1_tarski(k2_relat_1(o_0_0_xboole_0),sK1)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | k8_relat_1(sK1,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_231,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_368,plain,
    ( k8_relat_1(sK1,o_0_0_xboole_0) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k8_relat_1(sK1,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_369,plain,
    ( k8_relat_1(sK1,o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k8_relat_1(sK1,o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_230,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_249,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_78,plain,
    ( v1_relat_1(X0)
    | X0 != X1
    | k2_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1) = X1
    | sK0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_79,plain,
    ( v1_relat_1(X0)
    | k2_xboole_0(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_78])).

cnf(c_81,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | k2_xboole_0(k6_enumset1(sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0)),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_7,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9,negated_conjecture,
    ( o_0_0_xboole_0 != k8_relat_1(sK1,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_589,c_569,c_438,c_411,c_391,c_369,c_249,c_81,c_7,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.77/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.77/1.03  
% 0.77/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.77/1.03  
% 0.77/1.03  ------  iProver source info
% 0.77/1.03  
% 0.77/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.77/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.77/1.03  git: non_committed_changes: false
% 0.77/1.03  git: last_make_outside_of_git: false
% 0.77/1.03  
% 0.77/1.03  ------ 
% 0.77/1.03  
% 0.77/1.03  ------ Input Options
% 0.77/1.03  
% 0.77/1.03  --out_options                           all
% 0.77/1.03  --tptp_safe_out                         true
% 0.77/1.03  --problem_path                          ""
% 0.77/1.03  --include_path                          ""
% 0.77/1.03  --clausifier                            res/vclausify_rel
% 0.77/1.03  --clausifier_options                    --mode clausify
% 0.77/1.03  --stdin                                 false
% 0.77/1.03  --stats_out                             all
% 0.77/1.03  
% 0.77/1.03  ------ General Options
% 0.77/1.03  
% 0.77/1.03  --fof                                   false
% 0.77/1.03  --time_out_real                         305.
% 0.77/1.03  --time_out_virtual                      -1.
% 0.77/1.03  --symbol_type_check                     false
% 0.77/1.03  --clausify_out                          false
% 0.77/1.03  --sig_cnt_out                           false
% 0.77/1.03  --trig_cnt_out                          false
% 0.77/1.03  --trig_cnt_out_tolerance                1.
% 0.77/1.03  --trig_cnt_out_sk_spl                   false
% 0.77/1.03  --abstr_cl_out                          false
% 0.77/1.03  
% 0.77/1.03  ------ Global Options
% 0.77/1.03  
% 0.77/1.03  --schedule                              default
% 0.77/1.03  --add_important_lit                     false
% 0.77/1.03  --prop_solver_per_cl                    1000
% 0.77/1.03  --min_unsat_core                        false
% 0.77/1.03  --soft_assumptions                      false
% 0.77/1.03  --soft_lemma_size                       3
% 0.77/1.03  --prop_impl_unit_size                   0
% 0.77/1.03  --prop_impl_unit                        []
% 0.77/1.03  --share_sel_clauses                     true
% 0.77/1.03  --reset_solvers                         false
% 0.77/1.03  --bc_imp_inh                            [conj_cone]
% 0.77/1.03  --conj_cone_tolerance                   3.
% 0.77/1.03  --extra_neg_conj                        none
% 0.77/1.03  --large_theory_mode                     true
% 0.77/1.03  --prolific_symb_bound                   200
% 0.77/1.03  --lt_threshold                          2000
% 0.77/1.03  --clause_weak_htbl                      true
% 0.77/1.03  --gc_record_bc_elim                     false
% 0.77/1.03  
% 0.77/1.03  ------ Preprocessing Options
% 0.77/1.03  
% 0.77/1.03  --preprocessing_flag                    true
% 0.77/1.03  --time_out_prep_mult                    0.1
% 0.77/1.03  --splitting_mode                        input
% 0.77/1.03  --splitting_grd                         true
% 0.77/1.03  --splitting_cvd                         false
% 0.77/1.03  --splitting_cvd_svl                     false
% 0.77/1.03  --splitting_nvd                         32
% 0.77/1.03  --sub_typing                            true
% 0.77/1.03  --prep_gs_sim                           true
% 0.77/1.03  --prep_unflatten                        true
% 0.77/1.03  --prep_res_sim                          true
% 0.77/1.03  --prep_upred                            true
% 0.77/1.03  --prep_sem_filter                       exhaustive
% 0.77/1.03  --prep_sem_filter_out                   false
% 0.77/1.03  --pred_elim                             true
% 0.77/1.03  --res_sim_input                         true
% 0.77/1.03  --eq_ax_congr_red                       true
% 0.77/1.03  --pure_diseq_elim                       true
% 0.77/1.03  --brand_transform                       false
% 0.77/1.03  --non_eq_to_eq                          false
% 0.77/1.03  --prep_def_merge                        true
% 0.77/1.03  --prep_def_merge_prop_impl              false
% 0.77/1.03  --prep_def_merge_mbd                    true
% 0.77/1.03  --prep_def_merge_tr_red                 false
% 0.77/1.03  --prep_def_merge_tr_cl                  false
% 0.77/1.03  --smt_preprocessing                     true
% 0.77/1.03  --smt_ac_axioms                         fast
% 0.77/1.03  --preprocessed_out                      false
% 0.77/1.03  --preprocessed_stats                    false
% 0.77/1.03  
% 0.77/1.03  ------ Abstraction refinement Options
% 0.77/1.03  
% 0.77/1.03  --abstr_ref                             []
% 0.77/1.03  --abstr_ref_prep                        false
% 0.77/1.03  --abstr_ref_until_sat                   false
% 0.77/1.03  --abstr_ref_sig_restrict                funpre
% 0.77/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.77/1.03  --abstr_ref_under                       []
% 0.77/1.03  
% 0.77/1.03  ------ SAT Options
% 0.77/1.03  
% 0.77/1.03  --sat_mode                              false
% 0.77/1.03  --sat_fm_restart_options                ""
% 0.77/1.03  --sat_gr_def                            false
% 0.77/1.03  --sat_epr_types                         true
% 0.77/1.03  --sat_non_cyclic_types                  false
% 0.77/1.03  --sat_finite_models                     false
% 0.77/1.03  --sat_fm_lemmas                         false
% 0.77/1.03  --sat_fm_prep                           false
% 0.77/1.03  --sat_fm_uc_incr                        true
% 0.77/1.03  --sat_out_model                         small
% 0.77/1.03  --sat_out_clauses                       false
% 0.77/1.03  
% 0.77/1.03  ------ QBF Options
% 0.77/1.03  
% 0.77/1.03  --qbf_mode                              false
% 0.77/1.03  --qbf_elim_univ                         false
% 0.77/1.03  --qbf_dom_inst                          none
% 0.77/1.03  --qbf_dom_pre_inst                      false
% 0.77/1.03  --qbf_sk_in                             false
% 0.77/1.03  --qbf_pred_elim                         true
% 0.77/1.03  --qbf_split                             512
% 0.77/1.03  
% 0.77/1.03  ------ BMC1 Options
% 0.77/1.03  
% 0.77/1.03  --bmc1_incremental                      false
% 0.77/1.03  --bmc1_axioms                           reachable_all
% 0.77/1.03  --bmc1_min_bound                        0
% 0.77/1.03  --bmc1_max_bound                        -1
% 0.77/1.03  --bmc1_max_bound_default                -1
% 0.77/1.03  --bmc1_symbol_reachability              true
% 0.77/1.03  --bmc1_property_lemmas                  false
% 0.77/1.03  --bmc1_k_induction                      false
% 0.77/1.03  --bmc1_non_equiv_states                 false
% 0.77/1.03  --bmc1_deadlock                         false
% 0.77/1.03  --bmc1_ucm                              false
% 0.77/1.03  --bmc1_add_unsat_core                   none
% 0.77/1.03  --bmc1_unsat_core_children              false
% 0.77/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.77/1.03  --bmc1_out_stat                         full
% 0.77/1.03  --bmc1_ground_init                      false
% 0.77/1.03  --bmc1_pre_inst_next_state              false
% 0.77/1.03  --bmc1_pre_inst_state                   false
% 0.77/1.03  --bmc1_pre_inst_reach_state             false
% 0.77/1.03  --bmc1_out_unsat_core                   false
% 0.77/1.03  --bmc1_aig_witness_out                  false
% 0.77/1.03  --bmc1_verbose                          false
% 0.77/1.03  --bmc1_dump_clauses_tptp                false
% 0.77/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.77/1.03  --bmc1_dump_file                        -
% 0.77/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.77/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.77/1.03  --bmc1_ucm_extend_mode                  1
% 0.77/1.03  --bmc1_ucm_init_mode                    2
% 0.77/1.03  --bmc1_ucm_cone_mode                    none
% 0.77/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.77/1.03  --bmc1_ucm_relax_model                  4
% 0.77/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.77/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.77/1.03  --bmc1_ucm_layered_model                none
% 0.77/1.03  --bmc1_ucm_max_lemma_size               10
% 0.77/1.03  
% 0.77/1.03  ------ AIG Options
% 0.77/1.03  
% 0.77/1.03  --aig_mode                              false
% 0.77/1.03  
% 0.77/1.03  ------ Instantiation Options
% 0.77/1.03  
% 0.77/1.03  --instantiation_flag                    true
% 0.77/1.03  --inst_sos_flag                         false
% 0.77/1.03  --inst_sos_phase                        true
% 0.77/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.77/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.77/1.03  --inst_lit_sel_side                     num_symb
% 0.77/1.03  --inst_solver_per_active                1400
% 0.77/1.03  --inst_solver_calls_frac                1.
% 0.77/1.03  --inst_passive_queue_type               priority_queues
% 0.77/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.77/1.03  --inst_passive_queues_freq              [25;2]
% 0.77/1.03  --inst_dismatching                      true
% 0.77/1.03  --inst_eager_unprocessed_to_passive     true
% 0.77/1.03  --inst_prop_sim_given                   true
% 0.77/1.03  --inst_prop_sim_new                     false
% 0.77/1.03  --inst_subs_new                         false
% 0.77/1.03  --inst_eq_res_simp                      false
% 0.77/1.03  --inst_subs_given                       false
% 0.77/1.03  --inst_orphan_elimination               true
% 0.77/1.03  --inst_learning_loop_flag               true
% 0.77/1.03  --inst_learning_start                   3000
% 0.77/1.03  --inst_learning_factor                  2
% 0.77/1.03  --inst_start_prop_sim_after_learn       3
% 0.77/1.03  --inst_sel_renew                        solver
% 0.77/1.03  --inst_lit_activity_flag                true
% 0.77/1.03  --inst_restr_to_given                   false
% 0.77/1.03  --inst_activity_threshold               500
% 0.77/1.03  --inst_out_proof                        true
% 0.77/1.03  
% 0.77/1.03  ------ Resolution Options
% 0.77/1.03  
% 0.77/1.03  --resolution_flag                       true
% 0.77/1.03  --res_lit_sel                           adaptive
% 0.77/1.03  --res_lit_sel_side                      none
% 0.77/1.03  --res_ordering                          kbo
% 0.77/1.03  --res_to_prop_solver                    active
% 0.77/1.03  --res_prop_simpl_new                    false
% 0.77/1.03  --res_prop_simpl_given                  true
% 0.77/1.03  --res_passive_queue_type                priority_queues
% 0.77/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.77/1.03  --res_passive_queues_freq               [15;5]
% 0.77/1.03  --res_forward_subs                      full
% 0.77/1.03  --res_backward_subs                     full
% 0.77/1.03  --res_forward_subs_resolution           true
% 0.77/1.03  --res_backward_subs_resolution          true
% 0.77/1.03  --res_orphan_elimination                true
% 0.77/1.03  --res_time_limit                        2.
% 0.77/1.03  --res_out_proof                         true
% 0.77/1.03  
% 0.77/1.03  ------ Superposition Options
% 0.77/1.03  
% 0.77/1.03  --superposition_flag                    true
% 0.77/1.03  --sup_passive_queue_type                priority_queues
% 0.77/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.77/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.77/1.03  --demod_completeness_check              fast
% 0.77/1.03  --demod_use_ground                      true
% 0.77/1.03  --sup_to_prop_solver                    passive
% 0.77/1.03  --sup_prop_simpl_new                    true
% 0.77/1.03  --sup_prop_simpl_given                  true
% 0.77/1.03  --sup_fun_splitting                     false
% 0.77/1.03  --sup_smt_interval                      50000
% 0.77/1.03  
% 0.77/1.03  ------ Superposition Simplification Setup
% 0.77/1.03  
% 0.77/1.03  --sup_indices_passive                   []
% 0.77/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.77/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.03  --sup_full_bw                           [BwDemod]
% 0.77/1.03  --sup_immed_triv                        [TrivRules]
% 0.77/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.77/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.03  --sup_immed_bw_main                     []
% 0.77/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.77/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/1.03  
% 0.77/1.03  ------ Combination Options
% 0.77/1.03  
% 0.77/1.03  --comb_res_mult                         3
% 0.77/1.03  --comb_sup_mult                         2
% 0.77/1.03  --comb_inst_mult                        10
% 0.77/1.03  
% 0.77/1.03  ------ Debug Options
% 0.77/1.03  
% 0.77/1.03  --dbg_backtrace                         false
% 0.77/1.03  --dbg_dump_prop_clauses                 false
% 0.77/1.03  --dbg_dump_prop_clauses_file            -
% 0.77/1.03  --dbg_out_stat                          false
% 0.77/1.03  ------ Parsing...
% 0.77/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.77/1.03  
% 0.77/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.77/1.03  
% 0.77/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.77/1.03  
% 0.77/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.77/1.03  ------ Proving...
% 0.77/1.03  ------ Problem Properties 
% 0.77/1.03  
% 0.77/1.03  
% 0.77/1.03  clauses                                 9
% 0.77/1.03  conjectures                             1
% 0.77/1.03  EPR                                     0
% 0.77/1.03  Horn                                    8
% 0.77/1.03  unary                                   5
% 0.77/1.03  binary                                  3
% 0.77/1.03  lits                                    14
% 0.77/1.03  lits eq                                 9
% 0.77/1.03  fd_pure                                 0
% 0.77/1.03  fd_pseudo                               0
% 0.77/1.03  fd_cond                                 0
% 0.77/1.03  fd_pseudo_cond                          0
% 0.77/1.03  AC symbols                              0
% 0.77/1.03  
% 0.77/1.03  ------ Schedule dynamic 5 is on 
% 0.77/1.03  
% 0.77/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.77/1.03  
% 0.77/1.03  
% 0.77/1.03  ------ 
% 0.77/1.03  Current options:
% 0.77/1.03  ------ 
% 0.77/1.03  
% 0.77/1.03  ------ Input Options
% 0.77/1.03  
% 0.77/1.03  --out_options                           all
% 0.77/1.03  --tptp_safe_out                         true
% 0.77/1.03  --problem_path                          ""
% 0.77/1.03  --include_path                          ""
% 0.77/1.03  --clausifier                            res/vclausify_rel
% 0.77/1.03  --clausifier_options                    --mode clausify
% 0.77/1.03  --stdin                                 false
% 0.77/1.03  --stats_out                             all
% 0.77/1.03  
% 0.77/1.03  ------ General Options
% 0.77/1.03  
% 0.77/1.03  --fof                                   false
% 0.77/1.03  --time_out_real                         305.
% 0.77/1.03  --time_out_virtual                      -1.
% 0.77/1.03  --symbol_type_check                     false
% 0.77/1.03  --clausify_out                          false
% 0.77/1.03  --sig_cnt_out                           false
% 0.77/1.03  --trig_cnt_out                          false
% 0.77/1.03  --trig_cnt_out_tolerance                1.
% 0.77/1.03  --trig_cnt_out_sk_spl                   false
% 0.77/1.03  --abstr_cl_out                          false
% 0.77/1.03  
% 0.77/1.03  ------ Global Options
% 0.77/1.03  
% 0.77/1.03  --schedule                              default
% 0.77/1.03  --add_important_lit                     false
% 0.77/1.03  --prop_solver_per_cl                    1000
% 0.77/1.03  --min_unsat_core                        false
% 0.77/1.03  --soft_assumptions                      false
% 0.77/1.03  --soft_lemma_size                       3
% 0.77/1.03  --prop_impl_unit_size                   0
% 0.77/1.03  --prop_impl_unit                        []
% 0.77/1.03  --share_sel_clauses                     true
% 0.77/1.03  --reset_solvers                         false
% 0.77/1.03  --bc_imp_inh                            [conj_cone]
% 0.77/1.03  --conj_cone_tolerance                   3.
% 0.77/1.03  --extra_neg_conj                        none
% 0.77/1.03  --large_theory_mode                     true
% 0.77/1.03  --prolific_symb_bound                   200
% 0.77/1.03  --lt_threshold                          2000
% 0.77/1.03  --clause_weak_htbl                      true
% 0.77/1.03  --gc_record_bc_elim                     false
% 0.77/1.03  
% 0.77/1.03  ------ Preprocessing Options
% 0.77/1.03  
% 0.77/1.03  --preprocessing_flag                    true
% 0.77/1.03  --time_out_prep_mult                    0.1
% 0.77/1.03  --splitting_mode                        input
% 0.77/1.03  --splitting_grd                         true
% 0.77/1.03  --splitting_cvd                         false
% 0.77/1.03  --splitting_cvd_svl                     false
% 0.77/1.03  --splitting_nvd                         32
% 0.77/1.03  --sub_typing                            true
% 0.77/1.03  --prep_gs_sim                           true
% 0.77/1.03  --prep_unflatten                        true
% 0.77/1.03  --prep_res_sim                          true
% 0.77/1.03  --prep_upred                            true
% 0.77/1.03  --prep_sem_filter                       exhaustive
% 0.77/1.03  --prep_sem_filter_out                   false
% 0.77/1.03  --pred_elim                             true
% 0.77/1.03  --res_sim_input                         true
% 0.77/1.04  --eq_ax_congr_red                       true
% 0.77/1.04  --pure_diseq_elim                       true
% 0.77/1.04  --brand_transform                       false
% 0.77/1.04  --non_eq_to_eq                          false
% 0.77/1.04  --prep_def_merge                        true
% 0.77/1.04  --prep_def_merge_prop_impl              false
% 0.77/1.04  --prep_def_merge_mbd                    true
% 0.77/1.04  --prep_def_merge_tr_red                 false
% 0.77/1.04  --prep_def_merge_tr_cl                  false
% 0.77/1.04  --smt_preprocessing                     true
% 0.77/1.04  --smt_ac_axioms                         fast
% 0.77/1.04  --preprocessed_out                      false
% 0.77/1.04  --preprocessed_stats                    false
% 0.77/1.04  
% 0.77/1.04  ------ Abstraction refinement Options
% 0.77/1.04  
% 0.77/1.04  --abstr_ref                             []
% 0.77/1.04  --abstr_ref_prep                        false
% 0.77/1.04  --abstr_ref_until_sat                   false
% 0.77/1.04  --abstr_ref_sig_restrict                funpre
% 0.77/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.77/1.04  --abstr_ref_under                       []
% 0.77/1.04  
% 0.77/1.04  ------ SAT Options
% 0.77/1.04  
% 0.77/1.04  --sat_mode                              false
% 0.77/1.04  --sat_fm_restart_options                ""
% 0.77/1.04  --sat_gr_def                            false
% 0.77/1.04  --sat_epr_types                         true
% 0.77/1.04  --sat_non_cyclic_types                  false
% 0.77/1.04  --sat_finite_models                     false
% 0.77/1.04  --sat_fm_lemmas                         false
% 0.77/1.04  --sat_fm_prep                           false
% 0.77/1.04  --sat_fm_uc_incr                        true
% 0.77/1.04  --sat_out_model                         small
% 0.77/1.04  --sat_out_clauses                       false
% 0.77/1.04  
% 0.77/1.04  ------ QBF Options
% 0.77/1.04  
% 0.77/1.04  --qbf_mode                              false
% 0.77/1.04  --qbf_elim_univ                         false
% 0.77/1.04  --qbf_dom_inst                          none
% 0.77/1.04  --qbf_dom_pre_inst                      false
% 0.77/1.04  --qbf_sk_in                             false
% 0.77/1.04  --qbf_pred_elim                         true
% 0.77/1.04  --qbf_split                             512
% 0.77/1.04  
% 0.77/1.04  ------ BMC1 Options
% 0.77/1.04  
% 0.77/1.04  --bmc1_incremental                      false
% 0.77/1.04  --bmc1_axioms                           reachable_all
% 0.77/1.04  --bmc1_min_bound                        0
% 0.77/1.04  --bmc1_max_bound                        -1
% 0.77/1.04  --bmc1_max_bound_default                -1
% 0.77/1.04  --bmc1_symbol_reachability              true
% 0.77/1.04  --bmc1_property_lemmas                  false
% 0.77/1.04  --bmc1_k_induction                      false
% 0.77/1.04  --bmc1_non_equiv_states                 false
% 0.77/1.04  --bmc1_deadlock                         false
% 0.77/1.04  --bmc1_ucm                              false
% 0.77/1.04  --bmc1_add_unsat_core                   none
% 0.77/1.04  --bmc1_unsat_core_children              false
% 0.77/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.77/1.04  --bmc1_out_stat                         full
% 0.77/1.04  --bmc1_ground_init                      false
% 0.77/1.04  --bmc1_pre_inst_next_state              false
% 0.77/1.04  --bmc1_pre_inst_state                   false
% 0.77/1.04  --bmc1_pre_inst_reach_state             false
% 0.77/1.04  --bmc1_out_unsat_core                   false
% 0.77/1.04  --bmc1_aig_witness_out                  false
% 0.77/1.04  --bmc1_verbose                          false
% 0.77/1.04  --bmc1_dump_clauses_tptp                false
% 0.77/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.77/1.04  --bmc1_dump_file                        -
% 0.77/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.77/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.77/1.04  --bmc1_ucm_extend_mode                  1
% 0.77/1.04  --bmc1_ucm_init_mode                    2
% 0.77/1.04  --bmc1_ucm_cone_mode                    none
% 0.77/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.77/1.04  --bmc1_ucm_relax_model                  4
% 0.77/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.77/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.77/1.04  --bmc1_ucm_layered_model                none
% 0.77/1.04  --bmc1_ucm_max_lemma_size               10
% 0.77/1.04  
% 0.77/1.04  ------ AIG Options
% 0.77/1.04  
% 0.77/1.04  --aig_mode                              false
% 0.77/1.04  
% 0.77/1.04  ------ Instantiation Options
% 0.77/1.04  
% 0.77/1.04  --instantiation_flag                    true
% 0.77/1.04  --inst_sos_flag                         false
% 0.77/1.04  --inst_sos_phase                        true
% 0.77/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.77/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.77/1.04  --inst_lit_sel_side                     none
% 0.77/1.04  --inst_solver_per_active                1400
% 0.77/1.04  --inst_solver_calls_frac                1.
% 0.77/1.04  --inst_passive_queue_type               priority_queues
% 0.77/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.77/1.04  --inst_passive_queues_freq              [25;2]
% 0.77/1.04  --inst_dismatching                      true
% 0.77/1.04  --inst_eager_unprocessed_to_passive     true
% 0.77/1.04  --inst_prop_sim_given                   true
% 0.77/1.04  --inst_prop_sim_new                     false
% 0.77/1.04  --inst_subs_new                         false
% 0.77/1.04  --inst_eq_res_simp                      false
% 0.77/1.04  --inst_subs_given                       false
% 0.77/1.04  --inst_orphan_elimination               true
% 0.77/1.04  --inst_learning_loop_flag               true
% 0.77/1.04  --inst_learning_start                   3000
% 0.77/1.04  --inst_learning_factor                  2
% 0.77/1.04  --inst_start_prop_sim_after_learn       3
% 0.77/1.04  --inst_sel_renew                        solver
% 0.77/1.04  --inst_lit_activity_flag                true
% 0.77/1.04  --inst_restr_to_given                   false
% 0.77/1.04  --inst_activity_threshold               500
% 0.77/1.04  --inst_out_proof                        true
% 0.77/1.04  
% 0.77/1.04  ------ Resolution Options
% 0.77/1.04  
% 0.77/1.04  --resolution_flag                       false
% 0.77/1.04  --res_lit_sel                           adaptive
% 0.77/1.04  --res_lit_sel_side                      none
% 0.77/1.04  --res_ordering                          kbo
% 0.77/1.04  --res_to_prop_solver                    active
% 0.77/1.04  --res_prop_simpl_new                    false
% 0.77/1.04  --res_prop_simpl_given                  true
% 0.77/1.04  --res_passive_queue_type                priority_queues
% 0.77/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.77/1.04  --res_passive_queues_freq               [15;5]
% 0.77/1.04  --res_forward_subs                      full
% 0.77/1.04  --res_backward_subs                     full
% 0.77/1.04  --res_forward_subs_resolution           true
% 0.77/1.04  --res_backward_subs_resolution          true
% 0.77/1.04  --res_orphan_elimination                true
% 0.77/1.04  --res_time_limit                        2.
% 0.77/1.04  --res_out_proof                         true
% 0.77/1.04  
% 0.77/1.04  ------ Superposition Options
% 0.77/1.04  
% 0.77/1.04  --superposition_flag                    true
% 0.77/1.04  --sup_passive_queue_type                priority_queues
% 0.77/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.77/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.77/1.04  --demod_completeness_check              fast
% 0.77/1.04  --demod_use_ground                      true
% 0.77/1.04  --sup_to_prop_solver                    passive
% 0.77/1.04  --sup_prop_simpl_new                    true
% 0.77/1.04  --sup_prop_simpl_given                  true
% 0.77/1.04  --sup_fun_splitting                     false
% 0.77/1.04  --sup_smt_interval                      50000
% 0.77/1.04  
% 0.77/1.04  ------ Superposition Simplification Setup
% 0.77/1.04  
% 0.77/1.04  --sup_indices_passive                   []
% 0.77/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.77/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.04  --sup_full_bw                           [BwDemod]
% 0.77/1.04  --sup_immed_triv                        [TrivRules]
% 0.77/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.77/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.04  --sup_immed_bw_main                     []
% 0.77/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.77/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/1.04  
% 0.77/1.04  ------ Combination Options
% 0.77/1.04  
% 0.77/1.04  --comb_res_mult                         3
% 0.77/1.04  --comb_sup_mult                         2
% 0.77/1.04  --comb_inst_mult                        10
% 0.77/1.04  
% 0.77/1.04  ------ Debug Options
% 0.77/1.04  
% 0.77/1.04  --dbg_backtrace                         false
% 0.77/1.04  --dbg_dump_prop_clauses                 false
% 0.77/1.04  --dbg_dump_prop_clauses_file            -
% 0.77/1.04  --dbg_out_stat                          false
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  ------ Proving...
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  % SZS status Theorem for theBenchmark.p
% 0.77/1.04  
% 0.77/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.77/1.04  
% 0.77/1.04  fof(f13,axiom,(
% 0.77/1.04    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f44,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f13])).
% 0.77/1.04  
% 0.77/1.04  fof(f1,axiom,(
% 0.77/1.04    k1_xboole_0 = o_0_0_xboole_0),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f32,plain,(
% 0.77/1.04    k1_xboole_0 = o_0_0_xboole_0),
% 0.77/1.04    inference(cnf_transformation,[],[f1])).
% 0.77/1.04  
% 0.77/1.04  fof(f5,axiom,(
% 0.77/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f36,plain,(
% 0.77/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f5])).
% 0.77/1.04  
% 0.77/1.04  fof(f6,axiom,(
% 0.77/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f37,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f6])).
% 0.77/1.04  
% 0.77/1.04  fof(f7,axiom,(
% 0.77/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f38,plain,(
% 0.77/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f7])).
% 0.77/1.04  
% 0.77/1.04  fof(f8,axiom,(
% 0.77/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f39,plain,(
% 0.77/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f8])).
% 0.77/1.04  
% 0.77/1.04  fof(f9,axiom,(
% 0.77/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f40,plain,(
% 0.77/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f9])).
% 0.77/1.04  
% 0.77/1.04  fof(f10,axiom,(
% 0.77/1.04    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f41,plain,(
% 0.77/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f10])).
% 0.77/1.04  
% 0.77/1.04  fof(f11,axiom,(
% 0.77/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f42,plain,(
% 0.77/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f11])).
% 0.77/1.04  
% 0.77/1.04  fof(f52,plain,(
% 0.77/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.77/1.04    inference(definition_unfolding,[],[f41,f42])).
% 0.77/1.04  
% 0.77/1.04  fof(f53,plain,(
% 0.77/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.77/1.04    inference(definition_unfolding,[],[f40,f52])).
% 0.77/1.04  
% 0.77/1.04  fof(f54,plain,(
% 0.77/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.77/1.04    inference(definition_unfolding,[],[f39,f53])).
% 0.77/1.04  
% 0.77/1.04  fof(f55,plain,(
% 0.77/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.77/1.04    inference(definition_unfolding,[],[f38,f54])).
% 0.77/1.04  
% 0.77/1.04  fof(f56,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.77/1.04    inference(definition_unfolding,[],[f37,f55])).
% 0.77/1.04  
% 0.77/1.04  fof(f59,plain,(
% 0.77/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.77/1.04    inference(definition_unfolding,[],[f36,f56])).
% 0.77/1.04  
% 0.77/1.04  fof(f63,plain,(
% 0.77/1.04    ( ! [X0,X1] : (o_0_0_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 0.77/1.04    inference(definition_unfolding,[],[f44,f32,f59])).
% 0.77/1.04  
% 0.77/1.04  fof(f4,axiom,(
% 0.77/1.04    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f35,plain,(
% 0.77/1.04    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f4])).
% 0.77/1.04  
% 0.77/1.04  fof(f2,axiom,(
% 0.77/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f33,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.77/1.04    inference(cnf_transformation,[],[f2])).
% 0.77/1.04  
% 0.77/1.04  fof(f14,axiom,(
% 0.77/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f45,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.77/1.04    inference(cnf_transformation,[],[f14])).
% 0.77/1.04  
% 0.77/1.04  fof(f57,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.77/1.04    inference(definition_unfolding,[],[f45,f56])).
% 0.77/1.04  
% 0.77/1.04  fof(f58,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.77/1.04    inference(definition_unfolding,[],[f33,f57])).
% 0.77/1.04  
% 0.77/1.04  fof(f61,plain,(
% 0.77/1.04    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0)))) )),
% 0.77/1.04    inference(definition_unfolding,[],[f35,f32,f58,f32])).
% 0.77/1.04  
% 0.77/1.04  fof(f3,axiom,(
% 0.77/1.04    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f21,plain,(
% 0.77/1.04    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) => r1_tarski(X0,X1))),
% 0.77/1.04    inference(unused_predicate_definition_removal,[],[f3])).
% 0.77/1.04  
% 0.77/1.04  fof(f22,plain,(
% 0.77/1.04    ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 0.77/1.04    inference(ennf_transformation,[],[f21])).
% 0.77/1.04  
% 0.77/1.04  fof(f34,plain,(
% 0.77/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f22])).
% 0.77/1.04  
% 0.77/1.04  fof(f60,plain,(
% 0.77/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | o_0_0_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.77/1.04    inference(definition_unfolding,[],[f34,f32,f58])).
% 0.77/1.04  
% 0.77/1.04  fof(f16,axiom,(
% 0.77/1.04    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f25,plain,(
% 0.77/1.04    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.77/1.04    inference(ennf_transformation,[],[f16])).
% 0.77/1.04  
% 0.77/1.04  fof(f26,plain,(
% 0.77/1.04    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.77/1.04    inference(flattening,[],[f25])).
% 0.77/1.04  
% 0.77/1.04  fof(f48,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f26])).
% 0.77/1.04  
% 0.77/1.04  fof(f12,axiom,(
% 0.77/1.04    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f23,plain,(
% 0.77/1.04    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.77/1.04    inference(ennf_transformation,[],[f12])).
% 0.77/1.04  
% 0.77/1.04  fof(f43,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f23])).
% 0.77/1.04  
% 0.77/1.04  fof(f62,plain,(
% 0.77/1.04    ( ! [X0,X1] : (k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.77/1.04    inference(definition_unfolding,[],[f43,f59])).
% 0.77/1.04  
% 0.77/1.04  fof(f15,axiom,(
% 0.77/1.04    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f20,plain,(
% 0.77/1.04    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.77/1.04    inference(unused_predicate_definition_removal,[],[f15])).
% 0.77/1.04  
% 0.77/1.04  fof(f24,plain,(
% 0.77/1.04    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.77/1.04    inference(ennf_transformation,[],[f20])).
% 0.77/1.04  
% 0.77/1.04  fof(f28,plain,(
% 0.77/1.04    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.77/1.04    introduced(choice_axiom,[])).
% 0.77/1.04  
% 0.77/1.04  fof(f29,plain,(
% 0.77/1.04    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.77/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).
% 0.77/1.04  
% 0.77/1.04  fof(f46,plain,(
% 0.77/1.04    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f29])).
% 0.77/1.04  
% 0.77/1.04  fof(f17,axiom,(
% 0.77/1.04    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f50,plain,(
% 0.77/1.04    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.77/1.04    inference(cnf_transformation,[],[f17])).
% 0.77/1.04  
% 0.77/1.04  fof(f64,plain,(
% 0.77/1.04    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 0.77/1.04    inference(definition_unfolding,[],[f50,f32,f32])).
% 0.77/1.04  
% 0.77/1.04  fof(f18,conjecture,(
% 0.77/1.04    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f19,negated_conjecture,(
% 0.77/1.04    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.77/1.04    inference(negated_conjecture,[],[f18])).
% 0.77/1.04  
% 0.77/1.04  fof(f27,plain,(
% 0.77/1.04    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.77/1.04    inference(ennf_transformation,[],[f19])).
% 0.77/1.04  
% 0.77/1.04  fof(f30,plain,(
% 0.77/1.04    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK1,k1_xboole_0)),
% 0.77/1.04    introduced(choice_axiom,[])).
% 0.77/1.04  
% 0.77/1.04  fof(f31,plain,(
% 0.77/1.04    k1_xboole_0 != k8_relat_1(sK1,k1_xboole_0)),
% 0.77/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f30])).
% 0.77/1.04  
% 0.77/1.04  fof(f51,plain,(
% 0.77/1.04    k1_xboole_0 != k8_relat_1(sK1,k1_xboole_0)),
% 0.77/1.04    inference(cnf_transformation,[],[f31])).
% 0.77/1.04  
% 0.77/1.04  fof(f66,plain,(
% 0.77/1.04    o_0_0_xboole_0 != k8_relat_1(sK1,o_0_0_xboole_0)),
% 0.77/1.04    inference(definition_unfolding,[],[f51,f32,f32])).
% 0.77/1.04  
% 0.77/1.04  cnf(c_3,plain,
% 0.77/1.04      ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != o_0_0_xboole_0 ),
% 0.77/1.04      inference(cnf_transformation,[],[f63]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_589,plain,
% 0.77/1.04      ( k2_xboole_0(k6_enumset1(sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0)),o_0_0_xboole_0) != o_0_0_xboole_0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_1,plain,
% 0.77/1.04      ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0))) = o_0_0_xboole_0 ),
% 0.77/1.04      inference(cnf_transformation,[],[f61]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_569,plain,
% 0.77/1.04      ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,sK1))) = o_0_0_xboole_0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_0,plain,
% 0.77/1.04      ( r1_tarski(X0,X1)
% 0.77/1.04      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != o_0_0_xboole_0 ),
% 0.77/1.04      inference(cnf_transformation,[],[f60]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_436,plain,
% 0.77/1.04      ( r1_tarski(X0,sK1)
% 0.77/1.04      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))) != o_0_0_xboole_0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_0]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_438,plain,
% 0.77/1.04      ( r1_tarski(o_0_0_xboole_0,sK1)
% 0.77/1.04      | k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,sK1))) != o_0_0_xboole_0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_436]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_232,plain,
% 0.77/1.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 0.77/1.04      theory(equality) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_370,plain,
% 0.77/1.04      ( ~ r1_tarski(X0,X1)
% 0.77/1.04      | r1_tarski(k2_relat_1(X2),X1)
% 0.77/1.04      | k2_relat_1(X2) != X0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_232]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_409,plain,
% 0.77/1.04      ( ~ r1_tarski(X0,sK1)
% 0.77/1.04      | r1_tarski(k2_relat_1(o_0_0_xboole_0),sK1)
% 0.77/1.04      | k2_relat_1(o_0_0_xboole_0) != X0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_370]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_411,plain,
% 0.77/1.04      ( r1_tarski(k2_relat_1(o_0_0_xboole_0),sK1)
% 0.77/1.04      | ~ r1_tarski(o_0_0_xboole_0,sK1)
% 0.77/1.04      | k2_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_409]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_6,plain,
% 0.77/1.04      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 0.77/1.04      | ~ v1_relat_1(X0)
% 0.77/1.04      | k8_relat_1(X1,X0) = X0 ),
% 0.77/1.04      inference(cnf_transformation,[],[f48]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_391,plain,
% 0.77/1.04      ( ~ r1_tarski(k2_relat_1(o_0_0_xboole_0),sK1)
% 0.77/1.04      | ~ v1_relat_1(o_0_0_xboole_0)
% 0.77/1.04      | k8_relat_1(sK1,o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_231,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_368,plain,
% 0.77/1.04      ( k8_relat_1(sK1,o_0_0_xboole_0) != X0
% 0.77/1.04      | o_0_0_xboole_0 != X0
% 0.77/1.04      | o_0_0_xboole_0 = k8_relat_1(sK1,o_0_0_xboole_0) ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_231]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_369,plain,
% 0.77/1.04      ( k8_relat_1(sK1,o_0_0_xboole_0) != o_0_0_xboole_0
% 0.77/1.04      | o_0_0_xboole_0 = k8_relat_1(sK1,o_0_0_xboole_0)
% 0.77/1.04      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_368]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_230,plain,( X0 = X0 ),theory(equality) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_249,plain,
% 0.77/1.04      ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_230]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_2,plain,
% 0.77/1.04      ( ~ r2_hidden(X0,X1)
% 0.77/1.04      | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1 ),
% 0.77/1.04      inference(cnf_transformation,[],[f62]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_5,plain,
% 0.77/1.04      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 0.77/1.04      inference(cnf_transformation,[],[f46]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_78,plain,
% 0.77/1.04      ( v1_relat_1(X0)
% 0.77/1.04      | X0 != X1
% 0.77/1.04      | k2_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1) = X1
% 0.77/1.04      | sK0(X0) != X2 ),
% 0.77/1.04      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_79,plain,
% 0.77/1.04      ( v1_relat_1(X0)
% 0.77/1.04      | k2_xboole_0(k6_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0)),X0) = X0 ),
% 0.77/1.04      inference(unflattening,[status(thm)],[c_78]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_81,plain,
% 0.77/1.04      ( v1_relat_1(o_0_0_xboole_0)
% 0.77/1.04      | k2_xboole_0(k6_enumset1(sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0),sK0(o_0_0_xboole_0)),o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 0.77/1.04      inference(instantiation,[status(thm)],[c_79]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_7,plain,
% 0.77/1.04      ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 0.77/1.04      inference(cnf_transformation,[],[f64]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(c_9,negated_conjecture,
% 0.77/1.04      ( o_0_0_xboole_0 != k8_relat_1(sK1,o_0_0_xboole_0) ),
% 0.77/1.04      inference(cnf_transformation,[],[f66]) ).
% 0.77/1.04  
% 0.77/1.04  cnf(contradiction,plain,
% 0.77/1.04      ( $false ),
% 0.77/1.04      inference(minisat,
% 0.77/1.04                [status(thm)],
% 0.77/1.04                [c_589,c_569,c_438,c_411,c_391,c_369,c_249,c_81,c_7,c_9]) ).
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.77/1.04  
% 0.77/1.04  ------                               Statistics
% 0.77/1.04  
% 0.77/1.04  ------ General
% 0.77/1.04  
% 0.77/1.04  abstr_ref_over_cycles:                  0
% 0.77/1.04  abstr_ref_under_cycles:                 0
% 0.77/1.04  gc_basic_clause_elim:                   0
% 0.77/1.04  forced_gc_time:                         0
% 0.77/1.04  parsing_time:                           0.008
% 0.77/1.04  unif_index_cands_time:                  0.
% 0.77/1.04  unif_index_add_time:                    0.
% 0.77/1.04  orderings_time:                         0.
% 0.77/1.04  out_proof_time:                         0.006
% 0.77/1.04  total_time:                             0.045
% 0.77/1.04  num_of_symbols:                         45
% 0.77/1.04  num_of_terms:                           698
% 0.77/1.04  
% 0.77/1.04  ------ Preprocessing
% 0.77/1.04  
% 0.77/1.04  num_of_splits:                          0
% 0.77/1.04  num_of_split_atoms:                     0
% 0.77/1.04  num_of_reused_defs:                     0
% 0.77/1.04  num_eq_ax_congr_red:                    20
% 0.77/1.04  num_of_sem_filtered_clauses:            1
% 0.77/1.04  num_of_subtypes:                        0
% 0.77/1.04  monotx_restored_types:                  0
% 0.77/1.04  sat_num_of_epr_types:                   0
% 0.77/1.04  sat_num_of_non_cyclic_types:            0
% 0.77/1.04  sat_guarded_non_collapsed_types:        0
% 0.77/1.04  num_pure_diseq_elim:                    0
% 0.77/1.04  simp_replaced_by:                       0
% 0.77/1.04  res_preprocessed:                       58
% 0.77/1.04  prep_upred:                             0
% 0.77/1.04  prep_unflattend:                        6
% 0.77/1.04  smt_new_axioms:                         0
% 0.77/1.04  pred_elim_cands:                        2
% 0.77/1.04  pred_elim:                              1
% 0.77/1.04  pred_elim_cl:                           1
% 0.77/1.04  pred_elim_cycles:                       5
% 0.77/1.04  merged_defs:                            0
% 0.77/1.04  merged_defs_ncl:                        0
% 0.77/1.04  bin_hyper_res:                          0
% 0.77/1.04  prep_cycles:                            4
% 0.77/1.04  pred_elim_time:                         0.001
% 0.77/1.04  splitting_time:                         0.
% 0.77/1.04  sem_filter_time:                        0.
% 0.77/1.04  monotx_time:                            0.001
% 0.77/1.04  subtype_inf_time:                       0.
% 0.77/1.04  
% 0.77/1.04  ------ Problem properties
% 0.77/1.04  
% 0.77/1.04  clauses:                                9
% 0.77/1.04  conjectures:                            1
% 0.77/1.04  epr:                                    0
% 0.77/1.04  horn:                                   8
% 0.77/1.04  ground:                                 3
% 0.77/1.04  unary:                                  5
% 0.77/1.04  binary:                                 3
% 0.77/1.04  lits:                                   14
% 0.77/1.04  lits_eq:                                9
% 0.77/1.04  fd_pure:                                0
% 0.77/1.04  fd_pseudo:                              0
% 0.77/1.04  fd_cond:                                0
% 0.77/1.04  fd_pseudo_cond:                         0
% 0.77/1.04  ac_symbols:                             0
% 0.77/1.04  
% 0.77/1.04  ------ Propositional Solver
% 0.77/1.04  
% 0.77/1.04  prop_solver_calls:                      26
% 0.77/1.04  prop_fast_solver_calls:                 279
% 0.77/1.04  smt_solver_calls:                       0
% 0.77/1.04  smt_fast_solver_calls:                  0
% 0.77/1.04  prop_num_of_clauses:                    176
% 0.77/1.04  prop_preprocess_simplified:             1354
% 0.77/1.04  prop_fo_subsumed:                       1
% 0.77/1.04  prop_solver_time:                       0.
% 0.77/1.04  smt_solver_time:                        0.
% 0.77/1.04  smt_fast_solver_time:                   0.
% 0.77/1.04  prop_fast_solver_time:                  0.
% 0.77/1.04  prop_unsat_core_time:                   0.
% 0.77/1.04  
% 0.77/1.04  ------ QBF
% 0.77/1.04  
% 0.77/1.04  qbf_q_res:                              0
% 0.77/1.04  qbf_num_tautologies:                    0
% 0.77/1.04  qbf_prep_cycles:                        0
% 0.77/1.04  
% 0.77/1.04  ------ BMC1
% 0.77/1.04  
% 0.77/1.04  bmc1_current_bound:                     -1
% 0.77/1.04  bmc1_last_solved_bound:                 -1
% 0.77/1.04  bmc1_unsat_core_size:                   -1
% 0.77/1.04  bmc1_unsat_core_parents_size:           -1
% 0.77/1.04  bmc1_merge_next_fun:                    0
% 0.77/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.77/1.04  
% 0.77/1.04  ------ Instantiation
% 0.77/1.04  
% 0.77/1.04  inst_num_of_clauses:                    80
% 0.77/1.04  inst_num_in_passive:                    3
% 0.77/1.04  inst_num_in_active:                     53
% 0.77/1.04  inst_num_in_unprocessed:                23
% 0.77/1.04  inst_num_of_loops:                      61
% 0.77/1.04  inst_num_of_learning_restarts:          0
% 0.77/1.04  inst_num_moves_active_passive:          4
% 0.77/1.04  inst_lit_activity:                      0
% 0.77/1.04  inst_lit_activity_moves:                0
% 0.77/1.04  inst_num_tautologies:                   0
% 0.77/1.04  inst_num_prop_implied:                  0
% 0.77/1.04  inst_num_existing_simplified:           0
% 0.77/1.04  inst_num_eq_res_simplified:             0
% 0.77/1.04  inst_num_child_elim:                    0
% 0.77/1.04  inst_num_of_dismatching_blockings:      11
% 0.77/1.04  inst_num_of_non_proper_insts:           57
% 0.77/1.04  inst_num_of_duplicates:                 0
% 0.77/1.04  inst_inst_num_from_inst_to_res:         0
% 0.77/1.04  inst_dismatching_checking_time:         0.
% 0.77/1.04  
% 0.77/1.04  ------ Resolution
% 0.77/1.04  
% 0.77/1.04  res_num_of_clauses:                     0
% 0.77/1.04  res_num_in_passive:                     0
% 0.77/1.04  res_num_in_active:                      0
% 0.77/1.04  res_num_of_loops:                       62
% 0.77/1.04  res_forward_subset_subsumed:            14
% 0.77/1.04  res_backward_subset_subsumed:           0
% 0.77/1.04  res_forward_subsumed:                   0
% 0.77/1.04  res_backward_subsumed:                  0
% 0.77/1.04  res_forward_subsumption_resolution:     0
% 0.77/1.04  res_backward_subsumption_resolution:    0
% 0.77/1.04  res_clause_to_clause_subsumption:       9
% 0.77/1.04  res_orphan_elimination:                 0
% 0.77/1.04  res_tautology_del:                      6
% 0.77/1.04  res_num_eq_res_simplified:              0
% 0.77/1.04  res_num_sel_changes:                    0
% 0.77/1.04  res_moves_from_active_to_pass:          0
% 0.77/1.04  
% 0.77/1.04  ------ Superposition
% 0.77/1.04  
% 0.77/1.04  sup_time_total:                         0.
% 0.77/1.04  sup_time_generating:                    0.
% 0.77/1.04  sup_time_sim_full:                      0.
% 0.77/1.04  sup_time_sim_immed:                     0.
% 0.77/1.04  
% 0.77/1.04  sup_num_of_clauses:                     13
% 0.77/1.04  sup_num_in_active:                      12
% 0.77/1.04  sup_num_in_passive:                     1
% 0.77/1.04  sup_num_of_loops:                       12
% 0.77/1.04  sup_fw_superposition:                   2
% 0.77/1.04  sup_bw_superposition:                   2
% 0.77/1.04  sup_immediate_simplified:               0
% 0.77/1.04  sup_given_eliminated:                   0
% 0.77/1.04  comparisons_done:                       0
% 0.77/1.04  comparisons_avoided:                    0
% 0.77/1.04  
% 0.77/1.04  ------ Simplifications
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  sim_fw_subset_subsumed:                 0
% 0.77/1.04  sim_bw_subset_subsumed:                 0
% 0.77/1.04  sim_fw_subsumed:                        0
% 0.77/1.04  sim_bw_subsumed:                        0
% 0.77/1.04  sim_fw_subsumption_res:                 0
% 0.77/1.04  sim_bw_subsumption_res:                 0
% 0.77/1.04  sim_tautology_del:                      0
% 0.77/1.04  sim_eq_tautology_del:                   0
% 0.77/1.04  sim_eq_res_simp:                        0
% 0.77/1.04  sim_fw_demodulated:                     0
% 0.77/1.04  sim_bw_demodulated:                     0
% 0.77/1.04  sim_light_normalised:                   0
% 0.77/1.04  sim_joinable_taut:                      0
% 0.77/1.04  sim_joinable_simp:                      0
% 0.77/1.04  sim_ac_normalised:                      0
% 0.77/1.04  sim_smt_subsumption:                    0
% 0.77/1.04  
%------------------------------------------------------------------------------
