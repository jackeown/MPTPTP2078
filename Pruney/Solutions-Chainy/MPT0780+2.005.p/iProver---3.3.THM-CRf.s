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
% DateTime   : Thu Dec  3 11:54:22 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 338 expanded)
%              Number of clauses        :   91 ( 138 expanded)
%              Number of leaves         :   21 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  340 ( 837 expanded)
%              Number of equality atoms :  183 ( 324 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1)
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f37])).

fof(f57,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f63,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f44,f59,f59])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_209,plain,
    ( X0_43 != X1_43
    | k7_relat_1(X0_43,X0_44) = k7_relat_1(X1_43,X0_44) ),
    theory(equality)).

cnf(c_4167,plain,
    ( k7_relat_1(k8_relat_1(X0_44,X0_43),X0_44) = k7_relat_1(X1_43,X0_44)
    | k8_relat_1(X0_44,X0_43) != X1_43 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_13195,plain,
    ( k7_relat_1(k8_relat_1(X0_44,k2_wellord1(sK3,sK1)),X0_44) = k7_relat_1(k2_wellord1(sK3,sK1),X0_44)
    | k8_relat_1(X0_44,k2_wellord1(sK3,sK1)) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_4167])).

cnf(c_28271,plain,
    ( k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) = k7_relat_1(k2_wellord1(sK3,sK1),sK2)
    | k8_relat_1(sK2,k2_wellord1(sK3,sK1)) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_13195])).

cnf(c_200,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_526,plain,
    ( X0_43 != X1_43
    | k2_wellord1(sK3,sK1) != X1_43
    | k2_wellord1(sK3,sK1) = X0_43 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_535,plain,
    ( X0_43 != k2_wellord1(sK3,sK1)
    | k2_wellord1(sK3,sK1) = X0_43
    | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_551,plain,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1)
    | k2_wellord1(sK3,sK1) = k7_relat_1(k2_wellord1(sK3,sK1),X0_44)
    | k7_relat_1(k2_wellord1(sK3,sK1),X0_44) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_17960,plain,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1)
    | k2_wellord1(sK3,sK1) = k7_relat_1(k2_wellord1(sK3,sK1),sK2)
    | k7_relat_1(k2_wellord1(sK3,sK1),sK2) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_193,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_489,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_183,plain,
    ( r2_hidden(X0_45,X0_44)
    | ~ r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44)))
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_498,plain,
    ( r2_hidden(X0_45,X0_44) = iProver_top
    | r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44))) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_1407,plain,
    ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44),X0_44) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_498])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_179,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_501,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_179])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_192,plain,
    ( ~ r2_hidden(X0_45,X0_44)
    | r2_hidden(X0_45,X1_44)
    | ~ r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_490,plain,
    ( r2_hidden(X0_45,X0_44) != iProver_top
    | r2_hidden(X0_45,X1_44) = iProver_top
    | r1_tarski(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_873,plain,
    ( r2_hidden(X0_45,sK2) = iProver_top
    | r2_hidden(X0_45,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_501,c_490])).

cnf(c_7211,plain,
    ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44),sK2) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_873])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_194,plain,
    ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_488,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_10411,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),sK2) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_7211,c_488])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_178,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_502,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_178])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_185,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k2_wellord1(X0_43,X0_44)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_496,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_188,plain,
    ( ~ v1_relat_1(X0_43)
    | k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_493,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_1327,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k2_relat_1(k2_wellord1(X0_43,X0_44)))) = k3_relat_1(k2_wellord1(X0_43,X0_44))
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_493])).

cnf(c_6038,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k2_relat_1(k2_wellord1(sK3,X0_44)))) = k3_relat_1(k2_wellord1(sK3,X0_44)) ),
    inference(superposition,[status(thm)],[c_502,c_1327])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_191,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X2_44)),X1_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_491,plain,
    ( r1_tarski(X0_44,X1_44) = iProver_top
    | r1_tarski(k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X2_44)),X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_6386,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
    | r1_tarski(k1_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_6038,c_491])).

cnf(c_12147,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10411,c_6386])).

cnf(c_17,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13753,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12147,c_17])).

cnf(c_8,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_186,plain,
    ( ~ r1_tarski(k1_relat_1(X0_43),X0_44)
    | ~ v1_relat_1(X0_43)
    | k7_relat_1(X0_43,X0_44) = X0_43 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_495,plain,
    ( k7_relat_1(X0_43,X0_44) = X0_43
    | r1_tarski(k1_relat_1(X0_43),X0_44) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_13757,plain,
    ( k7_relat_1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1)
    | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13753,c_495])).

cnf(c_5,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_189,plain,
    ( k2_enumset1(X0_44,X0_44,X0_44,X1_44) = k2_enumset1(X1_44,X1_44,X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_735,plain,
    ( r1_tarski(X0_44,X1_44) = iProver_top
    | r1_tarski(k3_tarski(k2_enumset1(X2_44,X2_44,X2_44,X0_44)),X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_189,c_491])).

cnf(c_6390,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_6038,c_735])).

cnf(c_12146,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10411,c_6390])).

cnf(c_13740,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12146,c_17])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_187,plain,
    ( ~ r1_tarski(k2_relat_1(X0_43),X0_44)
    | ~ v1_relat_1(X0_43)
    | k8_relat_1(X0_44,X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_494,plain,
    ( k8_relat_1(X0_44,X0_43) = X0_43
    | r1_tarski(k2_relat_1(X0_43),X0_44) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_13744,plain,
    ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k2_wellord1(sK3,sK1)
    | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13740,c_494])).

cnf(c_726,plain,
    ( X0_43 != X1_43
    | X0_43 = k7_relat_1(k8_relat_1(X0_44,X2_43),X0_44)
    | k7_relat_1(k8_relat_1(X0_44,X2_43),X0_44) != X1_43 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_813,plain,
    ( X0_43 != k7_relat_1(X1_43,X0_44)
    | X0_43 = k7_relat_1(k8_relat_1(X0_44,X2_43),X0_44)
    | k7_relat_1(k8_relat_1(X0_44,X2_43),X0_44) != k7_relat_1(X1_43,X0_44) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1438,plain,
    ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),X0_44)
    | k2_wellord1(sK3,sK1) = k7_relat_1(k8_relat_1(X0_44,X0_43),X0_44)
    | k7_relat_1(k8_relat_1(X0_44,X0_43),X0_44) != k7_relat_1(k2_wellord1(sK3,sK1),X0_44) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_5247,plain,
    ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),sK2)
    | k2_wellord1(sK3,sK1) = k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,X0_44)),sK2)
    | k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,X0_44)),sK2) != k7_relat_1(k2_wellord1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_5252,plain,
    ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),sK2)
    | k2_wellord1(sK3,sK1) = k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2)
    | k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) != k7_relat_1(k2_wellord1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_5247])).

cnf(c_541,plain,
    ( k2_wellord1(X0_43,X0_44) != X1_43
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X1_43
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(X0_43,X0_44) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_3224,plain,
    ( k2_wellord1(X0_43,X0_44) != k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,X1_44)),sK2)
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(X0_43,X0_44)
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,X1_44)),sK2) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_3225,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(sK3,sK1)
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2)
    | k2_wellord1(sK3,sK1) != k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) ),
    inference(instantiation,[status(thm)],[c_3224])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_184,plain,
    ( ~ v1_relat_1(X0_43)
    | k7_relat_1(k8_relat_1(X0_44,X0_43),X0_44) = k2_wellord1(X0_43,X0_44) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1401,plain,
    ( ~ v1_relat_1(k2_wellord1(sK3,sK1))
    | k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) = k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_580,plain,
    ( X0_43 != X1_43
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X1_43
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = X0_43 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_638,plain,
    ( X0_43 != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = X0_43
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_959,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2)
    | k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) != k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_181,plain,
    ( ~ v1_relat_1(X0_43)
    | k2_wellord1(k2_wellord1(X0_43,X0_44),X1_44) = k2_wellord1(k2_wellord1(X0_43,X1_44),X0_44) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_630,plain,
    ( ~ v1_relat_1(sK3)
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_520,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X0_43
    | k2_wellord1(sK3,sK1) != X0_43
    | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_525,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(sK3,sK1)
    | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1)
    | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_14,negated_conjecture,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_180,negated_conjecture,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_239,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_241,plain,
    ( v1_relat_1(k2_wellord1(sK3,sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_240,plain,
    ( v1_relat_1(k2_wellord1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_197,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_221,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_196,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_220,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_210,plain,
    ( X0_44 != X1_44
    | X0_43 != X1_43
    | k2_wellord1(X0_43,X0_44) = k2_wellord1(X1_43,X1_44) ),
    theory(equality)).

cnf(c_218,plain,
    ( sK1 != sK1
    | k2_wellord1(sK3,sK1) = k2_wellord1(sK3,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28271,c_17960,c_13757,c_13744,c_5252,c_3225,c_1401,c_959,c_630,c_525,c_180,c_241,c_240,c_221,c_220,c_218,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.01/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/1.48  
% 8.01/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.01/1.48  
% 8.01/1.48  ------  iProver source info
% 8.01/1.48  
% 8.01/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.01/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.01/1.48  git: non_committed_changes: false
% 8.01/1.48  git: last_make_outside_of_git: false
% 8.01/1.48  
% 8.01/1.48  ------ 
% 8.01/1.48  
% 8.01/1.48  ------ Input Options
% 8.01/1.48  
% 8.01/1.48  --out_options                           all
% 8.01/1.48  --tptp_safe_out                         true
% 8.01/1.48  --problem_path                          ""
% 8.01/1.48  --include_path                          ""
% 8.01/1.48  --clausifier                            res/vclausify_rel
% 8.01/1.48  --clausifier_options                    ""
% 8.01/1.48  --stdin                                 false
% 8.01/1.48  --stats_out                             all
% 8.01/1.48  
% 8.01/1.48  ------ General Options
% 8.01/1.48  
% 8.01/1.48  --fof                                   false
% 8.01/1.48  --time_out_real                         305.
% 8.01/1.48  --time_out_virtual                      -1.
% 8.01/1.48  --symbol_type_check                     false
% 8.01/1.48  --clausify_out                          false
% 8.01/1.48  --sig_cnt_out                           false
% 8.01/1.48  --trig_cnt_out                          false
% 8.01/1.48  --trig_cnt_out_tolerance                1.
% 8.01/1.48  --trig_cnt_out_sk_spl                   false
% 8.01/1.48  --abstr_cl_out                          false
% 8.01/1.48  
% 8.01/1.48  ------ Global Options
% 8.01/1.48  
% 8.01/1.48  --schedule                              default
% 8.01/1.48  --add_important_lit                     false
% 8.01/1.48  --prop_solver_per_cl                    1000
% 8.01/1.48  --min_unsat_core                        false
% 8.01/1.48  --soft_assumptions                      false
% 8.01/1.48  --soft_lemma_size                       3
% 8.01/1.48  --prop_impl_unit_size                   0
% 8.01/1.48  --prop_impl_unit                        []
% 8.01/1.48  --share_sel_clauses                     true
% 8.01/1.48  --reset_solvers                         false
% 8.01/1.48  --bc_imp_inh                            [conj_cone]
% 8.01/1.48  --conj_cone_tolerance                   3.
% 8.01/1.48  --extra_neg_conj                        none
% 8.01/1.48  --large_theory_mode                     true
% 8.01/1.48  --prolific_symb_bound                   200
% 8.01/1.48  --lt_threshold                          2000
% 8.01/1.48  --clause_weak_htbl                      true
% 8.01/1.48  --gc_record_bc_elim                     false
% 8.01/1.48  
% 8.01/1.48  ------ Preprocessing Options
% 8.01/1.48  
% 8.01/1.48  --preprocessing_flag                    true
% 8.01/1.48  --time_out_prep_mult                    0.1
% 8.01/1.48  --splitting_mode                        input
% 8.01/1.48  --splitting_grd                         true
% 8.01/1.48  --splitting_cvd                         false
% 8.01/1.48  --splitting_cvd_svl                     false
% 8.01/1.48  --splitting_nvd                         32
% 8.01/1.48  --sub_typing                            true
% 8.01/1.48  --prep_gs_sim                           true
% 8.01/1.48  --prep_unflatten                        true
% 8.01/1.48  --prep_res_sim                          true
% 8.01/1.48  --prep_upred                            true
% 8.01/1.48  --prep_sem_filter                       exhaustive
% 8.01/1.48  --prep_sem_filter_out                   false
% 8.01/1.48  --pred_elim                             true
% 8.01/1.48  --res_sim_input                         true
% 8.01/1.48  --eq_ax_congr_red                       true
% 8.01/1.48  --pure_diseq_elim                       true
% 8.01/1.48  --brand_transform                       false
% 8.01/1.48  --non_eq_to_eq                          false
% 8.01/1.48  --prep_def_merge                        true
% 8.01/1.48  --prep_def_merge_prop_impl              false
% 8.01/1.48  --prep_def_merge_mbd                    true
% 8.01/1.48  --prep_def_merge_tr_red                 false
% 8.01/1.48  --prep_def_merge_tr_cl                  false
% 8.01/1.48  --smt_preprocessing                     true
% 8.01/1.48  --smt_ac_axioms                         fast
% 8.01/1.48  --preprocessed_out                      false
% 8.01/1.48  --preprocessed_stats                    false
% 8.01/1.48  
% 8.01/1.48  ------ Abstraction refinement Options
% 8.01/1.48  
% 8.01/1.48  --abstr_ref                             []
% 8.01/1.48  --abstr_ref_prep                        false
% 8.01/1.48  --abstr_ref_until_sat                   false
% 8.01/1.48  --abstr_ref_sig_restrict                funpre
% 8.01/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.01/1.48  --abstr_ref_under                       []
% 8.01/1.48  
% 8.01/1.48  ------ SAT Options
% 8.01/1.48  
% 8.01/1.48  --sat_mode                              false
% 8.01/1.48  --sat_fm_restart_options                ""
% 8.01/1.48  --sat_gr_def                            false
% 8.01/1.48  --sat_epr_types                         true
% 8.01/1.48  --sat_non_cyclic_types                  false
% 8.01/1.48  --sat_finite_models                     false
% 8.01/1.48  --sat_fm_lemmas                         false
% 8.01/1.48  --sat_fm_prep                           false
% 8.01/1.48  --sat_fm_uc_incr                        true
% 8.01/1.48  --sat_out_model                         small
% 8.01/1.48  --sat_out_clauses                       false
% 8.01/1.48  
% 8.01/1.48  ------ QBF Options
% 8.01/1.48  
% 8.01/1.48  --qbf_mode                              false
% 8.01/1.48  --qbf_elim_univ                         false
% 8.01/1.48  --qbf_dom_inst                          none
% 8.01/1.48  --qbf_dom_pre_inst                      false
% 8.01/1.48  --qbf_sk_in                             false
% 8.01/1.48  --qbf_pred_elim                         true
% 8.01/1.48  --qbf_split                             512
% 8.01/1.48  
% 8.01/1.48  ------ BMC1 Options
% 8.01/1.48  
% 8.01/1.48  --bmc1_incremental                      false
% 8.01/1.48  --bmc1_axioms                           reachable_all
% 8.01/1.48  --bmc1_min_bound                        0
% 8.01/1.48  --bmc1_max_bound                        -1
% 8.01/1.48  --bmc1_max_bound_default                -1
% 8.01/1.48  --bmc1_symbol_reachability              true
% 8.01/1.48  --bmc1_property_lemmas                  false
% 8.01/1.48  --bmc1_k_induction                      false
% 8.01/1.48  --bmc1_non_equiv_states                 false
% 8.01/1.48  --bmc1_deadlock                         false
% 8.01/1.48  --bmc1_ucm                              false
% 8.01/1.48  --bmc1_add_unsat_core                   none
% 8.01/1.48  --bmc1_unsat_core_children              false
% 8.01/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.01/1.48  --bmc1_out_stat                         full
% 8.01/1.48  --bmc1_ground_init                      false
% 8.01/1.48  --bmc1_pre_inst_next_state              false
% 8.01/1.48  --bmc1_pre_inst_state                   false
% 8.01/1.48  --bmc1_pre_inst_reach_state             false
% 8.01/1.48  --bmc1_out_unsat_core                   false
% 8.01/1.48  --bmc1_aig_witness_out                  false
% 8.01/1.48  --bmc1_verbose                          false
% 8.01/1.48  --bmc1_dump_clauses_tptp                false
% 8.01/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.01/1.48  --bmc1_dump_file                        -
% 8.01/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.01/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.01/1.48  --bmc1_ucm_extend_mode                  1
% 8.01/1.48  --bmc1_ucm_init_mode                    2
% 8.01/1.48  --bmc1_ucm_cone_mode                    none
% 8.01/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.01/1.48  --bmc1_ucm_relax_model                  4
% 8.01/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.01/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.01/1.48  --bmc1_ucm_layered_model                none
% 8.01/1.48  --bmc1_ucm_max_lemma_size               10
% 8.01/1.48  
% 8.01/1.48  ------ AIG Options
% 8.01/1.48  
% 8.01/1.48  --aig_mode                              false
% 8.01/1.48  
% 8.01/1.48  ------ Instantiation Options
% 8.01/1.48  
% 8.01/1.48  --instantiation_flag                    true
% 8.01/1.48  --inst_sos_flag                         true
% 8.01/1.48  --inst_sos_phase                        true
% 8.01/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.01/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.01/1.48  --inst_lit_sel_side                     num_symb
% 8.01/1.48  --inst_solver_per_active                1400
% 8.01/1.48  --inst_solver_calls_frac                1.
% 8.01/1.48  --inst_passive_queue_type               priority_queues
% 8.01/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.01/1.48  --inst_passive_queues_freq              [25;2]
% 8.01/1.48  --inst_dismatching                      true
% 8.01/1.48  --inst_eager_unprocessed_to_passive     true
% 8.01/1.48  --inst_prop_sim_given                   true
% 8.01/1.48  --inst_prop_sim_new                     false
% 8.01/1.48  --inst_subs_new                         false
% 8.01/1.48  --inst_eq_res_simp                      false
% 8.01/1.48  --inst_subs_given                       false
% 8.01/1.48  --inst_orphan_elimination               true
% 8.01/1.48  --inst_learning_loop_flag               true
% 8.01/1.48  --inst_learning_start                   3000
% 8.01/1.48  --inst_learning_factor                  2
% 8.01/1.48  --inst_start_prop_sim_after_learn       3
% 8.01/1.48  --inst_sel_renew                        solver
% 8.01/1.48  --inst_lit_activity_flag                true
% 8.01/1.48  --inst_restr_to_given                   false
% 8.01/1.48  --inst_activity_threshold               500
% 8.01/1.48  --inst_out_proof                        true
% 8.01/1.48  
% 8.01/1.48  ------ Resolution Options
% 8.01/1.48  
% 8.01/1.48  --resolution_flag                       true
% 8.01/1.48  --res_lit_sel                           adaptive
% 8.01/1.48  --res_lit_sel_side                      none
% 8.01/1.48  --res_ordering                          kbo
% 8.01/1.48  --res_to_prop_solver                    active
% 8.01/1.48  --res_prop_simpl_new                    false
% 8.01/1.48  --res_prop_simpl_given                  true
% 8.01/1.48  --res_passive_queue_type                priority_queues
% 8.01/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.01/1.48  --res_passive_queues_freq               [15;5]
% 8.01/1.48  --res_forward_subs                      full
% 8.01/1.48  --res_backward_subs                     full
% 8.01/1.48  --res_forward_subs_resolution           true
% 8.01/1.48  --res_backward_subs_resolution          true
% 8.01/1.48  --res_orphan_elimination                true
% 8.01/1.48  --res_time_limit                        2.
% 8.01/1.48  --res_out_proof                         true
% 8.01/1.48  
% 8.01/1.48  ------ Superposition Options
% 8.01/1.48  
% 8.01/1.48  --superposition_flag                    true
% 8.01/1.48  --sup_passive_queue_type                priority_queues
% 8.01/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.01/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.01/1.48  --demod_completeness_check              fast
% 8.01/1.48  --demod_use_ground                      true
% 8.01/1.48  --sup_to_prop_solver                    passive
% 8.01/1.48  --sup_prop_simpl_new                    true
% 8.01/1.48  --sup_prop_simpl_given                  true
% 8.01/1.48  --sup_fun_splitting                     true
% 8.01/1.48  --sup_smt_interval                      50000
% 8.01/1.48  
% 8.01/1.48  ------ Superposition Simplification Setup
% 8.01/1.48  
% 8.01/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.01/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.01/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.01/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.01/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.01/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.01/1.48  --sup_immed_triv                        [TrivRules]
% 8.01/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.48  --sup_immed_bw_main                     []
% 8.01/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.01/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.01/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.48  --sup_input_bw                          []
% 8.01/1.48  
% 8.01/1.48  ------ Combination Options
% 8.01/1.48  
% 8.01/1.48  --comb_res_mult                         3
% 8.01/1.48  --comb_sup_mult                         2
% 8.01/1.48  --comb_inst_mult                        10
% 8.01/1.48  
% 8.01/1.48  ------ Debug Options
% 8.01/1.48  
% 8.01/1.48  --dbg_backtrace                         false
% 8.01/1.48  --dbg_dump_prop_clauses                 false
% 8.01/1.48  --dbg_dump_prop_clauses_file            -
% 8.01/1.48  --dbg_out_stat                          false
% 8.01/1.48  ------ Parsing...
% 8.01/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.01/1.48  
% 8.01/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.01/1.48  
% 8.01/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.01/1.48  
% 8.01/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.01/1.48  ------ Proving...
% 8.01/1.48  ------ Problem Properties 
% 8.01/1.48  
% 8.01/1.48  
% 8.01/1.48  clauses                                 17
% 8.01/1.48  conjectures                             3
% 8.01/1.48  EPR                                     4
% 8.01/1.48  Horn                                    16
% 8.01/1.48  unary                                   4
% 8.01/1.48  binary                                  7
% 8.01/1.48  lits                                    36
% 8.01/1.48  lits eq                                 7
% 8.01/1.48  fd_pure                                 0
% 8.01/1.48  fd_pseudo                               0
% 8.01/1.48  fd_cond                                 0
% 8.01/1.48  fd_pseudo_cond                          0
% 8.01/1.48  AC symbols                              0
% 8.01/1.48  
% 8.01/1.48  ------ Schedule dynamic 5 is on 
% 8.01/1.48  
% 8.01/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.01/1.48  
% 8.01/1.48  
% 8.01/1.48  ------ 
% 8.01/1.48  Current options:
% 8.01/1.48  ------ 
% 8.01/1.48  
% 8.01/1.48  ------ Input Options
% 8.01/1.48  
% 8.01/1.48  --out_options                           all
% 8.01/1.48  --tptp_safe_out                         true
% 8.01/1.48  --problem_path                          ""
% 8.01/1.48  --include_path                          ""
% 8.01/1.48  --clausifier                            res/vclausify_rel
% 8.01/1.48  --clausifier_options                    ""
% 8.01/1.48  --stdin                                 false
% 8.01/1.48  --stats_out                             all
% 8.01/1.48  
% 8.01/1.48  ------ General Options
% 8.01/1.48  
% 8.01/1.48  --fof                                   false
% 8.01/1.48  --time_out_real                         305.
% 8.01/1.48  --time_out_virtual                      -1.
% 8.01/1.48  --symbol_type_check                     false
% 8.01/1.48  --clausify_out                          false
% 8.01/1.48  --sig_cnt_out                           false
% 8.01/1.48  --trig_cnt_out                          false
% 8.01/1.48  --trig_cnt_out_tolerance                1.
% 8.01/1.48  --trig_cnt_out_sk_spl                   false
% 8.01/1.48  --abstr_cl_out                          false
% 8.01/1.48  
% 8.01/1.48  ------ Global Options
% 8.01/1.48  
% 8.01/1.48  --schedule                              default
% 8.01/1.48  --add_important_lit                     false
% 8.01/1.48  --prop_solver_per_cl                    1000
% 8.01/1.48  --min_unsat_core                        false
% 8.01/1.48  --soft_assumptions                      false
% 8.01/1.48  --soft_lemma_size                       3
% 8.01/1.48  --prop_impl_unit_size                   0
% 8.01/1.48  --prop_impl_unit                        []
% 8.01/1.48  --share_sel_clauses                     true
% 8.01/1.48  --reset_solvers                         false
% 8.01/1.48  --bc_imp_inh                            [conj_cone]
% 8.01/1.48  --conj_cone_tolerance                   3.
% 8.01/1.48  --extra_neg_conj                        none
% 8.01/1.48  --large_theory_mode                     true
% 8.01/1.48  --prolific_symb_bound                   200
% 8.01/1.48  --lt_threshold                          2000
% 8.01/1.48  --clause_weak_htbl                      true
% 8.01/1.48  --gc_record_bc_elim                     false
% 8.01/1.48  
% 8.01/1.48  ------ Preprocessing Options
% 8.01/1.48  
% 8.01/1.48  --preprocessing_flag                    true
% 8.01/1.48  --time_out_prep_mult                    0.1
% 8.01/1.48  --splitting_mode                        input
% 8.01/1.48  --splitting_grd                         true
% 8.01/1.48  --splitting_cvd                         false
% 8.01/1.48  --splitting_cvd_svl                     false
% 8.01/1.48  --splitting_nvd                         32
% 8.01/1.48  --sub_typing                            true
% 8.01/1.48  --prep_gs_sim                           true
% 8.01/1.48  --prep_unflatten                        true
% 8.01/1.48  --prep_res_sim                          true
% 8.01/1.48  --prep_upred                            true
% 8.01/1.48  --prep_sem_filter                       exhaustive
% 8.01/1.48  --prep_sem_filter_out                   false
% 8.01/1.48  --pred_elim                             true
% 8.01/1.48  --res_sim_input                         true
% 8.01/1.48  --eq_ax_congr_red                       true
% 8.01/1.48  --pure_diseq_elim                       true
% 8.01/1.48  --brand_transform                       false
% 8.01/1.48  --non_eq_to_eq                          false
% 8.01/1.48  --prep_def_merge                        true
% 8.01/1.48  --prep_def_merge_prop_impl              false
% 8.01/1.48  --prep_def_merge_mbd                    true
% 8.01/1.48  --prep_def_merge_tr_red                 false
% 8.01/1.48  --prep_def_merge_tr_cl                  false
% 8.01/1.48  --smt_preprocessing                     true
% 8.01/1.48  --smt_ac_axioms                         fast
% 8.01/1.48  --preprocessed_out                      false
% 8.01/1.48  --preprocessed_stats                    false
% 8.01/1.48  
% 8.01/1.48  ------ Abstraction refinement Options
% 8.01/1.48  
% 8.01/1.48  --abstr_ref                             []
% 8.01/1.48  --abstr_ref_prep                        false
% 8.01/1.48  --abstr_ref_until_sat                   false
% 8.01/1.48  --abstr_ref_sig_restrict                funpre
% 8.01/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.01/1.48  --abstr_ref_under                       []
% 8.01/1.48  
% 8.01/1.48  ------ SAT Options
% 8.01/1.48  
% 8.01/1.48  --sat_mode                              false
% 8.01/1.48  --sat_fm_restart_options                ""
% 8.01/1.48  --sat_gr_def                            false
% 8.01/1.48  --sat_epr_types                         true
% 8.01/1.48  --sat_non_cyclic_types                  false
% 8.01/1.48  --sat_finite_models                     false
% 8.01/1.48  --sat_fm_lemmas                         false
% 8.01/1.48  --sat_fm_prep                           false
% 8.01/1.48  --sat_fm_uc_incr                        true
% 8.01/1.48  --sat_out_model                         small
% 8.01/1.48  --sat_out_clauses                       false
% 8.01/1.48  
% 8.01/1.48  ------ QBF Options
% 8.01/1.48  
% 8.01/1.48  --qbf_mode                              false
% 8.01/1.48  --qbf_elim_univ                         false
% 8.01/1.48  --qbf_dom_inst                          none
% 8.01/1.48  --qbf_dom_pre_inst                      false
% 8.01/1.48  --qbf_sk_in                             false
% 8.01/1.48  --qbf_pred_elim                         true
% 8.01/1.48  --qbf_split                             512
% 8.01/1.48  
% 8.01/1.48  ------ BMC1 Options
% 8.01/1.48  
% 8.01/1.48  --bmc1_incremental                      false
% 8.01/1.48  --bmc1_axioms                           reachable_all
% 8.01/1.48  --bmc1_min_bound                        0
% 8.01/1.48  --bmc1_max_bound                        -1
% 8.01/1.48  --bmc1_max_bound_default                -1
% 8.01/1.48  --bmc1_symbol_reachability              true
% 8.01/1.48  --bmc1_property_lemmas                  false
% 8.01/1.48  --bmc1_k_induction                      false
% 8.01/1.48  --bmc1_non_equiv_states                 false
% 8.01/1.48  --bmc1_deadlock                         false
% 8.01/1.48  --bmc1_ucm                              false
% 8.01/1.48  --bmc1_add_unsat_core                   none
% 8.01/1.48  --bmc1_unsat_core_children              false
% 8.01/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.01/1.48  --bmc1_out_stat                         full
% 8.01/1.48  --bmc1_ground_init                      false
% 8.01/1.48  --bmc1_pre_inst_next_state              false
% 8.01/1.48  --bmc1_pre_inst_state                   false
% 8.01/1.48  --bmc1_pre_inst_reach_state             false
% 8.01/1.48  --bmc1_out_unsat_core                   false
% 8.01/1.48  --bmc1_aig_witness_out                  false
% 8.01/1.48  --bmc1_verbose                          false
% 8.01/1.48  --bmc1_dump_clauses_tptp                false
% 8.01/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.01/1.48  --bmc1_dump_file                        -
% 8.01/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.01/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.01/1.48  --bmc1_ucm_extend_mode                  1
% 8.01/1.48  --bmc1_ucm_init_mode                    2
% 8.01/1.48  --bmc1_ucm_cone_mode                    none
% 8.01/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.01/1.48  --bmc1_ucm_relax_model                  4
% 8.01/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.01/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.01/1.48  --bmc1_ucm_layered_model                none
% 8.01/1.48  --bmc1_ucm_max_lemma_size               10
% 8.01/1.48  
% 8.01/1.48  ------ AIG Options
% 8.01/1.48  
% 8.01/1.48  --aig_mode                              false
% 8.01/1.48  
% 8.01/1.48  ------ Instantiation Options
% 8.01/1.48  
% 8.01/1.48  --instantiation_flag                    true
% 8.01/1.48  --inst_sos_flag                         true
% 8.01/1.48  --inst_sos_phase                        true
% 8.01/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.01/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.01/1.48  --inst_lit_sel_side                     none
% 8.01/1.48  --inst_solver_per_active                1400
% 8.01/1.48  --inst_solver_calls_frac                1.
% 8.01/1.48  --inst_passive_queue_type               priority_queues
% 8.01/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.01/1.48  --inst_passive_queues_freq              [25;2]
% 8.01/1.48  --inst_dismatching                      true
% 8.01/1.48  --inst_eager_unprocessed_to_passive     true
% 8.01/1.48  --inst_prop_sim_given                   true
% 8.01/1.48  --inst_prop_sim_new                     false
% 8.01/1.48  --inst_subs_new                         false
% 8.01/1.48  --inst_eq_res_simp                      false
% 8.01/1.48  --inst_subs_given                       false
% 8.01/1.48  --inst_orphan_elimination               true
% 8.01/1.48  --inst_learning_loop_flag               true
% 8.01/1.48  --inst_learning_start                   3000
% 8.01/1.48  --inst_learning_factor                  2
% 8.01/1.48  --inst_start_prop_sim_after_learn       3
% 8.01/1.48  --inst_sel_renew                        solver
% 8.01/1.48  --inst_lit_activity_flag                true
% 8.01/1.48  --inst_restr_to_given                   false
% 8.01/1.48  --inst_activity_threshold               500
% 8.01/1.48  --inst_out_proof                        true
% 8.01/1.48  
% 8.01/1.48  ------ Resolution Options
% 8.01/1.48  
% 8.01/1.48  --resolution_flag                       false
% 8.01/1.48  --res_lit_sel                           adaptive
% 8.01/1.48  --res_lit_sel_side                      none
% 8.01/1.48  --res_ordering                          kbo
% 8.01/1.48  --res_to_prop_solver                    active
% 8.01/1.48  --res_prop_simpl_new                    false
% 8.01/1.48  --res_prop_simpl_given                  true
% 8.01/1.48  --res_passive_queue_type                priority_queues
% 8.01/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.01/1.48  --res_passive_queues_freq               [15;5]
% 8.01/1.48  --res_forward_subs                      full
% 8.01/1.48  --res_backward_subs                     full
% 8.01/1.48  --res_forward_subs_resolution           true
% 8.01/1.48  --res_backward_subs_resolution          true
% 8.01/1.48  --res_orphan_elimination                true
% 8.01/1.48  --res_time_limit                        2.
% 8.01/1.48  --res_out_proof                         true
% 8.01/1.48  
% 8.01/1.48  ------ Superposition Options
% 8.01/1.48  
% 8.01/1.48  --superposition_flag                    true
% 8.01/1.48  --sup_passive_queue_type                priority_queues
% 8.01/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.01/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.01/1.48  --demod_completeness_check              fast
% 8.01/1.48  --demod_use_ground                      true
% 8.01/1.48  --sup_to_prop_solver                    passive
% 8.01/1.48  --sup_prop_simpl_new                    true
% 8.01/1.48  --sup_prop_simpl_given                  true
% 8.01/1.48  --sup_fun_splitting                     true
% 8.01/1.48  --sup_smt_interval                      50000
% 8.01/1.48  
% 8.01/1.48  ------ Superposition Simplification Setup
% 8.01/1.48  
% 8.01/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.01/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.01/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.01/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.01/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.01/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.01/1.48  --sup_immed_triv                        [TrivRules]
% 8.01/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.48  --sup_immed_bw_main                     []
% 8.01/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.01/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.01/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.48  --sup_input_bw                          []
% 8.01/1.48  
% 8.01/1.48  ------ Combination Options
% 8.01/1.48  
% 8.01/1.48  --comb_res_mult                         3
% 8.01/1.48  --comb_sup_mult                         2
% 8.01/1.48  --comb_inst_mult                        10
% 8.01/1.48  
% 8.01/1.48  ------ Debug Options
% 8.01/1.48  
% 8.01/1.48  --dbg_backtrace                         false
% 8.01/1.48  --dbg_dump_prop_clauses                 false
% 8.01/1.48  --dbg_dump_prop_clauses_file            -
% 8.01/1.48  --dbg_out_stat                          false
% 8.01/1.48  
% 8.01/1.48  
% 8.01/1.48  
% 8.01/1.48  
% 8.01/1.48  ------ Proving...
% 8.01/1.48  
% 8.01/1.48  
% 8.01/1.48  % SZS status Theorem for theBenchmark.p
% 8.01/1.48  
% 8.01/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 8.01/1.48  
% 8.01/1.48  fof(f1,axiom,(
% 8.01/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f17,plain,(
% 8.01/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.01/1.48    inference(ennf_transformation,[],[f1])).
% 8.01/1.48  
% 8.01/1.48  fof(f33,plain,(
% 8.01/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 8.01/1.48    inference(nnf_transformation,[],[f17])).
% 8.01/1.48  
% 8.01/1.48  fof(f34,plain,(
% 8.01/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.01/1.48    inference(rectify,[],[f33])).
% 8.01/1.48  
% 8.01/1.48  fof(f35,plain,(
% 8.01/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 8.01/1.48    introduced(choice_axiom,[])).
% 8.01/1.48  
% 8.01/1.48  fof(f36,plain,(
% 8.01/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.01/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 8.01/1.48  
% 8.01/1.48  fof(f40,plain,(
% 8.01/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f36])).
% 8.01/1.48  
% 8.01/1.48  fof(f13,axiom,(
% 8.01/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f28,plain,(
% 8.01/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.01/1.48    inference(ennf_transformation,[],[f13])).
% 8.01/1.48  
% 8.01/1.48  fof(f29,plain,(
% 8.01/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 8.01/1.48    inference(flattening,[],[f28])).
% 8.01/1.48  
% 8.01/1.48  fof(f54,plain,(
% 8.01/1.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f29])).
% 8.01/1.48  
% 8.01/1.48  fof(f15,conjecture,(
% 8.01/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f16,negated_conjecture,(
% 8.01/1.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 8.01/1.48    inference(negated_conjecture,[],[f15])).
% 8.01/1.48  
% 8.01/1.48  fof(f31,plain,(
% 8.01/1.48    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 8.01/1.48    inference(ennf_transformation,[],[f16])).
% 8.01/1.48  
% 8.01/1.48  fof(f32,plain,(
% 8.01/1.48    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 8.01/1.48    inference(flattening,[],[f31])).
% 8.01/1.48  
% 8.01/1.48  fof(f37,plain,(
% 8.01/1.48    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3))),
% 8.01/1.48    introduced(choice_axiom,[])).
% 8.01/1.48  
% 8.01/1.48  fof(f38,plain,(
% 8.01/1.48    k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3)),
% 8.01/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f37])).
% 8.01/1.48  
% 8.01/1.48  fof(f57,plain,(
% 8.01/1.48    r1_tarski(sK1,sK2)),
% 8.01/1.48    inference(cnf_transformation,[],[f38])).
% 8.01/1.48  
% 8.01/1.48  fof(f39,plain,(
% 8.01/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f36])).
% 8.01/1.48  
% 8.01/1.48  fof(f41,plain,(
% 8.01/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f36])).
% 8.01/1.48  
% 8.01/1.48  fof(f56,plain,(
% 8.01/1.48    v1_relat_1(sK3)),
% 8.01/1.48    inference(cnf_transformation,[],[f38])).
% 8.01/1.48  
% 8.01/1.48  fof(f11,axiom,(
% 8.01/1.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f26,plain,(
% 8.01/1.48    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 8.01/1.48    inference(ennf_transformation,[],[f11])).
% 8.01/1.48  
% 8.01/1.48  fof(f51,plain,(
% 8.01/1.48    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f26])).
% 8.01/1.48  
% 8.01/1.48  fof(f8,axiom,(
% 8.01/1.48    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f21,plain,(
% 8.01/1.48    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 8.01/1.48    inference(ennf_transformation,[],[f8])).
% 8.01/1.48  
% 8.01/1.48  fof(f48,plain,(
% 8.01/1.48    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f21])).
% 8.01/1.48  
% 8.01/1.48  fof(f7,axiom,(
% 8.01/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f47,plain,(
% 8.01/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 8.01/1.48    inference(cnf_transformation,[],[f7])).
% 8.01/1.48  
% 8.01/1.48  fof(f5,axiom,(
% 8.01/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f45,plain,(
% 8.01/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f5])).
% 8.01/1.48  
% 8.01/1.48  fof(f6,axiom,(
% 8.01/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f46,plain,(
% 8.01/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f6])).
% 8.01/1.48  
% 8.01/1.48  fof(f59,plain,(
% 8.01/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 8.01/1.48    inference(definition_unfolding,[],[f45,f46])).
% 8.01/1.48  
% 8.01/1.48  fof(f60,plain,(
% 8.01/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 8.01/1.48    inference(definition_unfolding,[],[f47,f59])).
% 8.01/1.48  
% 8.01/1.48  fof(f63,plain,(
% 8.01/1.48    ( ! [X0] : (k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.01/1.48    inference(definition_unfolding,[],[f48,f60])).
% 8.01/1.48  
% 8.01/1.48  fof(f2,axiom,(
% 8.01/1.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f18,plain,(
% 8.01/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 8.01/1.48    inference(ennf_transformation,[],[f2])).
% 8.01/1.48  
% 8.01/1.48  fof(f42,plain,(
% 8.01/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f18])).
% 8.01/1.48  
% 8.01/1.48  fof(f61,plain,(
% 8.01/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2)) )),
% 8.01/1.48    inference(definition_unfolding,[],[f42,f60])).
% 8.01/1.48  
% 8.01/1.48  fof(f10,axiom,(
% 8.01/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f24,plain,(
% 8.01/1.48    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.01/1.48    inference(ennf_transformation,[],[f10])).
% 8.01/1.48  
% 8.01/1.48  fof(f25,plain,(
% 8.01/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 8.01/1.48    inference(flattening,[],[f24])).
% 8.01/1.48  
% 8.01/1.48  fof(f50,plain,(
% 8.01/1.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f25])).
% 8.01/1.48  
% 8.01/1.48  fof(f4,axiom,(
% 8.01/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f44,plain,(
% 8.01/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f4])).
% 8.01/1.48  
% 8.01/1.48  fof(f62,plain,(
% 8.01/1.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 8.01/1.48    inference(definition_unfolding,[],[f44,f59,f59])).
% 8.01/1.48  
% 8.01/1.48  fof(f9,axiom,(
% 8.01/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f22,plain,(
% 8.01/1.48    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.01/1.48    inference(ennf_transformation,[],[f9])).
% 8.01/1.48  
% 8.01/1.48  fof(f23,plain,(
% 8.01/1.48    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 8.01/1.48    inference(flattening,[],[f22])).
% 8.01/1.48  
% 8.01/1.48  fof(f49,plain,(
% 8.01/1.48    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f23])).
% 8.01/1.48  
% 8.01/1.48  fof(f12,axiom,(
% 8.01/1.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f27,plain,(
% 8.01/1.48    ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 8.01/1.48    inference(ennf_transformation,[],[f12])).
% 8.01/1.48  
% 8.01/1.48  fof(f52,plain,(
% 8.01/1.48    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f27])).
% 8.01/1.48  
% 8.01/1.48  fof(f14,axiom,(
% 8.01/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 8.01/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.48  
% 8.01/1.48  fof(f30,plain,(
% 8.01/1.48    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 8.01/1.48    inference(ennf_transformation,[],[f14])).
% 8.01/1.48  
% 8.01/1.48  fof(f55,plain,(
% 8.01/1.48    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 8.01/1.48    inference(cnf_transformation,[],[f30])).
% 8.01/1.48  
% 8.01/1.48  fof(f58,plain,(
% 8.01/1.48    k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1)),
% 8.01/1.48    inference(cnf_transformation,[],[f38])).
% 8.01/1.48  
% 8.01/1.48  cnf(c_209,plain,
% 8.01/1.48      ( X0_43 != X1_43
% 8.01/1.48      | k7_relat_1(X0_43,X0_44) = k7_relat_1(X1_43,X0_44) ),
% 8.01/1.48      theory(equality) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_4167,plain,
% 8.01/1.48      ( k7_relat_1(k8_relat_1(X0_44,X0_43),X0_44) = k7_relat_1(X1_43,X0_44)
% 8.01/1.48      | k8_relat_1(X0_44,X0_43) != X1_43 ),
% 8.01/1.48      inference(instantiation,[status(thm)],[c_209]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_13195,plain,
% 8.01/1.48      ( k7_relat_1(k8_relat_1(X0_44,k2_wellord1(sK3,sK1)),X0_44) = k7_relat_1(k2_wellord1(sK3,sK1),X0_44)
% 8.01/1.48      | k8_relat_1(X0_44,k2_wellord1(sK3,sK1)) != k2_wellord1(sK3,sK1) ),
% 8.01/1.48      inference(instantiation,[status(thm)],[c_4167]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_28271,plain,
% 8.01/1.48      ( k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) = k7_relat_1(k2_wellord1(sK3,sK1),sK2)
% 8.01/1.48      | k8_relat_1(sK2,k2_wellord1(sK3,sK1)) != k2_wellord1(sK3,sK1) ),
% 8.01/1.48      inference(instantiation,[status(thm)],[c_13195]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_200,plain,
% 8.01/1.48      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 8.01/1.48      theory(equality) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_526,plain,
% 8.01/1.48      ( X0_43 != X1_43
% 8.01/1.48      | k2_wellord1(sK3,sK1) != X1_43
% 8.01/1.48      | k2_wellord1(sK3,sK1) = X0_43 ),
% 8.01/1.48      inference(instantiation,[status(thm)],[c_200]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_535,plain,
% 8.01/1.48      ( X0_43 != k2_wellord1(sK3,sK1)
% 8.01/1.48      | k2_wellord1(sK3,sK1) = X0_43
% 8.01/1.48      | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
% 8.01/1.48      inference(instantiation,[status(thm)],[c_526]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_551,plain,
% 8.01/1.48      ( k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1)
% 8.01/1.48      | k2_wellord1(sK3,sK1) = k7_relat_1(k2_wellord1(sK3,sK1),X0_44)
% 8.01/1.48      | k7_relat_1(k2_wellord1(sK3,sK1),X0_44) != k2_wellord1(sK3,sK1) ),
% 8.01/1.48      inference(instantiation,[status(thm)],[c_535]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_17960,plain,
% 8.01/1.48      ( k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1)
% 8.01/1.48      | k2_wellord1(sK3,sK1) = k7_relat_1(k2_wellord1(sK3,sK1),sK2)
% 8.01/1.48      | k7_relat_1(k2_wellord1(sK3,sK1),sK2) != k2_wellord1(sK3,sK1) ),
% 8.01/1.48      inference(instantiation,[status(thm)],[c_551]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_1,plain,
% 8.01/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 8.01/1.48      inference(cnf_transformation,[],[f40]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_193,plain,
% 8.01/1.48      ( r2_hidden(sK0(X0_44,X1_44),X0_44) | r1_tarski(X0_44,X1_44) ),
% 8.01/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_489,plain,
% 8.01/1.48      ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
% 8.01/1.48      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_11,plain,
% 8.01/1.48      ( r2_hidden(X0,X1)
% 8.01/1.48      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
% 8.01/1.48      | ~ v1_relat_1(X2) ),
% 8.01/1.48      inference(cnf_transformation,[],[f54]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_183,plain,
% 8.01/1.48      ( r2_hidden(X0_45,X0_44)
% 8.01/1.48      | ~ r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44)))
% 8.01/1.48      | ~ v1_relat_1(X0_43) ),
% 8.01/1.48      inference(subtyping,[status(esa)],[c_11]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_498,plain,
% 8.01/1.48      ( r2_hidden(X0_45,X0_44) = iProver_top
% 8.01/1.48      | r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44))) != iProver_top
% 8.01/1.48      | v1_relat_1(X0_43) != iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_1407,plain,
% 8.01/1.48      ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44),X0_44) = iProver_top
% 8.01/1.48      | r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44) = iProver_top
% 8.01/1.48      | v1_relat_1(X0_43) != iProver_top ),
% 8.01/1.48      inference(superposition,[status(thm)],[c_489,c_498]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_15,negated_conjecture,
% 8.01/1.48      ( r1_tarski(sK1,sK2) ),
% 8.01/1.48      inference(cnf_transformation,[],[f57]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_179,negated_conjecture,
% 8.01/1.48      ( r1_tarski(sK1,sK2) ),
% 8.01/1.48      inference(subtyping,[status(esa)],[c_15]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_501,plain,
% 8.01/1.48      ( r1_tarski(sK1,sK2) = iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_179]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_2,plain,
% 8.01/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 8.01/1.48      inference(cnf_transformation,[],[f39]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_192,plain,
% 8.01/1.48      ( ~ r2_hidden(X0_45,X0_44)
% 8.01/1.48      | r2_hidden(X0_45,X1_44)
% 8.01/1.48      | ~ r1_tarski(X0_44,X1_44) ),
% 8.01/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_490,plain,
% 8.01/1.48      ( r2_hidden(X0_45,X0_44) != iProver_top
% 8.01/1.48      | r2_hidden(X0_45,X1_44) = iProver_top
% 8.01/1.48      | r1_tarski(X0_44,X1_44) != iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_873,plain,
% 8.01/1.48      ( r2_hidden(X0_45,sK2) = iProver_top
% 8.01/1.48      | r2_hidden(X0_45,sK1) != iProver_top ),
% 8.01/1.48      inference(superposition,[status(thm)],[c_501,c_490]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_7211,plain,
% 8.01/1.48      ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44),sK2) = iProver_top
% 8.01/1.48      | r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44) = iProver_top
% 8.01/1.48      | v1_relat_1(X0_43) != iProver_top ),
% 8.01/1.48      inference(superposition,[status(thm)],[c_1407,c_873]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_0,plain,
% 8.01/1.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 8.01/1.48      inference(cnf_transformation,[],[f41]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_194,plain,
% 8.01/1.48      ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44) | r1_tarski(X0_44,X1_44) ),
% 8.01/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_488,plain,
% 8.01/1.48      ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
% 8.01/1.48      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_194]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_10411,plain,
% 8.01/1.48      ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),sK2) = iProver_top
% 8.01/1.48      | v1_relat_1(X0_43) != iProver_top ),
% 8.01/1.48      inference(superposition,[status(thm)],[c_7211,c_488]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_16,negated_conjecture,
% 8.01/1.48      ( v1_relat_1(sK3) ),
% 8.01/1.48      inference(cnf_transformation,[],[f56]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_178,negated_conjecture,
% 8.01/1.48      ( v1_relat_1(sK3) ),
% 8.01/1.48      inference(subtyping,[status(esa)],[c_16]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_502,plain,
% 8.01/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_178]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_9,plain,
% 8.01/1.48      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 8.01/1.48      inference(cnf_transformation,[],[f51]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_185,plain,
% 8.01/1.48      ( ~ v1_relat_1(X0_43) | v1_relat_1(k2_wellord1(X0_43,X0_44)) ),
% 8.01/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_496,plain,
% 8.01/1.48      ( v1_relat_1(X0_43) != iProver_top
% 8.01/1.48      | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_6,plain,
% 8.01/1.48      ( ~ v1_relat_1(X0)
% 8.01/1.48      | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 8.01/1.48      inference(cnf_transformation,[],[f63]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_188,plain,
% 8.01/1.48      ( ~ v1_relat_1(X0_43)
% 8.01/1.48      | k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
% 8.01/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_493,plain,
% 8.01/1.48      ( k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
% 8.01/1.48      | v1_relat_1(X0_43) != iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_1327,plain,
% 8.01/1.48      ( k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k2_relat_1(k2_wellord1(X0_43,X0_44)))) = k3_relat_1(k2_wellord1(X0_43,X0_44))
% 8.01/1.48      | v1_relat_1(X0_43) != iProver_top ),
% 8.01/1.48      inference(superposition,[status(thm)],[c_496,c_493]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_6038,plain,
% 8.01/1.48      ( k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k2_relat_1(k2_wellord1(sK3,X0_44)))) = k3_relat_1(k2_wellord1(sK3,X0_44)) ),
% 8.01/1.48      inference(superposition,[status(thm)],[c_502,c_1327]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_3,plain,
% 8.01/1.48      ( r1_tarski(X0,X1)
% 8.01/1.48      | ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
% 8.01/1.48      inference(cnf_transformation,[],[f61]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_191,plain,
% 8.01/1.48      ( r1_tarski(X0_44,X1_44)
% 8.01/1.48      | ~ r1_tarski(k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X2_44)),X1_44) ),
% 8.01/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_491,plain,
% 8.01/1.48      ( r1_tarski(X0_44,X1_44) = iProver_top
% 8.01/1.48      | r1_tarski(k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X2_44)),X1_44) != iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_6386,plain,
% 8.01/1.48      ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
% 8.01/1.48      | r1_tarski(k1_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
% 8.01/1.48      inference(superposition,[status(thm)],[c_6038,c_491]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_12147,plain,
% 8.01/1.48      ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
% 8.01/1.48      | v1_relat_1(sK3) != iProver_top ),
% 8.01/1.48      inference(superposition,[status(thm)],[c_10411,c_6386]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_17,plain,
% 8.01/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 8.01/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_13753,plain,
% 8.01/1.48      ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
% 8.01/1.48      inference(global_propositional_subsumption,
% 8.01/1.48                [status(thm)],
% 8.01/1.48                [c_12147,c_17]) ).
% 8.01/1.48  
% 8.01/1.48  cnf(c_8,plain,
% 8.01/1.48      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 8.01/1.48      | ~ v1_relat_1(X0)
% 8.01/1.48      | k7_relat_1(X0,X1) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f50]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_186,plain,
% 8.01/1.49      ( ~ r1_tarski(k1_relat_1(X0_43),X0_44)
% 8.01/1.49      | ~ v1_relat_1(X0_43)
% 8.01/1.49      | k7_relat_1(X0_43,X0_44) = X0_43 ),
% 8.01/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_495,plain,
% 8.01/1.49      ( k7_relat_1(X0_43,X0_44) = X0_43
% 8.01/1.49      | r1_tarski(k1_relat_1(X0_43),X0_44) != iProver_top
% 8.01/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13757,plain,
% 8.01/1.49      ( k7_relat_1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1)
% 8.01/1.49      | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_13753,c_495]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5,plain,
% 8.01/1.49      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f62]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_189,plain,
% 8.01/1.49      ( k2_enumset1(X0_44,X0_44,X0_44,X1_44) = k2_enumset1(X1_44,X1_44,X1_44,X0_44) ),
% 8.01/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_735,plain,
% 8.01/1.49      ( r1_tarski(X0_44,X1_44) = iProver_top
% 8.01/1.49      | r1_tarski(k3_tarski(k2_enumset1(X2_44,X2_44,X2_44,X0_44)),X1_44) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_189,c_491]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6390,plain,
% 8.01/1.49      ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
% 8.01/1.49      | r1_tarski(k2_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_6038,c_735]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_12146,plain,
% 8.01/1.49      ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
% 8.01/1.49      | v1_relat_1(sK3) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_10411,c_6390]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13740,plain,
% 8.01/1.49      ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_12146,c_17]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7,plain,
% 8.01/1.49      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 8.01/1.49      | ~ v1_relat_1(X0)
% 8.01/1.49      | k8_relat_1(X1,X0) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f49]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_187,plain,
% 8.01/1.49      ( ~ r1_tarski(k2_relat_1(X0_43),X0_44)
% 8.01/1.49      | ~ v1_relat_1(X0_43)
% 8.01/1.49      | k8_relat_1(X0_44,X0_43) = X0_43 ),
% 8.01/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_494,plain,
% 8.01/1.49      ( k8_relat_1(X0_44,X0_43) = X0_43
% 8.01/1.49      | r1_tarski(k2_relat_1(X0_43),X0_44) != iProver_top
% 8.01/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13744,plain,
% 8.01/1.49      ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k2_wellord1(sK3,sK1)
% 8.01/1.49      | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_13740,c_494]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_726,plain,
% 8.01/1.49      ( X0_43 != X1_43
% 8.01/1.49      | X0_43 = k7_relat_1(k8_relat_1(X0_44,X2_43),X0_44)
% 8.01/1.49      | k7_relat_1(k8_relat_1(X0_44,X2_43),X0_44) != X1_43 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_813,plain,
% 8.01/1.49      ( X0_43 != k7_relat_1(X1_43,X0_44)
% 8.01/1.49      | X0_43 = k7_relat_1(k8_relat_1(X0_44,X2_43),X0_44)
% 8.01/1.49      | k7_relat_1(k8_relat_1(X0_44,X2_43),X0_44) != k7_relat_1(X1_43,X0_44) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_726]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1438,plain,
% 8.01/1.49      ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),X0_44)
% 8.01/1.49      | k2_wellord1(sK3,sK1) = k7_relat_1(k8_relat_1(X0_44,X0_43),X0_44)
% 8.01/1.49      | k7_relat_1(k8_relat_1(X0_44,X0_43),X0_44) != k7_relat_1(k2_wellord1(sK3,sK1),X0_44) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_813]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5247,plain,
% 8.01/1.49      ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),sK2)
% 8.01/1.49      | k2_wellord1(sK3,sK1) = k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,X0_44)),sK2)
% 8.01/1.49      | k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,X0_44)),sK2) != k7_relat_1(k2_wellord1(sK3,sK1),sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_1438]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5252,plain,
% 8.01/1.49      ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),sK2)
% 8.01/1.49      | k2_wellord1(sK3,sK1) = k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2)
% 8.01/1.49      | k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) != k7_relat_1(k2_wellord1(sK3,sK1),sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_5247]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_541,plain,
% 8.01/1.49      ( k2_wellord1(X0_43,X0_44) != X1_43
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X1_43
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(X0_43,X0_44) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3224,plain,
% 8.01/1.49      ( k2_wellord1(X0_43,X0_44) != k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,X1_44)),sK2)
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(X0_43,X0_44)
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,X1_44)),sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_541]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3225,plain,
% 8.01/1.49      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(sK3,sK1)
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2)
% 8.01/1.49      | k2_wellord1(sK3,sK1) != k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_3224]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0)
% 8.01/1.49      | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f52]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_184,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0_43)
% 8.01/1.49      | k7_relat_1(k8_relat_1(X0_44,X0_43),X0_44) = k2_wellord1(X0_43,X0_44) ),
% 8.01/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1401,plain,
% 8.01/1.49      ( ~ v1_relat_1(k2_wellord1(sK3,sK1))
% 8.01/1.49      | k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) = k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_184]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_580,plain,
% 8.01/1.49      ( X0_43 != X1_43
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X1_43
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = X0_43 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_638,plain,
% 8.01/1.49      ( X0_43 != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = X0_43
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_580]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_959,plain,
% 8.01/1.49      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2)
% 8.01/1.49      | k7_relat_1(k8_relat_1(sK2,k2_wellord1(sK3,sK1)),sK2) != k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_638]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0)
% 8.01/1.49      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_181,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0_43)
% 8.01/1.49      | k2_wellord1(k2_wellord1(X0_43,X0_44),X1_44) = k2_wellord1(k2_wellord1(X0_43,X1_44),X0_44) ),
% 8.01/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_630,plain,
% 8.01/1.49      ( ~ v1_relat_1(sK3)
% 8.01/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_181]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_520,plain,
% 8.01/1.49      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X0_43
% 8.01/1.49      | k2_wellord1(sK3,sK1) != X0_43
% 8.01/1.49      | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_525,plain,
% 8.01/1.49      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(sK3,sK1)
% 8.01/1.49      | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1)
% 8.01/1.49      | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_520]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_14,negated_conjecture,
% 8.01/1.49      ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f58]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_180,negated_conjecture,
% 8.01/1.49      ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 8.01/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_239,plain,
% 8.01/1.49      ( v1_relat_1(X0_43) != iProver_top
% 8.01/1.49      | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_241,plain,
% 8.01/1.49      ( v1_relat_1(k2_wellord1(sK3,sK1)) = iProver_top
% 8.01/1.49      | v1_relat_1(sK3) != iProver_top ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_239]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_240,plain,
% 8.01/1.49      ( v1_relat_1(k2_wellord1(sK3,sK1)) | ~ v1_relat_1(sK3) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_185]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_197,plain,( X0_44 = X0_44 ),theory(equality) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_221,plain,
% 8.01/1.49      ( sK1 = sK1 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_197]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_196,plain,( X0_43 = X0_43 ),theory(equality) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_220,plain,
% 8.01/1.49      ( sK3 = sK3 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_196]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_210,plain,
% 8.01/1.49      ( X0_44 != X1_44
% 8.01/1.49      | X0_43 != X1_43
% 8.01/1.49      | k2_wellord1(X0_43,X0_44) = k2_wellord1(X1_43,X1_44) ),
% 8.01/1.49      theory(equality) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_218,plain,
% 8.01/1.49      ( sK1 != sK1
% 8.01/1.49      | k2_wellord1(sK3,sK1) = k2_wellord1(sK3,sK1)
% 8.01/1.49      | sK3 != sK3 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_210]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(contradiction,plain,
% 8.01/1.49      ( $false ),
% 8.01/1.49      inference(minisat,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_28271,c_17960,c_13757,c_13744,c_5252,c_3225,c_1401,
% 8.01/1.49                 c_959,c_630,c_525,c_180,c_241,c_240,c_221,c_220,c_218,
% 8.01/1.49                 c_17,c_16]) ).
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  ------                               Statistics
% 8.01/1.49  
% 8.01/1.49  ------ General
% 8.01/1.49  
% 8.01/1.49  abstr_ref_over_cycles:                  0
% 8.01/1.49  abstr_ref_under_cycles:                 0
% 8.01/1.49  gc_basic_clause_elim:                   0
% 8.01/1.49  forced_gc_time:                         0
% 8.01/1.49  parsing_time:                           0.009
% 8.01/1.49  unif_index_cands_time:                  0.
% 8.01/1.49  unif_index_add_time:                    0.
% 8.01/1.49  orderings_time:                         0.
% 8.01/1.49  out_proof_time:                         0.009
% 8.01/1.49  total_time:                             0.873
% 8.01/1.49  num_of_symbols:                         47
% 8.01/1.49  num_of_terms:                           23935
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing
% 8.01/1.49  
% 8.01/1.49  num_of_splits:                          0
% 8.01/1.49  num_of_split_atoms:                     0
% 8.01/1.49  num_of_reused_defs:                     0
% 8.01/1.49  num_eq_ax_congr_red:                    14
% 8.01/1.49  num_of_sem_filtered_clauses:            1
% 8.01/1.49  num_of_subtypes:                        4
% 8.01/1.49  monotx_restored_types:                  0
% 8.01/1.49  sat_num_of_epr_types:                   0
% 8.01/1.49  sat_num_of_non_cyclic_types:            0
% 8.01/1.49  sat_guarded_non_collapsed_types:        1
% 8.01/1.49  num_pure_diseq_elim:                    0
% 8.01/1.49  simp_replaced_by:                       0
% 8.01/1.49  res_preprocessed:                       82
% 8.01/1.49  prep_upred:                             0
% 8.01/1.49  prep_unflattend:                        0
% 8.01/1.49  smt_new_axioms:                         0
% 8.01/1.49  pred_elim_cands:                        3
% 8.01/1.49  pred_elim:                              0
% 8.01/1.49  pred_elim_cl:                           0
% 8.01/1.49  pred_elim_cycles:                       1
% 8.01/1.49  merged_defs:                            0
% 8.01/1.49  merged_defs_ncl:                        0
% 8.01/1.49  bin_hyper_res:                          0
% 8.01/1.49  prep_cycles:                            3
% 8.01/1.49  pred_elim_time:                         0.
% 8.01/1.49  splitting_time:                         0.
% 8.01/1.49  sem_filter_time:                        0.
% 8.01/1.49  monotx_time:                            0.
% 8.01/1.49  subtype_inf_time:                       0.
% 8.01/1.49  
% 8.01/1.49  ------ Problem properties
% 8.01/1.49  
% 8.01/1.49  clauses:                                17
% 8.01/1.49  conjectures:                            3
% 8.01/1.49  epr:                                    4
% 8.01/1.49  horn:                                   16
% 8.01/1.49  ground:                                 3
% 8.01/1.49  unary:                                  4
% 8.01/1.49  binary:                                 7
% 8.01/1.49  lits:                                   36
% 8.01/1.49  lits_eq:                                7
% 8.01/1.49  fd_pure:                                0
% 8.01/1.49  fd_pseudo:                              0
% 8.01/1.49  fd_cond:                                0
% 8.01/1.49  fd_pseudo_cond:                         0
% 8.01/1.49  ac_symbols:                             0
% 8.01/1.49  
% 8.01/1.49  ------ Propositional Solver
% 8.01/1.49  
% 8.01/1.49  prop_solver_calls:                      29
% 8.01/1.49  prop_fast_solver_calls:                 746
% 8.01/1.49  smt_solver_calls:                       0
% 8.01/1.49  smt_fast_solver_calls:                  0
% 8.01/1.49  prop_num_of_clauses:                    9082
% 8.01/1.49  prop_preprocess_simplified:             13561
% 8.01/1.49  prop_fo_subsumed:                       17
% 8.01/1.49  prop_solver_time:                       0.
% 8.01/1.49  smt_solver_time:                        0.
% 8.01/1.49  smt_fast_solver_time:                   0.
% 8.01/1.49  prop_fast_solver_time:                  0.
% 8.01/1.49  prop_unsat_core_time:                   0.001
% 8.01/1.49  
% 8.01/1.49  ------ QBF
% 8.01/1.49  
% 8.01/1.49  qbf_q_res:                              0
% 8.01/1.49  qbf_num_tautologies:                    0
% 8.01/1.49  qbf_prep_cycles:                        0
% 8.01/1.49  
% 8.01/1.49  ------ BMC1
% 8.01/1.49  
% 8.01/1.49  bmc1_current_bound:                     -1
% 8.01/1.49  bmc1_last_solved_bound:                 -1
% 8.01/1.49  bmc1_unsat_core_size:                   -1
% 8.01/1.49  bmc1_unsat_core_parents_size:           -1
% 8.01/1.49  bmc1_merge_next_fun:                    0
% 8.01/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation
% 8.01/1.49  
% 8.01/1.49  inst_num_of_clauses:                    2528
% 8.01/1.49  inst_num_in_passive:                    540
% 8.01/1.49  inst_num_in_active:                     930
% 8.01/1.49  inst_num_in_unprocessed:                1058
% 8.01/1.49  inst_num_of_loops:                      1104
% 8.01/1.49  inst_num_of_learning_restarts:          0
% 8.01/1.49  inst_num_moves_active_passive:          170
% 8.01/1.49  inst_lit_activity:                      0
% 8.01/1.49  inst_lit_activity_moves:                0
% 8.01/1.49  inst_num_tautologies:                   0
% 8.01/1.49  inst_num_prop_implied:                  0
% 8.01/1.49  inst_num_existing_simplified:           0
% 8.01/1.49  inst_num_eq_res_simplified:             0
% 8.01/1.49  inst_num_child_elim:                    0
% 8.01/1.49  inst_num_of_dismatching_blockings:      3979
% 8.01/1.49  inst_num_of_non_proper_insts:           5044
% 8.01/1.49  inst_num_of_duplicates:                 0
% 8.01/1.49  inst_inst_num_from_inst_to_res:         0
% 8.01/1.49  inst_dismatching_checking_time:         0.
% 8.01/1.49  
% 8.01/1.49  ------ Resolution
% 8.01/1.49  
% 8.01/1.49  res_num_of_clauses:                     0
% 8.01/1.49  res_num_in_passive:                     0
% 8.01/1.49  res_num_in_active:                      0
% 8.01/1.49  res_num_of_loops:                       85
% 8.01/1.49  res_forward_subset_subsumed:            458
% 8.01/1.49  res_backward_subset_subsumed:           2
% 8.01/1.49  res_forward_subsumed:                   0
% 8.01/1.49  res_backward_subsumed:                  0
% 8.01/1.49  res_forward_subsumption_resolution:     0
% 8.01/1.49  res_backward_subsumption_resolution:    0
% 8.01/1.49  res_clause_to_clause_subsumption:       9425
% 8.01/1.49  res_orphan_elimination:                 0
% 8.01/1.49  res_tautology_del:                      820
% 8.01/1.49  res_num_eq_res_simplified:              0
% 8.01/1.49  res_num_sel_changes:                    0
% 8.01/1.49  res_moves_from_active_to_pass:          0
% 8.01/1.49  
% 8.01/1.49  ------ Superposition
% 8.01/1.49  
% 8.01/1.49  sup_time_total:                         0.
% 8.01/1.49  sup_time_generating:                    0.
% 8.01/1.49  sup_time_sim_full:                      0.
% 8.01/1.49  sup_time_sim_immed:                     0.
% 8.01/1.49  
% 8.01/1.49  sup_num_of_clauses:                     1887
% 8.01/1.49  sup_num_in_active:                      209
% 8.01/1.49  sup_num_in_passive:                     1678
% 8.01/1.49  sup_num_of_loops:                       220
% 8.01/1.49  sup_fw_superposition:                   2593
% 8.01/1.49  sup_bw_superposition:                   2692
% 8.01/1.49  sup_immediate_simplified:               964
% 8.01/1.49  sup_given_eliminated:                   0
% 8.01/1.49  comparisons_done:                       0
% 8.01/1.49  comparisons_avoided:                    0
% 8.01/1.49  
% 8.01/1.49  ------ Simplifications
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  sim_fw_subset_subsumed:                 2
% 8.01/1.49  sim_bw_subset_subsumed:                 13
% 8.01/1.49  sim_fw_subsumed:                        159
% 8.01/1.49  sim_bw_subsumed:                        0
% 8.01/1.49  sim_fw_subsumption_res:                 0
% 8.01/1.49  sim_bw_subsumption_res:                 0
% 8.01/1.49  sim_tautology_del:                      34
% 8.01/1.49  sim_eq_tautology_del:                   76
% 8.01/1.49  sim_eq_res_simp:                        0
% 8.01/1.49  sim_fw_demodulated:                     310
% 8.01/1.49  sim_bw_demodulated:                     13
% 8.01/1.49  sim_light_normalised:                   655
% 8.01/1.49  sim_joinable_taut:                      0
% 8.01/1.49  sim_joinable_simp:                      0
% 8.01/1.49  sim_ac_normalised:                      0
% 8.01/1.49  sim_smt_subsumption:                    0
% 8.01/1.49  
%------------------------------------------------------------------------------
