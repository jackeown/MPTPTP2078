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
% DateTime   : Thu Dec  3 11:54:22 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 367 expanded)
%              Number of clauses        :   87 ( 144 expanded)
%              Number of leaves         :   21 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  323 ( 889 expanded)
%              Number of equality atoms :  158 ( 314 expanded)
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

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1)
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f36])).

fof(f56,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f62,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f58,f58])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_192,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_502,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_182,plain,
    ( r2_hidden(X0_45,X0_44)
    | ~ r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44)))
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_511,plain,
    ( r2_hidden(X0_45,X0_44) = iProver_top
    | r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44))) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_182])).

cnf(c_1682,plain,
    ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44),X0_44) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_511])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_178,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_514,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_178])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_191,plain,
    ( ~ r2_hidden(X0_45,X0_44)
    | r2_hidden(X0_45,X1_44)
    | ~ r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_503,plain,
    ( r2_hidden(X0_45,X0_44) != iProver_top
    | r2_hidden(X0_45,X1_44) = iProver_top
    | r1_tarski(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_779,plain,
    ( r2_hidden(X0_45,sK2) = iProver_top
    | r2_hidden(X0_45,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_514,c_503])).

cnf(c_18320,plain,
    ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44),sK2) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_779])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_193,plain,
    ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_501,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_20194,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),sK2) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_18320,c_501])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_177,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_515,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_177])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_184,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k2_wellord1(X0_43,X0_44)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_509,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_187,plain,
    ( ~ v1_relat_1(X0_43)
    | k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_506,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_1368,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k2_relat_1(k2_wellord1(X0_43,X0_44)))) = k3_relat_1(k2_wellord1(X0_43,X0_44))
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_509,c_506])).

cnf(c_10893,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k2_relat_1(k2_wellord1(sK3,X0_44)))) = k3_relat_1(k2_wellord1(sK3,X0_44)) ),
    inference(superposition,[status(thm)],[c_515,c_1368])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_189,plain,
    ( r1_tarski(X0_44,k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X1_44))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_505,plain,
    ( r1_tarski(X0_44,k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X1_44))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_190,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(X1_44,X2_44)
    | r1_tarski(X0_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_504,plain,
    ( r1_tarski(X0_44,X1_44) != iProver_top
    | r1_tarski(X1_44,X2_44) != iProver_top
    | r1_tarski(X0_44,X2_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_891,plain,
    ( r1_tarski(X0_44,X1_44) = iProver_top
    | r1_tarski(k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X2_44)),X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_504])).

cnf(c_12210,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
    | r1_tarski(k1_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_10893,c_891])).

cnf(c_22494,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_20194,c_12210])).

cnf(c_17,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_30177,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22494,c_17])).

cnf(c_8,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_185,plain,
    ( ~ r1_tarski(k1_relat_1(X0_43),X0_44)
    | ~ v1_relat_1(X0_43)
    | k7_relat_1(X0_43,X0_44) = X0_43 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_508,plain,
    ( k7_relat_1(X0_43,X0_44) = X0_43
    | r1_tarski(k1_relat_1(X0_43),X0_44) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_30182,plain,
    ( k7_relat_1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1)
    | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30177,c_508])).

cnf(c_238,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_240,plain,
    ( v1_relat_1(k2_wellord1(sK3,sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_33522,plain,
    ( k7_relat_1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30182,c_17,c_240])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(X1,k7_relat_1(X0,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_183,plain,
    ( ~ v1_relat_1(X0_43)
    | k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) = k2_wellord1(X0_43,X0_44) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_510,plain,
    ( k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) = k2_wellord1(X0_43,X0_44)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_717,plain,
    ( k8_relat_1(X0_44,k7_relat_1(k2_wellord1(X0_43,X1_44),X0_44)) = k2_wellord1(k2_wellord1(X0_43,X1_44),X0_44)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_509,c_510])).

cnf(c_2971,plain,
    ( k8_relat_1(X0_44,k7_relat_1(k2_wellord1(sK3,X1_44),X0_44)) = k2_wellord1(k2_wellord1(sK3,X1_44),X0_44) ),
    inference(superposition,[status(thm)],[c_515,c_717])).

cnf(c_33525,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK1),sK2) = k8_relat_1(sK2,k2_wellord1(sK3,sK1)) ),
    inference(superposition,[status(thm)],[c_33522,c_2971])).

cnf(c_5,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_188,plain,
    ( k2_enumset1(X0_44,X0_44,X0_44,X1_44) = k2_enumset1(X1_44,X1_44,X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_685,plain,
    ( r1_tarski(X0_44,k3_tarski(k2_enumset1(X1_44,X1_44,X1_44,X0_44))) = iProver_top ),
    inference(superposition,[status(thm)],[c_188,c_505])).

cnf(c_892,plain,
    ( r1_tarski(X0_44,X1_44) = iProver_top
    | r1_tarski(k3_tarski(k2_enumset1(X2_44,X2_44,X2_44,X0_44)),X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_504])).

cnf(c_12212,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_10893,c_892])).

cnf(c_22493,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_20194,c_12212])).

cnf(c_30151,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22493,c_17])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_186,plain,
    ( ~ r1_tarski(k2_relat_1(X0_43),X0_44)
    | ~ v1_relat_1(X0_43)
    | k8_relat_1(X0_44,X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_507,plain,
    ( k8_relat_1(X0_44,X0_43) = X0_43
    | r1_tarski(k2_relat_1(X0_43),X0_44) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_30156,plain,
    ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k2_wellord1(sK3,sK1)
    | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30151,c_507])).

cnf(c_33424,plain,
    ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k2_wellord1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30156,c_17,c_240])).

cnf(c_33526,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1) ),
    inference(light_normalisation,[status(thm)],[c_33525,c_33424])).

cnf(c_199,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_697,plain,
    ( X0_43 != X1_43
    | k2_wellord1(sK3,sK1) != X1_43
    | k2_wellord1(sK3,sK1) = X0_43 ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_743,plain,
    ( X0_43 != k2_wellord1(sK3,sK1)
    | k2_wellord1(sK3,sK1) = X0_43
    | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_828,plain,
    ( k2_wellord1(X0_43,X0_44) != k2_wellord1(sK3,sK1)
    | k2_wellord1(sK3,sK1) = k2_wellord1(X0_43,X0_44)
    | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_996,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK1),sK2) != k2_wellord1(sK3,sK1)
    | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK1),sK2)
    | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_180,plain,
    ( ~ v1_relat_1(X0_43)
    | k2_wellord1(k2_wellord1(X0_43,X0_44),X1_44) = k2_wellord1(k2_wellord1(X0_43,X1_44),X0_44) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_749,plain,
    ( ~ v1_relat_1(sK3)
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_672,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X0_43
    | k2_wellord1(sK3,sK1) != X0_43
    | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_698,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(X0_43,X0_44)
    | k2_wellord1(sK3,sK1) != k2_wellord1(X0_43,X0_44)
    | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_748,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
    | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1)
    | k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_14,negated_conjecture,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_179,negated_conjecture,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_196,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_220,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_195,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_219,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_209,plain,
    ( X0_44 != X1_44
    | X0_43 != X1_43
    | k2_wellord1(X0_43,X0_44) = k2_wellord1(X1_43,X1_44) ),
    theory(equality)).

cnf(c_217,plain,
    ( sK1 != sK1
    | k2_wellord1(sK3,sK1) = k2_wellord1(sK3,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33526,c_996,c_749,c_748,c_179,c_220,c_219,c_217,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:01:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.89/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/1.49  
% 7.89/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.49  
% 7.89/1.49  ------  iProver source info
% 7.89/1.49  
% 7.89/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.49  git: non_committed_changes: false
% 7.89/1.49  git: last_make_outside_of_git: false
% 7.89/1.49  
% 7.89/1.49  ------ 
% 7.89/1.49  
% 7.89/1.49  ------ Input Options
% 7.89/1.49  
% 7.89/1.49  --out_options                           all
% 7.89/1.49  --tptp_safe_out                         true
% 7.89/1.49  --problem_path                          ""
% 7.89/1.49  --include_path                          ""
% 7.89/1.49  --clausifier                            res/vclausify_rel
% 7.89/1.49  --clausifier_options                    --mode clausify
% 7.89/1.49  --stdin                                 false
% 7.89/1.49  --stats_out                             all
% 7.89/1.49  
% 7.89/1.49  ------ General Options
% 7.89/1.49  
% 7.89/1.49  --fof                                   false
% 7.89/1.49  --time_out_real                         305.
% 7.89/1.49  --time_out_virtual                      -1.
% 7.89/1.49  --symbol_type_check                     false
% 7.89/1.49  --clausify_out                          false
% 7.89/1.49  --sig_cnt_out                           false
% 7.89/1.49  --trig_cnt_out                          false
% 7.89/1.49  --trig_cnt_out_tolerance                1.
% 7.89/1.49  --trig_cnt_out_sk_spl                   false
% 7.89/1.49  --abstr_cl_out                          false
% 7.89/1.49  
% 7.89/1.49  ------ Global Options
% 7.89/1.49  
% 7.89/1.49  --schedule                              default
% 7.89/1.49  --add_important_lit                     false
% 7.89/1.49  --prop_solver_per_cl                    1000
% 7.89/1.49  --min_unsat_core                        false
% 7.89/1.49  --soft_assumptions                      false
% 7.89/1.49  --soft_lemma_size                       3
% 7.89/1.49  --prop_impl_unit_size                   0
% 7.89/1.49  --prop_impl_unit                        []
% 7.89/1.49  --share_sel_clauses                     true
% 7.89/1.49  --reset_solvers                         false
% 7.89/1.49  --bc_imp_inh                            [conj_cone]
% 7.89/1.49  --conj_cone_tolerance                   3.
% 7.89/1.49  --extra_neg_conj                        none
% 7.89/1.49  --large_theory_mode                     true
% 7.89/1.49  --prolific_symb_bound                   200
% 7.89/1.49  --lt_threshold                          2000
% 7.89/1.49  --clause_weak_htbl                      true
% 7.89/1.49  --gc_record_bc_elim                     false
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing Options
% 7.89/1.49  
% 7.89/1.49  --preprocessing_flag                    true
% 7.89/1.49  --time_out_prep_mult                    0.1
% 7.89/1.49  --splitting_mode                        input
% 7.89/1.49  --splitting_grd                         true
% 7.89/1.49  --splitting_cvd                         false
% 7.89/1.49  --splitting_cvd_svl                     false
% 7.89/1.49  --splitting_nvd                         32
% 7.89/1.49  --sub_typing                            true
% 7.89/1.49  --prep_gs_sim                           true
% 7.89/1.49  --prep_unflatten                        true
% 7.89/1.49  --prep_res_sim                          true
% 7.89/1.49  --prep_upred                            true
% 7.89/1.49  --prep_sem_filter                       exhaustive
% 7.89/1.49  --prep_sem_filter_out                   false
% 7.89/1.49  --pred_elim                             true
% 7.89/1.49  --res_sim_input                         true
% 7.89/1.49  --eq_ax_congr_red                       true
% 7.89/1.49  --pure_diseq_elim                       true
% 7.89/1.49  --brand_transform                       false
% 7.89/1.49  --non_eq_to_eq                          false
% 7.89/1.49  --prep_def_merge                        true
% 7.89/1.49  --prep_def_merge_prop_impl              false
% 7.89/1.49  --prep_def_merge_mbd                    true
% 7.89/1.49  --prep_def_merge_tr_red                 false
% 7.89/1.49  --prep_def_merge_tr_cl                  false
% 7.89/1.49  --smt_preprocessing                     true
% 7.89/1.49  --smt_ac_axioms                         fast
% 7.89/1.49  --preprocessed_out                      false
% 7.89/1.49  --preprocessed_stats                    false
% 7.89/1.49  
% 7.89/1.49  ------ Abstraction refinement Options
% 7.89/1.49  
% 7.89/1.49  --abstr_ref                             []
% 7.89/1.49  --abstr_ref_prep                        false
% 7.89/1.49  --abstr_ref_until_sat                   false
% 7.89/1.49  --abstr_ref_sig_restrict                funpre
% 7.89/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.49  --abstr_ref_under                       []
% 7.89/1.49  
% 7.89/1.49  ------ SAT Options
% 7.89/1.49  
% 7.89/1.49  --sat_mode                              false
% 7.89/1.49  --sat_fm_restart_options                ""
% 7.89/1.49  --sat_gr_def                            false
% 7.89/1.49  --sat_epr_types                         true
% 7.89/1.49  --sat_non_cyclic_types                  false
% 7.89/1.49  --sat_finite_models                     false
% 7.89/1.49  --sat_fm_lemmas                         false
% 7.89/1.49  --sat_fm_prep                           false
% 7.89/1.49  --sat_fm_uc_incr                        true
% 7.89/1.49  --sat_out_model                         small
% 7.89/1.49  --sat_out_clauses                       false
% 7.89/1.49  
% 7.89/1.49  ------ QBF Options
% 7.89/1.49  
% 7.89/1.49  --qbf_mode                              false
% 7.89/1.49  --qbf_elim_univ                         false
% 7.89/1.49  --qbf_dom_inst                          none
% 7.89/1.49  --qbf_dom_pre_inst                      false
% 7.89/1.49  --qbf_sk_in                             false
% 7.89/1.49  --qbf_pred_elim                         true
% 7.89/1.49  --qbf_split                             512
% 7.89/1.49  
% 7.89/1.49  ------ BMC1 Options
% 7.89/1.49  
% 7.89/1.49  --bmc1_incremental                      false
% 7.89/1.49  --bmc1_axioms                           reachable_all
% 7.89/1.49  --bmc1_min_bound                        0
% 7.89/1.49  --bmc1_max_bound                        -1
% 7.89/1.49  --bmc1_max_bound_default                -1
% 7.89/1.49  --bmc1_symbol_reachability              true
% 7.89/1.49  --bmc1_property_lemmas                  false
% 7.89/1.49  --bmc1_k_induction                      false
% 7.89/1.49  --bmc1_non_equiv_states                 false
% 7.89/1.49  --bmc1_deadlock                         false
% 7.89/1.49  --bmc1_ucm                              false
% 7.89/1.49  --bmc1_add_unsat_core                   none
% 7.89/1.49  --bmc1_unsat_core_children              false
% 7.89/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.89/1.49  --bmc1_out_stat                         full
% 7.89/1.49  --bmc1_ground_init                      false
% 7.89/1.49  --bmc1_pre_inst_next_state              false
% 7.89/1.49  --bmc1_pre_inst_state                   false
% 7.89/1.49  --bmc1_pre_inst_reach_state             false
% 7.89/1.49  --bmc1_out_unsat_core                   false
% 7.89/1.49  --bmc1_aig_witness_out                  false
% 7.89/1.49  --bmc1_verbose                          false
% 7.89/1.49  --bmc1_dump_clauses_tptp                false
% 7.89/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.89/1.49  --bmc1_dump_file                        -
% 7.89/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.89/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.89/1.49  --bmc1_ucm_extend_mode                  1
% 7.89/1.49  --bmc1_ucm_init_mode                    2
% 7.89/1.49  --bmc1_ucm_cone_mode                    none
% 7.89/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.89/1.49  --bmc1_ucm_relax_model                  4
% 7.89/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.89/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.89/1.49  --bmc1_ucm_layered_model                none
% 7.89/1.49  --bmc1_ucm_max_lemma_size               10
% 7.89/1.49  
% 7.89/1.49  ------ AIG Options
% 7.89/1.49  
% 7.89/1.49  --aig_mode                              false
% 7.89/1.49  
% 7.89/1.49  ------ Instantiation Options
% 7.89/1.49  
% 7.89/1.49  --instantiation_flag                    true
% 7.89/1.49  --inst_sos_flag                         false
% 7.89/1.49  --inst_sos_phase                        true
% 7.89/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel_side                     num_symb
% 7.89/1.49  --inst_solver_per_active                1400
% 7.89/1.49  --inst_solver_calls_frac                1.
% 7.89/1.49  --inst_passive_queue_type               priority_queues
% 7.89/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.89/1.49  --inst_passive_queues_freq              [25;2]
% 7.89/1.49  --inst_dismatching                      true
% 7.89/1.49  --inst_eager_unprocessed_to_passive     true
% 7.89/1.49  --inst_prop_sim_given                   true
% 7.89/1.49  --inst_prop_sim_new                     false
% 7.89/1.49  --inst_subs_new                         false
% 7.89/1.49  --inst_eq_res_simp                      false
% 7.89/1.49  --inst_subs_given                       false
% 7.89/1.49  --inst_orphan_elimination               true
% 7.89/1.49  --inst_learning_loop_flag               true
% 7.89/1.49  --inst_learning_start                   3000
% 7.89/1.49  --inst_learning_factor                  2
% 7.89/1.49  --inst_start_prop_sim_after_learn       3
% 7.89/1.49  --inst_sel_renew                        solver
% 7.89/1.49  --inst_lit_activity_flag                true
% 7.89/1.49  --inst_restr_to_given                   false
% 7.89/1.49  --inst_activity_threshold               500
% 7.89/1.49  --inst_out_proof                        true
% 7.89/1.49  
% 7.89/1.49  ------ Resolution Options
% 7.89/1.49  
% 7.89/1.49  --resolution_flag                       true
% 7.89/1.49  --res_lit_sel                           adaptive
% 7.89/1.49  --res_lit_sel_side                      none
% 7.89/1.49  --res_ordering                          kbo
% 7.89/1.49  --res_to_prop_solver                    active
% 7.89/1.49  --res_prop_simpl_new                    false
% 7.89/1.49  --res_prop_simpl_given                  true
% 7.89/1.49  --res_passive_queue_type                priority_queues
% 7.89/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.89/1.49  --res_passive_queues_freq               [15;5]
% 7.89/1.49  --res_forward_subs                      full
% 7.89/1.49  --res_backward_subs                     full
% 7.89/1.49  --res_forward_subs_resolution           true
% 7.89/1.49  --res_backward_subs_resolution          true
% 7.89/1.49  --res_orphan_elimination                true
% 7.89/1.49  --res_time_limit                        2.
% 7.89/1.49  --res_out_proof                         true
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Options
% 7.89/1.49  
% 7.89/1.49  --superposition_flag                    true
% 7.89/1.49  --sup_passive_queue_type                priority_queues
% 7.89/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.89/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.89/1.49  --demod_completeness_check              fast
% 7.89/1.49  --demod_use_ground                      true
% 7.89/1.49  --sup_to_prop_solver                    passive
% 7.89/1.49  --sup_prop_simpl_new                    true
% 7.89/1.49  --sup_prop_simpl_given                  true
% 7.89/1.49  --sup_fun_splitting                     false
% 7.89/1.49  --sup_smt_interval                      50000
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Simplification Setup
% 7.89/1.49  
% 7.89/1.49  --sup_indices_passive                   []
% 7.89/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.89/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.49  --sup_full_bw                           [BwDemod]
% 7.89/1.49  --sup_immed_triv                        [TrivRules]
% 7.89/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.49  --sup_immed_bw_main                     []
% 7.89/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.89/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.89/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.89/1.49  
% 7.89/1.49  ------ Combination Options
% 7.89/1.49  
% 7.89/1.49  --comb_res_mult                         3
% 7.89/1.49  --comb_sup_mult                         2
% 7.89/1.49  --comb_inst_mult                        10
% 7.89/1.49  
% 7.89/1.49  ------ Debug Options
% 7.89/1.49  
% 7.89/1.49  --dbg_backtrace                         false
% 7.89/1.49  --dbg_dump_prop_clauses                 false
% 7.89/1.49  --dbg_dump_prop_clauses_file            -
% 7.89/1.49  --dbg_out_stat                          false
% 7.89/1.49  ------ Parsing...
% 7.89/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.49  ------ Proving...
% 7.89/1.49  ------ Problem Properties 
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  clauses                                 17
% 7.89/1.49  conjectures                             3
% 7.89/1.49  EPR                                     4
% 7.89/1.49  Horn                                    16
% 7.89/1.49  unary                                   5
% 7.89/1.49  binary                                  6
% 7.89/1.49  lits                                    35
% 7.89/1.49  lits eq                                 7
% 7.89/1.49  fd_pure                                 0
% 7.89/1.49  fd_pseudo                               0
% 7.89/1.49  fd_cond                                 0
% 7.89/1.49  fd_pseudo_cond                          0
% 7.89/1.49  AC symbols                              0
% 7.89/1.49  
% 7.89/1.49  ------ Schedule dynamic 5 is on 
% 7.89/1.49  
% 7.89/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  ------ 
% 7.89/1.49  Current options:
% 7.89/1.49  ------ 
% 7.89/1.49  
% 7.89/1.49  ------ Input Options
% 7.89/1.49  
% 7.89/1.49  --out_options                           all
% 7.89/1.49  --tptp_safe_out                         true
% 7.89/1.49  --problem_path                          ""
% 7.89/1.49  --include_path                          ""
% 7.89/1.49  --clausifier                            res/vclausify_rel
% 7.89/1.49  --clausifier_options                    --mode clausify
% 7.89/1.49  --stdin                                 false
% 7.89/1.49  --stats_out                             all
% 7.89/1.49  
% 7.89/1.49  ------ General Options
% 7.89/1.49  
% 7.89/1.49  --fof                                   false
% 7.89/1.49  --time_out_real                         305.
% 7.89/1.49  --time_out_virtual                      -1.
% 7.89/1.49  --symbol_type_check                     false
% 7.89/1.49  --clausify_out                          false
% 7.89/1.49  --sig_cnt_out                           false
% 7.89/1.49  --trig_cnt_out                          false
% 7.89/1.49  --trig_cnt_out_tolerance                1.
% 7.89/1.49  --trig_cnt_out_sk_spl                   false
% 7.89/1.49  --abstr_cl_out                          false
% 7.89/1.49  
% 7.89/1.49  ------ Global Options
% 7.89/1.49  
% 7.89/1.49  --schedule                              default
% 7.89/1.49  --add_important_lit                     false
% 7.89/1.49  --prop_solver_per_cl                    1000
% 7.89/1.49  --min_unsat_core                        false
% 7.89/1.49  --soft_assumptions                      false
% 7.89/1.49  --soft_lemma_size                       3
% 7.89/1.49  --prop_impl_unit_size                   0
% 7.89/1.49  --prop_impl_unit                        []
% 7.89/1.49  --share_sel_clauses                     true
% 7.89/1.49  --reset_solvers                         false
% 7.89/1.49  --bc_imp_inh                            [conj_cone]
% 7.89/1.49  --conj_cone_tolerance                   3.
% 7.89/1.49  --extra_neg_conj                        none
% 7.89/1.49  --large_theory_mode                     true
% 7.89/1.49  --prolific_symb_bound                   200
% 7.89/1.49  --lt_threshold                          2000
% 7.89/1.49  --clause_weak_htbl                      true
% 7.89/1.49  --gc_record_bc_elim                     false
% 7.89/1.49  
% 7.89/1.49  ------ Preprocessing Options
% 7.89/1.49  
% 7.89/1.49  --preprocessing_flag                    true
% 7.89/1.49  --time_out_prep_mult                    0.1
% 7.89/1.49  --splitting_mode                        input
% 7.89/1.49  --splitting_grd                         true
% 7.89/1.49  --splitting_cvd                         false
% 7.89/1.49  --splitting_cvd_svl                     false
% 7.89/1.49  --splitting_nvd                         32
% 7.89/1.49  --sub_typing                            true
% 7.89/1.49  --prep_gs_sim                           true
% 7.89/1.49  --prep_unflatten                        true
% 7.89/1.49  --prep_res_sim                          true
% 7.89/1.49  --prep_upred                            true
% 7.89/1.49  --prep_sem_filter                       exhaustive
% 7.89/1.49  --prep_sem_filter_out                   false
% 7.89/1.49  --pred_elim                             true
% 7.89/1.49  --res_sim_input                         true
% 7.89/1.49  --eq_ax_congr_red                       true
% 7.89/1.49  --pure_diseq_elim                       true
% 7.89/1.49  --brand_transform                       false
% 7.89/1.49  --non_eq_to_eq                          false
% 7.89/1.49  --prep_def_merge                        true
% 7.89/1.49  --prep_def_merge_prop_impl              false
% 7.89/1.49  --prep_def_merge_mbd                    true
% 7.89/1.49  --prep_def_merge_tr_red                 false
% 7.89/1.49  --prep_def_merge_tr_cl                  false
% 7.89/1.49  --smt_preprocessing                     true
% 7.89/1.49  --smt_ac_axioms                         fast
% 7.89/1.49  --preprocessed_out                      false
% 7.89/1.49  --preprocessed_stats                    false
% 7.89/1.49  
% 7.89/1.49  ------ Abstraction refinement Options
% 7.89/1.49  
% 7.89/1.49  --abstr_ref                             []
% 7.89/1.49  --abstr_ref_prep                        false
% 7.89/1.49  --abstr_ref_until_sat                   false
% 7.89/1.49  --abstr_ref_sig_restrict                funpre
% 7.89/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.49  --abstr_ref_under                       []
% 7.89/1.49  
% 7.89/1.49  ------ SAT Options
% 7.89/1.49  
% 7.89/1.49  --sat_mode                              false
% 7.89/1.49  --sat_fm_restart_options                ""
% 7.89/1.49  --sat_gr_def                            false
% 7.89/1.49  --sat_epr_types                         true
% 7.89/1.49  --sat_non_cyclic_types                  false
% 7.89/1.49  --sat_finite_models                     false
% 7.89/1.49  --sat_fm_lemmas                         false
% 7.89/1.49  --sat_fm_prep                           false
% 7.89/1.49  --sat_fm_uc_incr                        true
% 7.89/1.49  --sat_out_model                         small
% 7.89/1.49  --sat_out_clauses                       false
% 7.89/1.49  
% 7.89/1.49  ------ QBF Options
% 7.89/1.49  
% 7.89/1.49  --qbf_mode                              false
% 7.89/1.49  --qbf_elim_univ                         false
% 7.89/1.49  --qbf_dom_inst                          none
% 7.89/1.49  --qbf_dom_pre_inst                      false
% 7.89/1.49  --qbf_sk_in                             false
% 7.89/1.49  --qbf_pred_elim                         true
% 7.89/1.49  --qbf_split                             512
% 7.89/1.49  
% 7.89/1.49  ------ BMC1 Options
% 7.89/1.49  
% 7.89/1.49  --bmc1_incremental                      false
% 7.89/1.49  --bmc1_axioms                           reachable_all
% 7.89/1.49  --bmc1_min_bound                        0
% 7.89/1.49  --bmc1_max_bound                        -1
% 7.89/1.49  --bmc1_max_bound_default                -1
% 7.89/1.49  --bmc1_symbol_reachability              true
% 7.89/1.49  --bmc1_property_lemmas                  false
% 7.89/1.49  --bmc1_k_induction                      false
% 7.89/1.49  --bmc1_non_equiv_states                 false
% 7.89/1.49  --bmc1_deadlock                         false
% 7.89/1.49  --bmc1_ucm                              false
% 7.89/1.49  --bmc1_add_unsat_core                   none
% 7.89/1.49  --bmc1_unsat_core_children              false
% 7.89/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.89/1.49  --bmc1_out_stat                         full
% 7.89/1.49  --bmc1_ground_init                      false
% 7.89/1.49  --bmc1_pre_inst_next_state              false
% 7.89/1.49  --bmc1_pre_inst_state                   false
% 7.89/1.49  --bmc1_pre_inst_reach_state             false
% 7.89/1.49  --bmc1_out_unsat_core                   false
% 7.89/1.49  --bmc1_aig_witness_out                  false
% 7.89/1.49  --bmc1_verbose                          false
% 7.89/1.49  --bmc1_dump_clauses_tptp                false
% 7.89/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.89/1.49  --bmc1_dump_file                        -
% 7.89/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.89/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.89/1.49  --bmc1_ucm_extend_mode                  1
% 7.89/1.49  --bmc1_ucm_init_mode                    2
% 7.89/1.49  --bmc1_ucm_cone_mode                    none
% 7.89/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.89/1.49  --bmc1_ucm_relax_model                  4
% 7.89/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.89/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.89/1.49  --bmc1_ucm_layered_model                none
% 7.89/1.49  --bmc1_ucm_max_lemma_size               10
% 7.89/1.49  
% 7.89/1.49  ------ AIG Options
% 7.89/1.49  
% 7.89/1.49  --aig_mode                              false
% 7.89/1.49  
% 7.89/1.49  ------ Instantiation Options
% 7.89/1.49  
% 7.89/1.49  --instantiation_flag                    true
% 7.89/1.49  --inst_sos_flag                         false
% 7.89/1.49  --inst_sos_phase                        true
% 7.89/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.89/1.49  --inst_lit_sel_side                     none
% 7.89/1.49  --inst_solver_per_active                1400
% 7.89/1.49  --inst_solver_calls_frac                1.
% 7.89/1.49  --inst_passive_queue_type               priority_queues
% 7.89/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.89/1.49  --inst_passive_queues_freq              [25;2]
% 7.89/1.49  --inst_dismatching                      true
% 7.89/1.49  --inst_eager_unprocessed_to_passive     true
% 7.89/1.49  --inst_prop_sim_given                   true
% 7.89/1.49  --inst_prop_sim_new                     false
% 7.89/1.49  --inst_subs_new                         false
% 7.89/1.49  --inst_eq_res_simp                      false
% 7.89/1.49  --inst_subs_given                       false
% 7.89/1.49  --inst_orphan_elimination               true
% 7.89/1.49  --inst_learning_loop_flag               true
% 7.89/1.49  --inst_learning_start                   3000
% 7.89/1.49  --inst_learning_factor                  2
% 7.89/1.49  --inst_start_prop_sim_after_learn       3
% 7.89/1.49  --inst_sel_renew                        solver
% 7.89/1.49  --inst_lit_activity_flag                true
% 7.89/1.49  --inst_restr_to_given                   false
% 7.89/1.49  --inst_activity_threshold               500
% 7.89/1.49  --inst_out_proof                        true
% 7.89/1.49  
% 7.89/1.49  ------ Resolution Options
% 7.89/1.49  
% 7.89/1.49  --resolution_flag                       false
% 7.89/1.49  --res_lit_sel                           adaptive
% 7.89/1.49  --res_lit_sel_side                      none
% 7.89/1.49  --res_ordering                          kbo
% 7.89/1.49  --res_to_prop_solver                    active
% 7.89/1.49  --res_prop_simpl_new                    false
% 7.89/1.49  --res_prop_simpl_given                  true
% 7.89/1.49  --res_passive_queue_type                priority_queues
% 7.89/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.89/1.49  --res_passive_queues_freq               [15;5]
% 7.89/1.49  --res_forward_subs                      full
% 7.89/1.49  --res_backward_subs                     full
% 7.89/1.49  --res_forward_subs_resolution           true
% 7.89/1.49  --res_backward_subs_resolution          true
% 7.89/1.49  --res_orphan_elimination                true
% 7.89/1.49  --res_time_limit                        2.
% 7.89/1.49  --res_out_proof                         true
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Options
% 7.89/1.49  
% 7.89/1.49  --superposition_flag                    true
% 7.89/1.49  --sup_passive_queue_type                priority_queues
% 7.89/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.89/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.89/1.49  --demod_completeness_check              fast
% 7.89/1.49  --demod_use_ground                      true
% 7.89/1.49  --sup_to_prop_solver                    passive
% 7.89/1.49  --sup_prop_simpl_new                    true
% 7.89/1.49  --sup_prop_simpl_given                  true
% 7.89/1.49  --sup_fun_splitting                     false
% 7.89/1.49  --sup_smt_interval                      50000
% 7.89/1.49  
% 7.89/1.49  ------ Superposition Simplification Setup
% 7.89/1.49  
% 7.89/1.49  --sup_indices_passive                   []
% 7.89/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.89/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.49  --sup_full_bw                           [BwDemod]
% 7.89/1.49  --sup_immed_triv                        [TrivRules]
% 7.89/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.49  --sup_immed_bw_main                     []
% 7.89/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.89/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.89/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.89/1.49  
% 7.89/1.49  ------ Combination Options
% 7.89/1.49  
% 7.89/1.49  --comb_res_mult                         3
% 7.89/1.49  --comb_sup_mult                         2
% 7.89/1.49  --comb_inst_mult                        10
% 7.89/1.49  
% 7.89/1.49  ------ Debug Options
% 7.89/1.49  
% 7.89/1.49  --dbg_backtrace                         false
% 7.89/1.49  --dbg_dump_prop_clauses                 false
% 7.89/1.49  --dbg_dump_prop_clauses_file            -
% 7.89/1.49  --dbg_out_stat                          false
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  ------ Proving...
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  % SZS status Theorem for theBenchmark.p
% 7.89/1.49  
% 7.89/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.89/1.49  
% 7.89/1.49  fof(f1,axiom,(
% 7.89/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f17,plain,(
% 7.89/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.89/1.49    inference(ennf_transformation,[],[f1])).
% 7.89/1.49  
% 7.89/1.49  fof(f32,plain,(
% 7.89/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.89/1.49    inference(nnf_transformation,[],[f17])).
% 7.89/1.49  
% 7.89/1.49  fof(f33,plain,(
% 7.89/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.89/1.49    inference(rectify,[],[f32])).
% 7.89/1.49  
% 7.89/1.49  fof(f34,plain,(
% 7.89/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.89/1.49    introduced(choice_axiom,[])).
% 7.89/1.49  
% 7.89/1.49  fof(f35,plain,(
% 7.89/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.89/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 7.89/1.49  
% 7.89/1.49  fof(f39,plain,(
% 7.89/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f35])).
% 7.89/1.49  
% 7.89/1.49  fof(f13,axiom,(
% 7.89/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f27,plain,(
% 7.89/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.89/1.49    inference(ennf_transformation,[],[f13])).
% 7.89/1.49  
% 7.89/1.49  fof(f28,plain,(
% 7.89/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 7.89/1.49    inference(flattening,[],[f27])).
% 7.89/1.49  
% 7.89/1.49  fof(f53,plain,(
% 7.89/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f28])).
% 7.89/1.49  
% 7.89/1.49  fof(f15,conjecture,(
% 7.89/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f16,negated_conjecture,(
% 7.89/1.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 7.89/1.49    inference(negated_conjecture,[],[f15])).
% 7.89/1.49  
% 7.89/1.49  fof(f30,plain,(
% 7.89/1.49    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 7.89/1.49    inference(ennf_transformation,[],[f16])).
% 7.89/1.49  
% 7.89/1.49  fof(f31,plain,(
% 7.89/1.49    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 7.89/1.49    inference(flattening,[],[f30])).
% 7.89/1.49  
% 7.89/1.49  fof(f36,plain,(
% 7.89/1.49    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3))),
% 7.89/1.49    introduced(choice_axiom,[])).
% 7.89/1.49  
% 7.89/1.49  fof(f37,plain,(
% 7.89/1.49    k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3)),
% 7.89/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f36])).
% 7.89/1.49  
% 7.89/1.49  fof(f56,plain,(
% 7.89/1.49    r1_tarski(sK1,sK2)),
% 7.89/1.49    inference(cnf_transformation,[],[f37])).
% 7.89/1.49  
% 7.89/1.49  fof(f38,plain,(
% 7.89/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f35])).
% 7.89/1.49  
% 7.89/1.49  fof(f40,plain,(
% 7.89/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f35])).
% 7.89/1.49  
% 7.89/1.49  fof(f55,plain,(
% 7.89/1.49    v1_relat_1(sK3)),
% 7.89/1.49    inference(cnf_transformation,[],[f37])).
% 7.89/1.49  
% 7.89/1.49  fof(f11,axiom,(
% 7.89/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f25,plain,(
% 7.89/1.49    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 7.89/1.49    inference(ennf_transformation,[],[f11])).
% 7.89/1.49  
% 7.89/1.49  fof(f50,plain,(
% 7.89/1.49    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f25])).
% 7.89/1.49  
% 7.89/1.49  fof(f8,axiom,(
% 7.89/1.49    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f20,plain,(
% 7.89/1.49    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.89/1.49    inference(ennf_transformation,[],[f8])).
% 7.89/1.49  
% 7.89/1.49  fof(f47,plain,(
% 7.89/1.49    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f20])).
% 7.89/1.49  
% 7.89/1.49  fof(f7,axiom,(
% 7.89/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f46,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.89/1.49    inference(cnf_transformation,[],[f7])).
% 7.89/1.49  
% 7.89/1.49  fof(f5,axiom,(
% 7.89/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f44,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f5])).
% 7.89/1.49  
% 7.89/1.49  fof(f6,axiom,(
% 7.89/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f45,plain,(
% 7.89/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f6])).
% 7.89/1.49  
% 7.89/1.49  fof(f58,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f44,f45])).
% 7.89/1.49  
% 7.89/1.49  fof(f59,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 7.89/1.49    inference(definition_unfolding,[],[f46,f58])).
% 7.89/1.49  
% 7.89/1.49  fof(f62,plain,(
% 7.89/1.49    ( ! [X0] : (k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f47,f59])).
% 7.89/1.49  
% 7.89/1.49  fof(f3,axiom,(
% 7.89/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f42,plain,(
% 7.89/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.89/1.49    inference(cnf_transformation,[],[f3])).
% 7.89/1.49  
% 7.89/1.49  fof(f60,plain,(
% 7.89/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 7.89/1.49    inference(definition_unfolding,[],[f42,f59])).
% 7.89/1.49  
% 7.89/1.49  fof(f2,axiom,(
% 7.89/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f18,plain,(
% 7.89/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.89/1.49    inference(ennf_transformation,[],[f2])).
% 7.89/1.49  
% 7.89/1.49  fof(f19,plain,(
% 7.89/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.89/1.49    inference(flattening,[],[f18])).
% 7.89/1.49  
% 7.89/1.49  fof(f41,plain,(
% 7.89/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f19])).
% 7.89/1.49  
% 7.89/1.49  fof(f10,axiom,(
% 7.89/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f23,plain,(
% 7.89/1.49    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.89/1.49    inference(ennf_transformation,[],[f10])).
% 7.89/1.49  
% 7.89/1.49  fof(f24,plain,(
% 7.89/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.89/1.49    inference(flattening,[],[f23])).
% 7.89/1.49  
% 7.89/1.49  fof(f49,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f24])).
% 7.89/1.49  
% 7.89/1.49  fof(f12,axiom,(
% 7.89/1.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f26,plain,(
% 7.89/1.49    ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 7.89/1.49    inference(ennf_transformation,[],[f12])).
% 7.89/1.49  
% 7.89/1.49  fof(f51,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f26])).
% 7.89/1.49  
% 7.89/1.49  fof(f4,axiom,(
% 7.89/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f43,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f4])).
% 7.89/1.49  
% 7.89/1.49  fof(f61,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 7.89/1.49    inference(definition_unfolding,[],[f43,f58,f58])).
% 7.89/1.49  
% 7.89/1.49  fof(f9,axiom,(
% 7.89/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f21,plain,(
% 7.89/1.49    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.89/1.49    inference(ennf_transformation,[],[f9])).
% 7.89/1.49  
% 7.89/1.49  fof(f22,plain,(
% 7.89/1.49    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.89/1.49    inference(flattening,[],[f21])).
% 7.89/1.49  
% 7.89/1.49  fof(f48,plain,(
% 7.89/1.49    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f22])).
% 7.89/1.49  
% 7.89/1.49  fof(f14,axiom,(
% 7.89/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 7.89/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.49  
% 7.89/1.49  fof(f29,plain,(
% 7.89/1.49    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 7.89/1.49    inference(ennf_transformation,[],[f14])).
% 7.89/1.49  
% 7.89/1.49  fof(f54,plain,(
% 7.89/1.49    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 7.89/1.49    inference(cnf_transformation,[],[f29])).
% 7.89/1.49  
% 7.89/1.49  fof(f57,plain,(
% 7.89/1.49    k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1)),
% 7.89/1.49    inference(cnf_transformation,[],[f37])).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1,plain,
% 7.89/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_192,plain,
% 7.89/1.49      ( r2_hidden(sK0(X0_44,X1_44),X0_44) | r1_tarski(X0_44,X1_44) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_502,plain,
% 7.89/1.49      ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
% 7.89/1.49      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_11,plain,
% 7.89/1.49      ( r2_hidden(X0,X1)
% 7.89/1.49      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
% 7.89/1.49      | ~ v1_relat_1(X2) ),
% 7.89/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_182,plain,
% 7.89/1.49      ( r2_hidden(X0_45,X0_44)
% 7.89/1.49      | ~ r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44)))
% 7.89/1.49      | ~ v1_relat_1(X0_43) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_511,plain,
% 7.89/1.49      ( r2_hidden(X0_45,X0_44) = iProver_top
% 7.89/1.49      | r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44))) != iProver_top
% 7.89/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_182]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1682,plain,
% 7.89/1.49      ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44),X0_44) = iProver_top
% 7.89/1.49      | r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44) = iProver_top
% 7.89/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_502,c_511]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_15,negated_conjecture,
% 7.89/1.49      ( r1_tarski(sK1,sK2) ),
% 7.89/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_178,negated_conjecture,
% 7.89/1.49      ( r1_tarski(sK1,sK2) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_514,plain,
% 7.89/1.49      ( r1_tarski(sK1,sK2) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_178]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2,plain,
% 7.89/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.89/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_191,plain,
% 7.89/1.49      ( ~ r2_hidden(X0_45,X0_44)
% 7.89/1.49      | r2_hidden(X0_45,X1_44)
% 7.89/1.49      | ~ r1_tarski(X0_44,X1_44) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_503,plain,
% 7.89/1.49      ( r2_hidden(X0_45,X0_44) != iProver_top
% 7.89/1.49      | r2_hidden(X0_45,X1_44) = iProver_top
% 7.89/1.49      | r1_tarski(X0_44,X1_44) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_779,plain,
% 7.89/1.49      ( r2_hidden(X0_45,sK2) = iProver_top
% 7.89/1.49      | r2_hidden(X0_45,sK1) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_514,c_503]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_18320,plain,
% 7.89/1.49      ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44),sK2) = iProver_top
% 7.89/1.49      | r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44) = iProver_top
% 7.89/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1682,c_779]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_0,plain,
% 7.89/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_193,plain,
% 7.89/1.49      ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44) | r1_tarski(X0_44,X1_44) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_501,plain,
% 7.89/1.49      ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
% 7.89/1.49      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20194,plain,
% 7.89/1.49      ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),sK2) = iProver_top
% 7.89/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_18320,c_501]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_16,negated_conjecture,
% 7.89/1.49      ( v1_relat_1(sK3) ),
% 7.89/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_177,negated_conjecture,
% 7.89/1.49      ( v1_relat_1(sK3) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_515,plain,
% 7.89/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_177]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_9,plain,
% 7.89/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 7.89/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_184,plain,
% 7.89/1.49      ( ~ v1_relat_1(X0_43) | v1_relat_1(k2_wellord1(X0_43,X0_44)) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_509,plain,
% 7.89/1.49      ( v1_relat_1(X0_43) != iProver_top
% 7.89/1.49      | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6,plain,
% 7.89/1.49      ( ~ v1_relat_1(X0)
% 7.89/1.49      | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_187,plain,
% 7.89/1.49      ( ~ v1_relat_1(X0_43)
% 7.89/1.49      | k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_506,plain,
% 7.89/1.49      ( k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
% 7.89/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1368,plain,
% 7.89/1.49      ( k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k2_relat_1(k2_wellord1(X0_43,X0_44)))) = k3_relat_1(k2_wellord1(X0_43,X0_44))
% 7.89/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_509,c_506]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10893,plain,
% 7.89/1.49      ( k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k2_relat_1(k2_wellord1(sK3,X0_44)))) = k3_relat_1(k2_wellord1(sK3,X0_44)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_515,c_1368]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4,plain,
% 7.89/1.49      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 7.89/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_189,plain,
% 7.89/1.49      ( r1_tarski(X0_44,k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X1_44))) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_505,plain,
% 7.89/1.49      ( r1_tarski(X0_44,k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X1_44))) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3,plain,
% 7.89/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.89/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_190,plain,
% 7.89/1.49      ( ~ r1_tarski(X0_44,X1_44)
% 7.89/1.49      | ~ r1_tarski(X1_44,X2_44)
% 7.89/1.49      | r1_tarski(X0_44,X2_44) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_504,plain,
% 7.89/1.49      ( r1_tarski(X0_44,X1_44) != iProver_top
% 7.89/1.49      | r1_tarski(X1_44,X2_44) != iProver_top
% 7.89/1.49      | r1_tarski(X0_44,X2_44) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_891,plain,
% 7.89/1.49      ( r1_tarski(X0_44,X1_44) = iProver_top
% 7.89/1.49      | r1_tarski(k3_tarski(k2_enumset1(X0_44,X0_44,X0_44,X2_44)),X1_44) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_505,c_504]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_12210,plain,
% 7.89/1.49      ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
% 7.89/1.49      | r1_tarski(k1_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_10893,c_891]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_22494,plain,
% 7.89/1.49      ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
% 7.89/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_20194,c_12210]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_17,plain,
% 7.89/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_30177,plain,
% 7.89/1.49      ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_22494,c_17]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8,plain,
% 7.89/1.49      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.89/1.49      | ~ v1_relat_1(X0)
% 7.89/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.89/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_185,plain,
% 7.89/1.49      ( ~ r1_tarski(k1_relat_1(X0_43),X0_44)
% 7.89/1.49      | ~ v1_relat_1(X0_43)
% 7.89/1.49      | k7_relat_1(X0_43,X0_44) = X0_43 ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_508,plain,
% 7.89/1.49      ( k7_relat_1(X0_43,X0_44) = X0_43
% 7.89/1.49      | r1_tarski(k1_relat_1(X0_43),X0_44) != iProver_top
% 7.89/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_30182,plain,
% 7.89/1.49      ( k7_relat_1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1)
% 7.89/1.49      | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_30177,c_508]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_238,plain,
% 7.89/1.49      ( v1_relat_1(X0_43) != iProver_top
% 7.89/1.49      | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_240,plain,
% 7.89/1.49      ( v1_relat_1(k2_wellord1(sK3,sK1)) = iProver_top
% 7.89/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_238]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_33522,plain,
% 7.89/1.49      ( k7_relat_1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1) ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_30182,c_17,c_240]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_10,plain,
% 7.89/1.49      ( ~ v1_relat_1(X0)
% 7.89/1.49      | k8_relat_1(X1,k7_relat_1(X0,X1)) = k2_wellord1(X0,X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_183,plain,
% 7.89/1.49      ( ~ v1_relat_1(X0_43)
% 7.89/1.49      | k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) = k2_wellord1(X0_43,X0_44) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_510,plain,
% 7.89/1.49      ( k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) = k2_wellord1(X0_43,X0_44)
% 7.89/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_717,plain,
% 7.89/1.49      ( k8_relat_1(X0_44,k7_relat_1(k2_wellord1(X0_43,X1_44),X0_44)) = k2_wellord1(k2_wellord1(X0_43,X1_44),X0_44)
% 7.89/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_509,c_510]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2971,plain,
% 7.89/1.49      ( k8_relat_1(X0_44,k7_relat_1(k2_wellord1(sK3,X1_44),X0_44)) = k2_wellord1(k2_wellord1(sK3,X1_44),X0_44) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_515,c_717]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_33525,plain,
% 7.89/1.49      ( k2_wellord1(k2_wellord1(sK3,sK1),sK2) = k8_relat_1(sK2,k2_wellord1(sK3,sK1)) ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_33522,c_2971]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_5,plain,
% 7.89/1.49      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_188,plain,
% 7.89/1.49      ( k2_enumset1(X0_44,X0_44,X0_44,X1_44) = k2_enumset1(X1_44,X1_44,X1_44,X0_44) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_685,plain,
% 7.89/1.49      ( r1_tarski(X0_44,k3_tarski(k2_enumset1(X1_44,X1_44,X1_44,X0_44))) = iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_188,c_505]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_892,plain,
% 7.89/1.49      ( r1_tarski(X0_44,X1_44) = iProver_top
% 7.89/1.49      | r1_tarski(k3_tarski(k2_enumset1(X2_44,X2_44,X2_44,X0_44)),X1_44) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_685,c_504]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_12212,plain,
% 7.89/1.49      ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
% 7.89/1.49      | r1_tarski(k2_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_10893,c_892]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_22493,plain,
% 7.89/1.49      ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
% 7.89/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_20194,c_12212]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_30151,plain,
% 7.89/1.49      ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_22493,c_17]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7,plain,
% 7.89/1.49      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.89/1.50      | ~ v1_relat_1(X0)
% 7.89/1.50      | k8_relat_1(X1,X0) = X0 ),
% 7.89/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_186,plain,
% 7.89/1.50      ( ~ r1_tarski(k2_relat_1(X0_43),X0_44)
% 7.89/1.50      | ~ v1_relat_1(X0_43)
% 7.89/1.50      | k8_relat_1(X0_44,X0_43) = X0_43 ),
% 7.89/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_507,plain,
% 7.89/1.50      ( k8_relat_1(X0_44,X0_43) = X0_43
% 7.89/1.50      | r1_tarski(k2_relat_1(X0_43),X0_44) != iProver_top
% 7.89/1.50      | v1_relat_1(X0_43) != iProver_top ),
% 7.89/1.50      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_30156,plain,
% 7.89/1.50      ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k2_wellord1(sK3,sK1)
% 7.89/1.50      | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
% 7.89/1.50      inference(superposition,[status(thm)],[c_30151,c_507]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_33424,plain,
% 7.89/1.50      ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k2_wellord1(sK3,sK1) ),
% 7.89/1.50      inference(global_propositional_subsumption,
% 7.89/1.50                [status(thm)],
% 7.89/1.50                [c_30156,c_17,c_240]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_33526,plain,
% 7.89/1.50      ( k2_wellord1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1) ),
% 7.89/1.50      inference(light_normalisation,[status(thm)],[c_33525,c_33424]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_199,plain,
% 7.89/1.50      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 7.89/1.50      theory(equality) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_697,plain,
% 7.89/1.50      ( X0_43 != X1_43
% 7.89/1.50      | k2_wellord1(sK3,sK1) != X1_43
% 7.89/1.50      | k2_wellord1(sK3,sK1) = X0_43 ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_199]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_743,plain,
% 7.89/1.50      ( X0_43 != k2_wellord1(sK3,sK1)
% 7.89/1.50      | k2_wellord1(sK3,sK1) = X0_43
% 7.89/1.50      | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_697]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_828,plain,
% 7.89/1.50      ( k2_wellord1(X0_43,X0_44) != k2_wellord1(sK3,sK1)
% 7.89/1.50      | k2_wellord1(sK3,sK1) = k2_wellord1(X0_43,X0_44)
% 7.89/1.50      | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_743]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_996,plain,
% 7.89/1.50      ( k2_wellord1(k2_wellord1(sK3,sK1),sK2) != k2_wellord1(sK3,sK1)
% 7.89/1.50      | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK1),sK2)
% 7.89/1.50      | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_828]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_13,plain,
% 7.89/1.50      ( ~ v1_relat_1(X0)
% 7.89/1.50      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 7.89/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_180,plain,
% 7.89/1.50      ( ~ v1_relat_1(X0_43)
% 7.89/1.50      | k2_wellord1(k2_wellord1(X0_43,X0_44),X1_44) = k2_wellord1(k2_wellord1(X0_43,X1_44),X0_44) ),
% 7.89/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_749,plain,
% 7.89/1.50      ( ~ v1_relat_1(sK3)
% 7.89/1.50      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_180]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_672,plain,
% 7.89/1.50      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X0_43
% 7.89/1.50      | k2_wellord1(sK3,sK1) != X0_43
% 7.89/1.50      | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_199]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_698,plain,
% 7.89/1.50      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(X0_43,X0_44)
% 7.89/1.50      | k2_wellord1(sK3,sK1) != k2_wellord1(X0_43,X0_44)
% 7.89/1.50      | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_672]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_748,plain,
% 7.89/1.50      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
% 7.89/1.50      | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1)
% 7.89/1.50      | k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_698]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_14,negated_conjecture,
% 7.89/1.50      ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 7.89/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_179,negated_conjecture,
% 7.89/1.50      ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 7.89/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_196,plain,( X0_44 = X0_44 ),theory(equality) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_220,plain,
% 7.89/1.50      ( sK1 = sK1 ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_196]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_195,plain,( X0_43 = X0_43 ),theory(equality) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_219,plain,
% 7.89/1.50      ( sK3 = sK3 ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_195]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_209,plain,
% 7.89/1.50      ( X0_44 != X1_44
% 7.89/1.50      | X0_43 != X1_43
% 7.89/1.50      | k2_wellord1(X0_43,X0_44) = k2_wellord1(X1_43,X1_44) ),
% 7.89/1.50      theory(equality) ).
% 7.89/1.50  
% 7.89/1.50  cnf(c_217,plain,
% 7.89/1.50      ( sK1 != sK1
% 7.89/1.50      | k2_wellord1(sK3,sK1) = k2_wellord1(sK3,sK1)
% 7.89/1.50      | sK3 != sK3 ),
% 7.89/1.50      inference(instantiation,[status(thm)],[c_209]) ).
% 7.89/1.50  
% 7.89/1.50  cnf(contradiction,plain,
% 7.89/1.50      ( $false ),
% 7.89/1.50      inference(minisat,
% 7.89/1.50                [status(thm)],
% 7.89/1.50                [c_33526,c_996,c_749,c_748,c_179,c_220,c_219,c_217,c_16]) ).
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.89/1.50  
% 7.89/1.50  ------                               Statistics
% 7.89/1.50  
% 7.89/1.50  ------ General
% 7.89/1.50  
% 7.89/1.50  abstr_ref_over_cycles:                  0
% 7.89/1.50  abstr_ref_under_cycles:                 0
% 7.89/1.50  gc_basic_clause_elim:                   0
% 7.89/1.50  forced_gc_time:                         0
% 7.89/1.50  parsing_time:                           0.012
% 7.89/1.50  unif_index_cands_time:                  0.
% 7.89/1.50  unif_index_add_time:                    0.
% 7.89/1.50  orderings_time:                         0.
% 7.89/1.50  out_proof_time:                         0.012
% 7.89/1.50  total_time:                             0.913
% 7.89/1.50  num_of_symbols:                         47
% 7.89/1.50  num_of_terms:                           27505
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing
% 7.89/1.50  
% 7.89/1.50  num_of_splits:                          0
% 7.89/1.50  num_of_split_atoms:                     0
% 7.89/1.50  num_of_reused_defs:                     0
% 7.89/1.50  num_eq_ax_congr_red:                    14
% 7.89/1.50  num_of_sem_filtered_clauses:            1
% 7.89/1.50  num_of_subtypes:                        4
% 7.89/1.50  monotx_restored_types:                  0
% 7.89/1.50  sat_num_of_epr_types:                   0
% 7.89/1.50  sat_num_of_non_cyclic_types:            0
% 7.89/1.50  sat_guarded_non_collapsed_types:        1
% 7.89/1.50  num_pure_diseq_elim:                    0
% 7.89/1.50  simp_replaced_by:                       0
% 7.89/1.50  res_preprocessed:                       82
% 7.89/1.50  prep_upred:                             0
% 7.89/1.50  prep_unflattend:                        0
% 7.89/1.50  smt_new_axioms:                         0
% 7.89/1.50  pred_elim_cands:                        3
% 7.89/1.50  pred_elim:                              0
% 7.89/1.50  pred_elim_cl:                           0
% 7.89/1.50  pred_elim_cycles:                       1
% 7.89/1.50  merged_defs:                            0
% 7.89/1.50  merged_defs_ncl:                        0
% 7.89/1.50  bin_hyper_res:                          0
% 7.89/1.50  prep_cycles:                            3
% 7.89/1.50  pred_elim_time:                         0.
% 7.89/1.50  splitting_time:                         0.
% 7.89/1.50  sem_filter_time:                        0.
% 7.89/1.50  monotx_time:                            0.
% 7.89/1.50  subtype_inf_time:                       0.
% 7.89/1.50  
% 7.89/1.50  ------ Problem properties
% 7.89/1.50  
% 7.89/1.50  clauses:                                17
% 7.89/1.50  conjectures:                            3
% 7.89/1.50  epr:                                    4
% 7.89/1.50  horn:                                   16
% 7.89/1.50  ground:                                 3
% 7.89/1.50  unary:                                  5
% 7.89/1.50  binary:                                 6
% 7.89/1.50  lits:                                   35
% 7.89/1.50  lits_eq:                                7
% 7.89/1.50  fd_pure:                                0
% 7.89/1.50  fd_pseudo:                              0
% 7.89/1.50  fd_cond:                                0
% 7.89/1.50  fd_pseudo_cond:                         0
% 7.89/1.50  ac_symbols:                             0
% 7.89/1.50  
% 7.89/1.50  ------ Propositional Solver
% 7.89/1.50  
% 7.89/1.50  prop_solver_calls:                      29
% 7.89/1.50  prop_fast_solver_calls:                 814
% 7.89/1.50  smt_solver_calls:                       0
% 7.89/1.50  smt_fast_solver_calls:                  0
% 7.89/1.50  prop_num_of_clauses:                    8840
% 7.89/1.50  prop_preprocess_simplified:             15941
% 7.89/1.50  prop_fo_subsumed:                       24
% 7.89/1.50  prop_solver_time:                       0.
% 7.89/1.50  smt_solver_time:                        0.
% 7.89/1.50  smt_fast_solver_time:                   0.
% 7.89/1.50  prop_fast_solver_time:                  0.
% 7.89/1.50  prop_unsat_core_time:                   0.001
% 7.89/1.50  
% 7.89/1.50  ------ QBF
% 7.89/1.50  
% 7.89/1.50  qbf_q_res:                              0
% 7.89/1.50  qbf_num_tautologies:                    0
% 7.89/1.50  qbf_prep_cycles:                        0
% 7.89/1.50  
% 7.89/1.50  ------ BMC1
% 7.89/1.50  
% 7.89/1.50  bmc1_current_bound:                     -1
% 7.89/1.50  bmc1_last_solved_bound:                 -1
% 7.89/1.50  bmc1_unsat_core_size:                   -1
% 7.89/1.50  bmc1_unsat_core_parents_size:           -1
% 7.89/1.50  bmc1_merge_next_fun:                    0
% 7.89/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.89/1.50  
% 7.89/1.50  ------ Instantiation
% 7.89/1.50  
% 7.89/1.50  inst_num_of_clauses:                    2619
% 7.89/1.50  inst_num_in_passive:                    1511
% 7.89/1.50  inst_num_in_active:                     1033
% 7.89/1.50  inst_num_in_unprocessed:                75
% 7.89/1.50  inst_num_of_loops:                      1220
% 7.89/1.50  inst_num_of_learning_restarts:          0
% 7.89/1.50  inst_num_moves_active_passive:          182
% 7.89/1.50  inst_lit_activity:                      0
% 7.89/1.50  inst_lit_activity_moves:                0
% 7.89/1.50  inst_num_tautologies:                   0
% 7.89/1.50  inst_num_prop_implied:                  0
% 7.89/1.50  inst_num_existing_simplified:           0
% 7.89/1.50  inst_num_eq_res_simplified:             0
% 7.89/1.50  inst_num_child_elim:                    0
% 7.89/1.50  inst_num_of_dismatching_blockings:      4041
% 7.89/1.50  inst_num_of_non_proper_insts:           4148
% 7.89/1.50  inst_num_of_duplicates:                 0
% 7.89/1.50  inst_inst_num_from_inst_to_res:         0
% 7.89/1.50  inst_dismatching_checking_time:         0.
% 7.89/1.50  
% 7.89/1.50  ------ Resolution
% 7.89/1.50  
% 7.89/1.50  res_num_of_clauses:                     0
% 7.89/1.50  res_num_in_passive:                     0
% 7.89/1.50  res_num_in_active:                      0
% 7.89/1.50  res_num_of_loops:                       85
% 7.89/1.50  res_forward_subset_subsumed:            391
% 7.89/1.50  res_backward_subset_subsumed:           0
% 7.89/1.50  res_forward_subsumed:                   0
% 7.89/1.50  res_backward_subsumed:                  0
% 7.89/1.50  res_forward_subsumption_resolution:     0
% 7.89/1.50  res_backward_subsumption_resolution:    0
% 7.89/1.50  res_clause_to_clause_subsumption:       8171
% 7.89/1.50  res_orphan_elimination:                 0
% 7.89/1.50  res_tautology_del:                      617
% 7.89/1.50  res_num_eq_res_simplified:              0
% 7.89/1.50  res_num_sel_changes:                    0
% 7.89/1.50  res_moves_from_active_to_pass:          0
% 7.89/1.50  
% 7.89/1.50  ------ Superposition
% 7.89/1.50  
% 7.89/1.50  sup_time_total:                         0.
% 7.89/1.50  sup_time_generating:                    0.
% 7.89/1.50  sup_time_sim_full:                      0.
% 7.89/1.50  sup_time_sim_immed:                     0.
% 7.89/1.50  
% 7.89/1.50  sup_num_of_clauses:                     1492
% 7.89/1.50  sup_num_in_active:                      236
% 7.89/1.50  sup_num_in_passive:                     1256
% 7.89/1.50  sup_num_of_loops:                       242
% 7.89/1.50  sup_fw_superposition:                   2727
% 7.89/1.50  sup_bw_superposition:                   1753
% 7.89/1.50  sup_immediate_simplified:               1044
% 7.89/1.50  sup_given_eliminated:                   1
% 7.89/1.50  comparisons_done:                       0
% 7.89/1.50  comparisons_avoided:                    0
% 7.89/1.50  
% 7.89/1.50  ------ Simplifications
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  sim_fw_subset_subsumed:                 8
% 7.89/1.50  sim_bw_subset_subsumed:                 32
% 7.89/1.50  sim_fw_subsumed:                        239
% 7.89/1.50  sim_bw_subsumed:                        17
% 7.89/1.50  sim_fw_subsumption_res:                 0
% 7.89/1.50  sim_bw_subsumption_res:                 0
% 7.89/1.50  sim_tautology_del:                      79
% 7.89/1.50  sim_eq_tautology_del:                   77
% 7.89/1.50  sim_eq_res_simp:                        0
% 7.89/1.50  sim_fw_demodulated:                     350
% 7.89/1.50  sim_bw_demodulated:                     11
% 7.89/1.50  sim_light_normalised:                   668
% 7.89/1.50  sim_joinable_taut:                      0
% 7.89/1.50  sim_joinable_simp:                      0
% 7.89/1.50  sim_ac_normalised:                      0
% 7.89/1.50  sim_smt_subsumption:                    0
% 7.89/1.50  
%------------------------------------------------------------------------------
