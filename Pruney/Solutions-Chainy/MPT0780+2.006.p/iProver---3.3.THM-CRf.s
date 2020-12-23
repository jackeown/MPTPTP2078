%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:22 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 391 expanded)
%              Number of clauses        :  103 ( 155 expanded)
%              Number of leaves         :   23 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  381 ( 923 expanded)
%              Number of equality atoms :  224 ( 410 expanded)
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

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1)
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f39])).

fof(f61,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f69,plain,(
    ! [X0] :
      ( k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f46,f65,f65])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f40])).

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

cnf(c_29001,plain,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1)
    | k2_wellord1(sK3,sK1) = k7_relat_1(k2_wellord1(sK3,sK1),sK2)
    | k7_relat_1(k2_wellord1(sK3,sK1),sK2) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_1373,plain,
    ( X0_43 != X1_43
    | X0_43 = k8_relat_1(X0_44,X2_43)
    | k8_relat_1(X0_44,X2_43) != X1_43 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_3617,plain,
    ( X0_43 != k8_relat_1(X0_44,X1_43)
    | X0_43 = k8_relat_1(X0_44,X2_43)
    | k8_relat_1(X0_44,X2_43) != k8_relat_1(X0_44,X1_43) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_6822,plain,
    ( k8_relat_1(X0_44,X0_43) != k8_relat_1(X0_44,X0_43)
    | k8_relat_1(X0_44,X1_43) != k8_relat_1(X0_44,X0_43)
    | k8_relat_1(X0_44,X0_43) = k8_relat_1(X0_44,X1_43) ),
    inference(instantiation,[status(thm)],[c_3617])).

cnf(c_27230,plain,
    ( k8_relat_1(sK2,k2_wellord1(X0_43,X0_44)) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2))
    | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2)) = k8_relat_1(sK2,k2_wellord1(X0_43,X0_44))
    | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2)) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2)) ),
    inference(instantiation,[status(thm)],[c_6822])).

cnf(c_27231,plain,
    ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2))
    | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) = k8_relat_1(sK2,k2_wellord1(sK3,sK1))
    | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_27230])).

cnf(c_726,plain,
    ( X0_43 != X1_43
    | X0_43 = k8_relat_1(X0_44,k7_relat_1(X2_43,X0_44))
    | k8_relat_1(X0_44,k7_relat_1(X2_43,X0_44)) != X1_43 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_811,plain,
    ( X0_43 != k2_wellord1(X1_43,X0_44)
    | X0_43 = k8_relat_1(X0_44,k7_relat_1(X1_43,X0_44))
    | k8_relat_1(X0_44,k7_relat_1(X1_43,X0_44)) != k2_wellord1(X1_43,X0_44) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1872,plain,
    ( k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) != k2_wellord1(X0_43,X0_44)
    | k8_relat_1(X1_44,k7_relat_1(X1_43,X1_44)) != k2_wellord1(X0_43,X0_44)
    | k8_relat_1(X1_44,k7_relat_1(X1_43,X1_44)) = k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_5992,plain,
    ( k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) != k2_wellord1(X1_43,sK2)
    | k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) = k8_relat_1(sK2,k7_relat_1(X1_43,sK2))
    | k8_relat_1(sK2,k7_relat_1(X1_43,sK2)) != k2_wellord1(X1_43,sK2) ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_26536,plain,
    ( k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
    | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_5992])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

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
    inference(cnf_transformation,[],[f58])).

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

cnf(c_1402,plain,
    ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44),X0_44) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_498])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(cnf_transformation,[],[f41])).

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

cnf(c_802,plain,
    ( r2_hidden(X0_45,sK2) = iProver_top
    | r2_hidden(X0_45,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_501,c_490])).

cnf(c_8458,plain,
    ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44),sK2) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_802])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_194,plain,
    ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_488,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_10580,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),sK2) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_8458,c_488])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_178,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_502,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_178])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

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
    | k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_188,plain,
    ( ~ v1_relat_1(X0_43)
    | k3_tarski(k4_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_493,plain,
    ( k3_tarski(k4_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_1231,plain,
    ( k3_tarski(k4_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k2_relat_1(k2_wellord1(X0_43,X0_44)))) = k3_relat_1(k2_wellord1(X0_43,X0_44))
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_493])).

cnf(c_7161,plain,
    ( k3_tarski(k4_enumset1(k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k2_relat_1(k2_wellord1(sK3,X0_44)))) = k3_relat_1(k2_wellord1(sK3,X0_44)) ),
    inference(superposition,[status(thm)],[c_502,c_1231])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_191,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(k3_tarski(k4_enumset1(X0_44,X0_44,X0_44,X0_44,X0_44,X2_44)),X1_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_491,plain,
    ( r1_tarski(X0_44,X1_44) = iProver_top
    | r1_tarski(k3_tarski(k4_enumset1(X0_44,X0_44,X0_44,X0_44,X0_44,X2_44)),X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_7810,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
    | r1_tarski(k1_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_7161,c_491])).

cnf(c_14801,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10580,c_7810])).

cnf(c_17,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_24151,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14801,c_17])).

cnf(c_8,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

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

cnf(c_24155,plain,
    ( k7_relat_1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1)
    | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24151,c_495])).

cnf(c_5,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_189,plain,
    ( k4_enumset1(X0_44,X0_44,X0_44,X0_44,X0_44,X1_44) = k4_enumset1(X1_44,X1_44,X1_44,X1_44,X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_807,plain,
    ( r1_tarski(X0_44,X1_44) = iProver_top
    | r1_tarski(k3_tarski(k4_enumset1(X2_44,X2_44,X2_44,X2_44,X2_44,X0_44)),X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_189,c_491])).

cnf(c_7813,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_7161,c_807])).

cnf(c_14800,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10580,c_7813])).

cnf(c_23848,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14800,c_17])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

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

cnf(c_23852,plain,
    ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k2_wellord1(sK3,sK1)
    | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23848,c_494])).

cnf(c_538,plain,
    ( X0_43 != k2_wellord1(X1_43,X0_44)
    | k2_wellord1(sK3,sK1) = X0_43
    | k2_wellord1(sK3,sK1) != k2_wellord1(X1_43,X0_44) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_14610,plain,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(X0_43,X0_44)
    | k2_wellord1(sK3,sK1) = k8_relat_1(sK2,k2_wellord1(sK3,sK1))
    | k8_relat_1(sK2,k2_wellord1(sK3,sK1)) != k2_wellord1(X0_43,X0_44) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_14611,plain,
    ( k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1)
    | k2_wellord1(sK3,sK1) = k8_relat_1(sK2,k2_wellord1(sK3,sK1))
    | k8_relat_1(sK2,k2_wellord1(sK3,sK1)) != k2_wellord1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_14610])).

cnf(c_209,plain,
    ( X0_43 != X1_43
    | k8_relat_1(X0_44,X0_43) = k8_relat_1(X0_44,X1_43) ),
    theory(equality)).

cnf(c_819,plain,
    ( X0_43 != k7_relat_1(X1_43,X0_44)
    | k8_relat_1(X0_44,X0_43) = k8_relat_1(X0_44,k7_relat_1(X1_43,X0_44)) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_1434,plain,
    ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),X0_44)
    | k8_relat_1(X0_44,k2_wellord1(sK3,sK1)) = k8_relat_1(X0_44,k7_relat_1(k2_wellord1(sK3,sK1),X0_44)) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_7378,plain,
    ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),sK2)
    | k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_815,plain,
    ( X0_43 != k8_relat_1(X0_44,X1_43)
    | X0_43 = k8_relat_1(X0_44,k7_relat_1(X2_43,X0_44))
    | k8_relat_1(X0_44,k7_relat_1(X2_43,X0_44)) != k8_relat_1(X0_44,X1_43) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1559,plain,
    ( k2_wellord1(sK3,sK1) != k8_relat_1(X0_44,k2_wellord1(sK3,sK1))
    | k2_wellord1(sK3,sK1) = k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44))
    | k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) != k8_relat_1(X0_44,k2_wellord1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_5230,plain,
    ( k2_wellord1(sK3,sK1) != k8_relat_1(sK2,k2_wellord1(sK3,sK1))
    | k2_wellord1(sK3,sK1) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X0_44),sK2))
    | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X0_44),sK2)) != k8_relat_1(sK2,k2_wellord1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_5235,plain,
    ( k2_wellord1(sK3,sK1) != k8_relat_1(sK2,k2_wellord1(sK3,sK1))
    | k2_wellord1(sK3,sK1) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2))
    | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) != k8_relat_1(sK2,k2_wellord1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_5230])).

cnf(c_541,plain,
    ( k2_wellord1(X0_43,X0_44) != X1_43
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X1_43
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(X0_43,X0_44) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_3244,plain,
    ( k2_wellord1(X0_43,X0_44) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2))
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(X0_43,X0_44)
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2)) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_3245,plain,
    ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(sK3,sK1)
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2))
    | k2_wellord1(sK3,sK1) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_3244])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(X1,k7_relat_1(X0,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_184,plain,
    ( ~ v1_relat_1(X0_43)
    | k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) = k2_wellord1(X0_43,X0_44) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1394,plain,
    ( ~ v1_relat_1(k2_wellord1(sK3,sK1))
    | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) = k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
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
    | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2))
    | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) != k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f59])).

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
    inference(cnf_transformation,[],[f62])).

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
    inference(minisat,[status(thm)],[c_29001,c_27231,c_26536,c_24155,c_23852,c_14611,c_7378,c_5235,c_3245,c_1394,c_959,c_630,c_525,c_180,c_241,c_240,c_221,c_220,c_218,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:52:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.97/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.97/1.49  
% 7.97/1.49  ------  iProver source info
% 7.97/1.49  
% 7.97/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.97/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.97/1.49  git: non_committed_changes: false
% 7.97/1.49  git: last_make_outside_of_git: false
% 7.97/1.49  
% 7.97/1.49  ------ 
% 7.97/1.49  
% 7.97/1.49  ------ Input Options
% 7.97/1.49  
% 7.97/1.49  --out_options                           all
% 7.97/1.49  --tptp_safe_out                         true
% 7.97/1.49  --problem_path                          ""
% 7.97/1.49  --include_path                          ""
% 7.97/1.49  --clausifier                            res/vclausify_rel
% 7.97/1.49  --clausifier_options                    ""
% 7.97/1.49  --stdin                                 false
% 7.97/1.49  --stats_out                             all
% 7.97/1.49  
% 7.97/1.49  ------ General Options
% 7.97/1.49  
% 7.97/1.49  --fof                                   false
% 7.97/1.49  --time_out_real                         305.
% 7.97/1.49  --time_out_virtual                      -1.
% 7.97/1.49  --symbol_type_check                     false
% 7.97/1.49  --clausify_out                          false
% 7.97/1.49  --sig_cnt_out                           false
% 7.97/1.49  --trig_cnt_out                          false
% 7.97/1.49  --trig_cnt_out_tolerance                1.
% 7.97/1.49  --trig_cnt_out_sk_spl                   false
% 7.97/1.49  --abstr_cl_out                          false
% 7.97/1.49  
% 7.97/1.49  ------ Global Options
% 7.97/1.49  
% 7.97/1.49  --schedule                              default
% 7.97/1.49  --add_important_lit                     false
% 7.97/1.49  --prop_solver_per_cl                    1000
% 7.97/1.49  --min_unsat_core                        false
% 7.97/1.49  --soft_assumptions                      false
% 7.97/1.49  --soft_lemma_size                       3
% 7.97/1.49  --prop_impl_unit_size                   0
% 7.97/1.49  --prop_impl_unit                        []
% 7.97/1.49  --share_sel_clauses                     true
% 7.97/1.49  --reset_solvers                         false
% 7.97/1.49  --bc_imp_inh                            [conj_cone]
% 7.97/1.49  --conj_cone_tolerance                   3.
% 7.97/1.49  --extra_neg_conj                        none
% 7.97/1.49  --large_theory_mode                     true
% 7.97/1.49  --prolific_symb_bound                   200
% 7.97/1.49  --lt_threshold                          2000
% 7.97/1.49  --clause_weak_htbl                      true
% 7.97/1.49  --gc_record_bc_elim                     false
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing Options
% 7.97/1.49  
% 7.97/1.49  --preprocessing_flag                    true
% 7.97/1.49  --time_out_prep_mult                    0.1
% 7.97/1.49  --splitting_mode                        input
% 7.97/1.49  --splitting_grd                         true
% 7.97/1.49  --splitting_cvd                         false
% 7.97/1.49  --splitting_cvd_svl                     false
% 7.97/1.49  --splitting_nvd                         32
% 7.97/1.49  --sub_typing                            true
% 7.97/1.49  --prep_gs_sim                           true
% 7.97/1.49  --prep_unflatten                        true
% 7.97/1.49  --prep_res_sim                          true
% 7.97/1.49  --prep_upred                            true
% 7.97/1.49  --prep_sem_filter                       exhaustive
% 7.97/1.49  --prep_sem_filter_out                   false
% 7.97/1.49  --pred_elim                             true
% 7.97/1.49  --res_sim_input                         true
% 7.97/1.49  --eq_ax_congr_red                       true
% 7.97/1.49  --pure_diseq_elim                       true
% 7.97/1.49  --brand_transform                       false
% 7.97/1.49  --non_eq_to_eq                          false
% 7.97/1.49  --prep_def_merge                        true
% 7.97/1.49  --prep_def_merge_prop_impl              false
% 7.97/1.49  --prep_def_merge_mbd                    true
% 7.97/1.49  --prep_def_merge_tr_red                 false
% 7.97/1.49  --prep_def_merge_tr_cl                  false
% 7.97/1.49  --smt_preprocessing                     true
% 7.97/1.49  --smt_ac_axioms                         fast
% 7.97/1.49  --preprocessed_out                      false
% 7.97/1.49  --preprocessed_stats                    false
% 7.97/1.49  
% 7.97/1.49  ------ Abstraction refinement Options
% 7.97/1.49  
% 7.97/1.49  --abstr_ref                             []
% 7.97/1.49  --abstr_ref_prep                        false
% 7.97/1.49  --abstr_ref_until_sat                   false
% 7.97/1.49  --abstr_ref_sig_restrict                funpre
% 7.97/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.97/1.49  --abstr_ref_under                       []
% 7.97/1.49  
% 7.97/1.49  ------ SAT Options
% 7.97/1.49  
% 7.97/1.49  --sat_mode                              false
% 7.97/1.49  --sat_fm_restart_options                ""
% 7.97/1.49  --sat_gr_def                            false
% 7.97/1.49  --sat_epr_types                         true
% 7.97/1.49  --sat_non_cyclic_types                  false
% 7.97/1.49  --sat_finite_models                     false
% 7.97/1.49  --sat_fm_lemmas                         false
% 7.97/1.49  --sat_fm_prep                           false
% 7.97/1.49  --sat_fm_uc_incr                        true
% 7.97/1.49  --sat_out_model                         small
% 7.97/1.49  --sat_out_clauses                       false
% 7.97/1.49  
% 7.97/1.49  ------ QBF Options
% 7.97/1.49  
% 7.97/1.49  --qbf_mode                              false
% 7.97/1.49  --qbf_elim_univ                         false
% 7.97/1.49  --qbf_dom_inst                          none
% 7.97/1.49  --qbf_dom_pre_inst                      false
% 7.97/1.49  --qbf_sk_in                             false
% 7.97/1.49  --qbf_pred_elim                         true
% 7.97/1.49  --qbf_split                             512
% 7.97/1.49  
% 7.97/1.49  ------ BMC1 Options
% 7.97/1.49  
% 7.97/1.49  --bmc1_incremental                      false
% 7.97/1.49  --bmc1_axioms                           reachable_all
% 7.97/1.49  --bmc1_min_bound                        0
% 7.97/1.49  --bmc1_max_bound                        -1
% 7.97/1.49  --bmc1_max_bound_default                -1
% 7.97/1.49  --bmc1_symbol_reachability              true
% 7.97/1.49  --bmc1_property_lemmas                  false
% 7.97/1.49  --bmc1_k_induction                      false
% 7.97/1.49  --bmc1_non_equiv_states                 false
% 7.97/1.49  --bmc1_deadlock                         false
% 7.97/1.49  --bmc1_ucm                              false
% 7.97/1.49  --bmc1_add_unsat_core                   none
% 7.97/1.49  --bmc1_unsat_core_children              false
% 7.97/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.97/1.49  --bmc1_out_stat                         full
% 7.97/1.49  --bmc1_ground_init                      false
% 7.97/1.49  --bmc1_pre_inst_next_state              false
% 7.97/1.49  --bmc1_pre_inst_state                   false
% 7.97/1.49  --bmc1_pre_inst_reach_state             false
% 7.97/1.49  --bmc1_out_unsat_core                   false
% 7.97/1.49  --bmc1_aig_witness_out                  false
% 7.97/1.49  --bmc1_verbose                          false
% 7.97/1.49  --bmc1_dump_clauses_tptp                false
% 7.97/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.97/1.49  --bmc1_dump_file                        -
% 7.97/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.97/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.97/1.49  --bmc1_ucm_extend_mode                  1
% 7.97/1.49  --bmc1_ucm_init_mode                    2
% 7.97/1.49  --bmc1_ucm_cone_mode                    none
% 7.97/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.97/1.49  --bmc1_ucm_relax_model                  4
% 7.97/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.97/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.97/1.49  --bmc1_ucm_layered_model                none
% 7.97/1.49  --bmc1_ucm_max_lemma_size               10
% 7.97/1.49  
% 7.97/1.49  ------ AIG Options
% 7.97/1.49  
% 7.97/1.49  --aig_mode                              false
% 7.97/1.49  
% 7.97/1.49  ------ Instantiation Options
% 7.97/1.49  
% 7.97/1.49  --instantiation_flag                    true
% 7.97/1.49  --inst_sos_flag                         true
% 7.97/1.49  --inst_sos_phase                        true
% 7.97/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.97/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.97/1.49  --inst_lit_sel_side                     num_symb
% 7.97/1.49  --inst_solver_per_active                1400
% 7.97/1.49  --inst_solver_calls_frac                1.
% 7.97/1.49  --inst_passive_queue_type               priority_queues
% 7.97/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.97/1.49  --inst_passive_queues_freq              [25;2]
% 7.97/1.49  --inst_dismatching                      true
% 7.97/1.49  --inst_eager_unprocessed_to_passive     true
% 7.97/1.49  --inst_prop_sim_given                   true
% 7.97/1.49  --inst_prop_sim_new                     false
% 7.97/1.49  --inst_subs_new                         false
% 7.97/1.49  --inst_eq_res_simp                      false
% 7.97/1.49  --inst_subs_given                       false
% 7.97/1.49  --inst_orphan_elimination               true
% 7.97/1.49  --inst_learning_loop_flag               true
% 7.97/1.49  --inst_learning_start                   3000
% 7.97/1.49  --inst_learning_factor                  2
% 7.97/1.49  --inst_start_prop_sim_after_learn       3
% 7.97/1.49  --inst_sel_renew                        solver
% 7.97/1.49  --inst_lit_activity_flag                true
% 7.97/1.49  --inst_restr_to_given                   false
% 7.97/1.49  --inst_activity_threshold               500
% 7.97/1.49  --inst_out_proof                        true
% 7.97/1.49  
% 7.97/1.49  ------ Resolution Options
% 7.97/1.49  
% 7.97/1.49  --resolution_flag                       true
% 7.97/1.49  --res_lit_sel                           adaptive
% 7.97/1.49  --res_lit_sel_side                      none
% 7.97/1.49  --res_ordering                          kbo
% 7.97/1.49  --res_to_prop_solver                    active
% 7.97/1.49  --res_prop_simpl_new                    false
% 7.97/1.49  --res_prop_simpl_given                  true
% 7.97/1.49  --res_passive_queue_type                priority_queues
% 7.97/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.97/1.49  --res_passive_queues_freq               [15;5]
% 7.97/1.49  --res_forward_subs                      full
% 7.97/1.49  --res_backward_subs                     full
% 7.97/1.49  --res_forward_subs_resolution           true
% 7.97/1.49  --res_backward_subs_resolution          true
% 7.97/1.49  --res_orphan_elimination                true
% 7.97/1.49  --res_time_limit                        2.
% 7.97/1.49  --res_out_proof                         true
% 7.97/1.49  
% 7.97/1.49  ------ Superposition Options
% 7.97/1.49  
% 7.97/1.49  --superposition_flag                    true
% 7.97/1.49  --sup_passive_queue_type                priority_queues
% 7.97/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.97/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.97/1.49  --demod_completeness_check              fast
% 7.97/1.49  --demod_use_ground                      true
% 7.97/1.49  --sup_to_prop_solver                    passive
% 7.97/1.49  --sup_prop_simpl_new                    true
% 7.97/1.49  --sup_prop_simpl_given                  true
% 7.97/1.49  --sup_fun_splitting                     true
% 7.97/1.49  --sup_smt_interval                      50000
% 7.97/1.49  
% 7.97/1.49  ------ Superposition Simplification Setup
% 7.97/1.49  
% 7.97/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.97/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.97/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.97/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.97/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.97/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.97/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.97/1.49  --sup_immed_triv                        [TrivRules]
% 7.97/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_immed_bw_main                     []
% 7.97/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.97/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.97/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_input_bw                          []
% 7.97/1.49  
% 7.97/1.49  ------ Combination Options
% 7.97/1.49  
% 7.97/1.49  --comb_res_mult                         3
% 7.97/1.49  --comb_sup_mult                         2
% 7.97/1.49  --comb_inst_mult                        10
% 7.97/1.49  
% 7.97/1.49  ------ Debug Options
% 7.97/1.49  
% 7.97/1.49  --dbg_backtrace                         false
% 7.97/1.49  --dbg_dump_prop_clauses                 false
% 7.97/1.49  --dbg_dump_prop_clauses_file            -
% 7.97/1.49  --dbg_out_stat                          false
% 7.97/1.49  ------ Parsing...
% 7.97/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.97/1.49  ------ Proving...
% 7.97/1.49  ------ Problem Properties 
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  clauses                                 17
% 7.97/1.49  conjectures                             3
% 7.97/1.49  EPR                                     4
% 7.97/1.49  Horn                                    16
% 7.97/1.49  unary                                   4
% 7.97/1.49  binary                                  7
% 7.97/1.49  lits                                    36
% 7.97/1.49  lits eq                                 7
% 7.97/1.49  fd_pure                                 0
% 7.97/1.49  fd_pseudo                               0
% 7.97/1.49  fd_cond                                 0
% 7.97/1.49  fd_pseudo_cond                          0
% 7.97/1.49  AC symbols                              0
% 7.97/1.49  
% 7.97/1.49  ------ Schedule dynamic 5 is on 
% 7.97/1.49  
% 7.97/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  ------ 
% 7.97/1.49  Current options:
% 7.97/1.49  ------ 
% 7.97/1.49  
% 7.97/1.49  ------ Input Options
% 7.97/1.49  
% 7.97/1.49  --out_options                           all
% 7.97/1.49  --tptp_safe_out                         true
% 7.97/1.49  --problem_path                          ""
% 7.97/1.49  --include_path                          ""
% 7.97/1.49  --clausifier                            res/vclausify_rel
% 7.97/1.49  --clausifier_options                    ""
% 7.97/1.49  --stdin                                 false
% 7.97/1.49  --stats_out                             all
% 7.97/1.49  
% 7.97/1.49  ------ General Options
% 7.97/1.49  
% 7.97/1.49  --fof                                   false
% 7.97/1.49  --time_out_real                         305.
% 7.97/1.49  --time_out_virtual                      -1.
% 7.97/1.49  --symbol_type_check                     false
% 7.97/1.49  --clausify_out                          false
% 7.97/1.49  --sig_cnt_out                           false
% 7.97/1.49  --trig_cnt_out                          false
% 7.97/1.49  --trig_cnt_out_tolerance                1.
% 7.97/1.49  --trig_cnt_out_sk_spl                   false
% 7.97/1.49  --abstr_cl_out                          false
% 7.97/1.49  
% 7.97/1.49  ------ Global Options
% 7.97/1.49  
% 7.97/1.49  --schedule                              default
% 7.97/1.49  --add_important_lit                     false
% 7.97/1.49  --prop_solver_per_cl                    1000
% 7.97/1.49  --min_unsat_core                        false
% 7.97/1.49  --soft_assumptions                      false
% 7.97/1.49  --soft_lemma_size                       3
% 7.97/1.49  --prop_impl_unit_size                   0
% 7.97/1.49  --prop_impl_unit                        []
% 7.97/1.49  --share_sel_clauses                     true
% 7.97/1.49  --reset_solvers                         false
% 7.97/1.49  --bc_imp_inh                            [conj_cone]
% 7.97/1.49  --conj_cone_tolerance                   3.
% 7.97/1.49  --extra_neg_conj                        none
% 7.97/1.49  --large_theory_mode                     true
% 7.97/1.49  --prolific_symb_bound                   200
% 7.97/1.49  --lt_threshold                          2000
% 7.97/1.49  --clause_weak_htbl                      true
% 7.97/1.49  --gc_record_bc_elim                     false
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing Options
% 7.97/1.49  
% 7.97/1.49  --preprocessing_flag                    true
% 7.97/1.49  --time_out_prep_mult                    0.1
% 7.97/1.49  --splitting_mode                        input
% 7.97/1.49  --splitting_grd                         true
% 7.97/1.49  --splitting_cvd                         false
% 7.97/1.49  --splitting_cvd_svl                     false
% 7.97/1.49  --splitting_nvd                         32
% 7.97/1.49  --sub_typing                            true
% 7.97/1.49  --prep_gs_sim                           true
% 7.97/1.49  --prep_unflatten                        true
% 7.97/1.49  --prep_res_sim                          true
% 7.97/1.49  --prep_upred                            true
% 7.97/1.49  --prep_sem_filter                       exhaustive
% 7.97/1.49  --prep_sem_filter_out                   false
% 7.97/1.49  --pred_elim                             true
% 7.97/1.49  --res_sim_input                         true
% 7.97/1.49  --eq_ax_congr_red                       true
% 7.97/1.49  --pure_diseq_elim                       true
% 7.97/1.49  --brand_transform                       false
% 7.97/1.49  --non_eq_to_eq                          false
% 7.97/1.49  --prep_def_merge                        true
% 7.97/1.49  --prep_def_merge_prop_impl              false
% 7.97/1.49  --prep_def_merge_mbd                    true
% 7.97/1.49  --prep_def_merge_tr_red                 false
% 7.97/1.49  --prep_def_merge_tr_cl                  false
% 7.97/1.49  --smt_preprocessing                     true
% 7.97/1.49  --smt_ac_axioms                         fast
% 7.97/1.49  --preprocessed_out                      false
% 7.97/1.49  --preprocessed_stats                    false
% 7.97/1.49  
% 7.97/1.49  ------ Abstraction refinement Options
% 7.97/1.49  
% 7.97/1.49  --abstr_ref                             []
% 7.97/1.49  --abstr_ref_prep                        false
% 7.97/1.49  --abstr_ref_until_sat                   false
% 7.97/1.49  --abstr_ref_sig_restrict                funpre
% 7.97/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.97/1.49  --abstr_ref_under                       []
% 7.97/1.49  
% 7.97/1.49  ------ SAT Options
% 7.97/1.49  
% 7.97/1.49  --sat_mode                              false
% 7.97/1.49  --sat_fm_restart_options                ""
% 7.97/1.49  --sat_gr_def                            false
% 7.97/1.49  --sat_epr_types                         true
% 7.97/1.49  --sat_non_cyclic_types                  false
% 7.97/1.49  --sat_finite_models                     false
% 7.97/1.49  --sat_fm_lemmas                         false
% 7.97/1.49  --sat_fm_prep                           false
% 7.97/1.49  --sat_fm_uc_incr                        true
% 7.97/1.49  --sat_out_model                         small
% 7.97/1.49  --sat_out_clauses                       false
% 7.97/1.49  
% 7.97/1.49  ------ QBF Options
% 7.97/1.49  
% 7.97/1.49  --qbf_mode                              false
% 7.97/1.49  --qbf_elim_univ                         false
% 7.97/1.49  --qbf_dom_inst                          none
% 7.97/1.49  --qbf_dom_pre_inst                      false
% 7.97/1.49  --qbf_sk_in                             false
% 7.97/1.49  --qbf_pred_elim                         true
% 7.97/1.49  --qbf_split                             512
% 7.97/1.49  
% 7.97/1.49  ------ BMC1 Options
% 7.97/1.49  
% 7.97/1.49  --bmc1_incremental                      false
% 7.97/1.49  --bmc1_axioms                           reachable_all
% 7.97/1.49  --bmc1_min_bound                        0
% 7.97/1.49  --bmc1_max_bound                        -1
% 7.97/1.49  --bmc1_max_bound_default                -1
% 7.97/1.49  --bmc1_symbol_reachability              true
% 7.97/1.49  --bmc1_property_lemmas                  false
% 7.97/1.49  --bmc1_k_induction                      false
% 7.97/1.49  --bmc1_non_equiv_states                 false
% 7.97/1.49  --bmc1_deadlock                         false
% 7.97/1.49  --bmc1_ucm                              false
% 7.97/1.49  --bmc1_add_unsat_core                   none
% 7.97/1.49  --bmc1_unsat_core_children              false
% 7.97/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.97/1.49  --bmc1_out_stat                         full
% 7.97/1.49  --bmc1_ground_init                      false
% 7.97/1.49  --bmc1_pre_inst_next_state              false
% 7.97/1.49  --bmc1_pre_inst_state                   false
% 7.97/1.49  --bmc1_pre_inst_reach_state             false
% 7.97/1.49  --bmc1_out_unsat_core                   false
% 7.97/1.49  --bmc1_aig_witness_out                  false
% 7.97/1.49  --bmc1_verbose                          false
% 7.97/1.49  --bmc1_dump_clauses_tptp                false
% 7.97/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.97/1.49  --bmc1_dump_file                        -
% 7.97/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.97/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.97/1.49  --bmc1_ucm_extend_mode                  1
% 7.97/1.49  --bmc1_ucm_init_mode                    2
% 7.97/1.49  --bmc1_ucm_cone_mode                    none
% 7.97/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.97/1.49  --bmc1_ucm_relax_model                  4
% 7.97/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.97/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.97/1.49  --bmc1_ucm_layered_model                none
% 7.97/1.49  --bmc1_ucm_max_lemma_size               10
% 7.97/1.49  
% 7.97/1.49  ------ AIG Options
% 7.97/1.49  
% 7.97/1.49  --aig_mode                              false
% 7.97/1.49  
% 7.97/1.49  ------ Instantiation Options
% 7.97/1.49  
% 7.97/1.49  --instantiation_flag                    true
% 7.97/1.49  --inst_sos_flag                         true
% 7.97/1.49  --inst_sos_phase                        true
% 7.97/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.97/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.97/1.49  --inst_lit_sel_side                     none
% 7.97/1.49  --inst_solver_per_active                1400
% 7.97/1.49  --inst_solver_calls_frac                1.
% 7.97/1.49  --inst_passive_queue_type               priority_queues
% 7.97/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.97/1.49  --inst_passive_queues_freq              [25;2]
% 7.97/1.49  --inst_dismatching                      true
% 7.97/1.49  --inst_eager_unprocessed_to_passive     true
% 7.97/1.49  --inst_prop_sim_given                   true
% 7.97/1.49  --inst_prop_sim_new                     false
% 7.97/1.49  --inst_subs_new                         false
% 7.97/1.49  --inst_eq_res_simp                      false
% 7.97/1.49  --inst_subs_given                       false
% 7.97/1.49  --inst_orphan_elimination               true
% 7.97/1.49  --inst_learning_loop_flag               true
% 7.97/1.49  --inst_learning_start                   3000
% 7.97/1.49  --inst_learning_factor                  2
% 7.97/1.49  --inst_start_prop_sim_after_learn       3
% 7.97/1.49  --inst_sel_renew                        solver
% 7.97/1.49  --inst_lit_activity_flag                true
% 7.97/1.49  --inst_restr_to_given                   false
% 7.97/1.49  --inst_activity_threshold               500
% 7.97/1.49  --inst_out_proof                        true
% 7.97/1.49  
% 7.97/1.49  ------ Resolution Options
% 7.97/1.49  
% 7.97/1.49  --resolution_flag                       false
% 7.97/1.49  --res_lit_sel                           adaptive
% 7.97/1.49  --res_lit_sel_side                      none
% 7.97/1.49  --res_ordering                          kbo
% 7.97/1.49  --res_to_prop_solver                    active
% 7.97/1.49  --res_prop_simpl_new                    false
% 7.97/1.49  --res_prop_simpl_given                  true
% 7.97/1.49  --res_passive_queue_type                priority_queues
% 7.97/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.97/1.49  --res_passive_queues_freq               [15;5]
% 7.97/1.49  --res_forward_subs                      full
% 7.97/1.49  --res_backward_subs                     full
% 7.97/1.49  --res_forward_subs_resolution           true
% 7.97/1.49  --res_backward_subs_resolution          true
% 7.97/1.49  --res_orphan_elimination                true
% 7.97/1.49  --res_time_limit                        2.
% 7.97/1.49  --res_out_proof                         true
% 7.97/1.49  
% 7.97/1.49  ------ Superposition Options
% 7.97/1.49  
% 7.97/1.49  --superposition_flag                    true
% 7.97/1.49  --sup_passive_queue_type                priority_queues
% 7.97/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.97/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.97/1.49  --demod_completeness_check              fast
% 7.97/1.49  --demod_use_ground                      true
% 7.97/1.49  --sup_to_prop_solver                    passive
% 7.97/1.49  --sup_prop_simpl_new                    true
% 7.97/1.49  --sup_prop_simpl_given                  true
% 7.97/1.49  --sup_fun_splitting                     true
% 7.97/1.49  --sup_smt_interval                      50000
% 7.97/1.49  
% 7.97/1.49  ------ Superposition Simplification Setup
% 7.97/1.49  
% 7.97/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.97/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.97/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.97/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.97/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.97/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.97/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.97/1.49  --sup_immed_triv                        [TrivRules]
% 7.97/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_immed_bw_main                     []
% 7.97/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.97/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.97/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.49  --sup_input_bw                          []
% 7.97/1.49  
% 7.97/1.49  ------ Combination Options
% 7.97/1.49  
% 7.97/1.49  --comb_res_mult                         3
% 7.97/1.49  --comb_sup_mult                         2
% 7.97/1.49  --comb_inst_mult                        10
% 7.97/1.49  
% 7.97/1.49  ------ Debug Options
% 7.97/1.49  
% 7.97/1.49  --dbg_backtrace                         false
% 7.97/1.49  --dbg_dump_prop_clauses                 false
% 7.97/1.49  --dbg_dump_prop_clauses_file            -
% 7.97/1.49  --dbg_out_stat                          false
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  ------ Proving...
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  % SZS status Theorem for theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  fof(f1,axiom,(
% 7.97/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f19,plain,(
% 7.97/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.97/1.49    inference(ennf_transformation,[],[f1])).
% 7.97/1.49  
% 7.97/1.49  fof(f35,plain,(
% 7.97/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.97/1.49    inference(nnf_transformation,[],[f19])).
% 7.97/1.49  
% 7.97/1.49  fof(f36,plain,(
% 7.97/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.97/1.49    inference(rectify,[],[f35])).
% 7.97/1.49  
% 7.97/1.49  fof(f37,plain,(
% 7.97/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.97/1.49    introduced(choice_axiom,[])).
% 7.97/1.49  
% 7.97/1.49  fof(f38,plain,(
% 7.97/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.97/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 7.97/1.49  
% 7.97/1.49  fof(f42,plain,(
% 7.97/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f38])).
% 7.97/1.49  
% 7.97/1.49  fof(f15,axiom,(
% 7.97/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f30,plain,(
% 7.97/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.97/1.49    inference(ennf_transformation,[],[f15])).
% 7.97/1.49  
% 7.97/1.49  fof(f31,plain,(
% 7.97/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 7.97/1.49    inference(flattening,[],[f30])).
% 7.97/1.49  
% 7.97/1.49  fof(f58,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f31])).
% 7.97/1.49  
% 7.97/1.49  fof(f17,conjecture,(
% 7.97/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f18,negated_conjecture,(
% 7.97/1.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 7.97/1.49    inference(negated_conjecture,[],[f17])).
% 7.97/1.49  
% 7.97/1.49  fof(f33,plain,(
% 7.97/1.49    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 7.97/1.49    inference(ennf_transformation,[],[f18])).
% 7.97/1.49  
% 7.97/1.49  fof(f34,plain,(
% 7.97/1.49    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 7.97/1.49    inference(flattening,[],[f33])).
% 7.97/1.49  
% 7.97/1.49  fof(f39,plain,(
% 7.97/1.49    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3))),
% 7.97/1.49    introduced(choice_axiom,[])).
% 7.97/1.49  
% 7.97/1.49  fof(f40,plain,(
% 7.97/1.49    k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3)),
% 7.97/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f39])).
% 7.97/1.49  
% 7.97/1.49  fof(f61,plain,(
% 7.97/1.49    r1_tarski(sK1,sK2)),
% 7.97/1.49    inference(cnf_transformation,[],[f40])).
% 7.97/1.49  
% 7.97/1.49  fof(f41,plain,(
% 7.97/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f38])).
% 7.97/1.49  
% 7.97/1.49  fof(f43,plain,(
% 7.97/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f38])).
% 7.97/1.49  
% 7.97/1.49  fof(f60,plain,(
% 7.97/1.49    v1_relat_1(sK3)),
% 7.97/1.49    inference(cnf_transformation,[],[f40])).
% 7.97/1.49  
% 7.97/1.49  fof(f13,axiom,(
% 7.97/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f28,plain,(
% 7.97/1.49    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 7.97/1.49    inference(ennf_transformation,[],[f13])).
% 7.97/1.49  
% 7.97/1.49  fof(f55,plain,(
% 7.97/1.49    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f28])).
% 7.97/1.49  
% 7.97/1.49  fof(f10,axiom,(
% 7.97/1.49    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f23,plain,(
% 7.97/1.49    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.97/1.49    inference(ennf_transformation,[],[f10])).
% 7.97/1.49  
% 7.97/1.49  fof(f52,plain,(
% 7.97/1.49    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f23])).
% 7.97/1.49  
% 7.97/1.49  fof(f9,axiom,(
% 7.97/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f51,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.97/1.49    inference(cnf_transformation,[],[f9])).
% 7.97/1.49  
% 7.97/1.49  fof(f5,axiom,(
% 7.97/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f47,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f5])).
% 7.97/1.49  
% 7.97/1.49  fof(f6,axiom,(
% 7.97/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f48,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f6])).
% 7.97/1.49  
% 7.97/1.49  fof(f7,axiom,(
% 7.97/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f49,plain,(
% 7.97/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f7])).
% 7.97/1.49  
% 7.97/1.49  fof(f8,axiom,(
% 7.97/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f50,plain,(
% 7.97/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f8])).
% 7.97/1.49  
% 7.97/1.49  fof(f63,plain,(
% 7.97/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.97/1.49    inference(definition_unfolding,[],[f49,f50])).
% 7.97/1.49  
% 7.97/1.49  fof(f64,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.97/1.49    inference(definition_unfolding,[],[f48,f63])).
% 7.97/1.49  
% 7.97/1.49  fof(f65,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.97/1.49    inference(definition_unfolding,[],[f47,f64])).
% 7.97/1.49  
% 7.97/1.49  fof(f66,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 7.97/1.49    inference(definition_unfolding,[],[f51,f65])).
% 7.97/1.49  
% 7.97/1.49  fof(f69,plain,(
% 7.97/1.49    ( ! [X0] : (k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.97/1.49    inference(definition_unfolding,[],[f52,f66])).
% 7.97/1.49  
% 7.97/1.49  fof(f2,axiom,(
% 7.97/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f20,plain,(
% 7.97/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.97/1.49    inference(ennf_transformation,[],[f2])).
% 7.97/1.49  
% 7.97/1.49  fof(f44,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f20])).
% 7.97/1.49  
% 7.97/1.49  fof(f67,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X2)) )),
% 7.97/1.49    inference(definition_unfolding,[],[f44,f66])).
% 7.97/1.49  
% 7.97/1.49  fof(f12,axiom,(
% 7.97/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f26,plain,(
% 7.97/1.49    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.97/1.49    inference(ennf_transformation,[],[f12])).
% 7.97/1.49  
% 7.97/1.49  fof(f27,plain,(
% 7.97/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.97/1.49    inference(flattening,[],[f26])).
% 7.97/1.49  
% 7.97/1.49  fof(f54,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f27])).
% 7.97/1.49  
% 7.97/1.49  fof(f4,axiom,(
% 7.97/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f46,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f4])).
% 7.97/1.49  
% 7.97/1.49  fof(f68,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 7.97/1.49    inference(definition_unfolding,[],[f46,f65,f65])).
% 7.97/1.49  
% 7.97/1.49  fof(f11,axiom,(
% 7.97/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f24,plain,(
% 7.97/1.49    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.97/1.49    inference(ennf_transformation,[],[f11])).
% 7.97/1.49  
% 7.97/1.49  fof(f25,plain,(
% 7.97/1.49    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.97/1.49    inference(flattening,[],[f24])).
% 7.97/1.49  
% 7.97/1.49  fof(f53,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f25])).
% 7.97/1.49  
% 7.97/1.49  fof(f14,axiom,(
% 7.97/1.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f29,plain,(
% 7.97/1.49    ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 7.97/1.49    inference(ennf_transformation,[],[f14])).
% 7.97/1.49  
% 7.97/1.49  fof(f56,plain,(
% 7.97/1.49    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f29])).
% 7.97/1.49  
% 7.97/1.49  fof(f16,axiom,(
% 7.97/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 7.97/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.49  
% 7.97/1.49  fof(f32,plain,(
% 7.97/1.49    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 7.97/1.49    inference(ennf_transformation,[],[f16])).
% 7.97/1.49  
% 7.97/1.49  fof(f59,plain,(
% 7.97/1.49    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 7.97/1.49    inference(cnf_transformation,[],[f32])).
% 7.97/1.49  
% 7.97/1.49  fof(f62,plain,(
% 7.97/1.49    k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1)),
% 7.97/1.49    inference(cnf_transformation,[],[f40])).
% 7.97/1.49  
% 7.97/1.49  cnf(c_200,plain,
% 7.97/1.49      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 7.97/1.49      theory(equality) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_526,plain,
% 7.97/1.49      ( X0_43 != X1_43
% 7.97/1.49      | k2_wellord1(sK3,sK1) != X1_43
% 7.97/1.49      | k2_wellord1(sK3,sK1) = X0_43 ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_535,plain,
% 7.97/1.49      ( X0_43 != k2_wellord1(sK3,sK1)
% 7.97/1.49      | k2_wellord1(sK3,sK1) = X0_43
% 7.97/1.49      | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_526]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_551,plain,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1)
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k7_relat_1(k2_wellord1(sK3,sK1),X0_44)
% 7.97/1.49      | k7_relat_1(k2_wellord1(sK3,sK1),X0_44) != k2_wellord1(sK3,sK1) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_535]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_29001,plain,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1)
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k7_relat_1(k2_wellord1(sK3,sK1),sK2)
% 7.97/1.49      | k7_relat_1(k2_wellord1(sK3,sK1),sK2) != k2_wellord1(sK3,sK1) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_551]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1373,plain,
% 7.97/1.49      ( X0_43 != X1_43
% 7.97/1.49      | X0_43 = k8_relat_1(X0_44,X2_43)
% 7.97/1.49      | k8_relat_1(X0_44,X2_43) != X1_43 ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3617,plain,
% 7.97/1.49      ( X0_43 != k8_relat_1(X0_44,X1_43)
% 7.97/1.49      | X0_43 = k8_relat_1(X0_44,X2_43)
% 7.97/1.49      | k8_relat_1(X0_44,X2_43) != k8_relat_1(X0_44,X1_43) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_1373]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_6822,plain,
% 7.97/1.49      ( k8_relat_1(X0_44,X0_43) != k8_relat_1(X0_44,X0_43)
% 7.97/1.49      | k8_relat_1(X0_44,X1_43) != k8_relat_1(X0_44,X0_43)
% 7.97/1.49      | k8_relat_1(X0_44,X0_43) = k8_relat_1(X0_44,X1_43) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_3617]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_27230,plain,
% 7.97/1.49      ( k8_relat_1(sK2,k2_wellord1(X0_43,X0_44)) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2))
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2)) = k8_relat_1(sK2,k2_wellord1(X0_43,X0_44))
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2)) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_6822]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_27231,plain,
% 7.97/1.49      ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2))
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) = k8_relat_1(sK2,k2_wellord1(sK3,sK1))
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_27230]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_726,plain,
% 7.97/1.49      ( X0_43 != X1_43
% 7.97/1.49      | X0_43 = k8_relat_1(X0_44,k7_relat_1(X2_43,X0_44))
% 7.97/1.49      | k8_relat_1(X0_44,k7_relat_1(X2_43,X0_44)) != X1_43 ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_811,plain,
% 7.97/1.49      ( X0_43 != k2_wellord1(X1_43,X0_44)
% 7.97/1.49      | X0_43 = k8_relat_1(X0_44,k7_relat_1(X1_43,X0_44))
% 7.97/1.49      | k8_relat_1(X0_44,k7_relat_1(X1_43,X0_44)) != k2_wellord1(X1_43,X0_44) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_726]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1872,plain,
% 7.97/1.49      ( k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) != k2_wellord1(X0_43,X0_44)
% 7.97/1.49      | k8_relat_1(X1_44,k7_relat_1(X1_43,X1_44)) != k2_wellord1(X0_43,X0_44)
% 7.97/1.49      | k8_relat_1(X1_44,k7_relat_1(X1_43,X1_44)) = k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_811]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_5992,plain,
% 7.97/1.49      ( k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) != k2_wellord1(X1_43,sK2)
% 7.97/1.49      | k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) = k8_relat_1(sK2,k7_relat_1(X1_43,sK2))
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(X1_43,sK2)) != k2_wellord1(X1_43,sK2) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_1872]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_26536,plain,
% 7.97/1.49      ( k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_5992]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1,plain,
% 7.97/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_193,plain,
% 7.97/1.49      ( r2_hidden(sK0(X0_44,X1_44),X0_44) | r1_tarski(X0_44,X1_44) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_489,plain,
% 7.97/1.49      ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
% 7.97/1.49      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_11,plain,
% 7.97/1.49      ( r2_hidden(X0,X1)
% 7.97/1.49      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
% 7.97/1.49      | ~ v1_relat_1(X2) ),
% 7.97/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_183,plain,
% 7.97/1.49      ( r2_hidden(X0_45,X0_44)
% 7.97/1.49      | ~ r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44)))
% 7.97/1.49      | ~ v1_relat_1(X0_43) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_498,plain,
% 7.97/1.49      ( r2_hidden(X0_45,X0_44) = iProver_top
% 7.97/1.49      | r2_hidden(X0_45,k3_relat_1(k2_wellord1(X0_43,X0_44))) != iProver_top
% 7.97/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1402,plain,
% 7.97/1.49      ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44),X0_44) = iProver_top
% 7.97/1.49      | r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_44)),X1_44) = iProver_top
% 7.97/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_489,c_498]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_15,negated_conjecture,
% 7.97/1.49      ( r1_tarski(sK1,sK2) ),
% 7.97/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_179,negated_conjecture,
% 7.97/1.49      ( r1_tarski(sK1,sK2) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_501,plain,
% 7.97/1.49      ( r1_tarski(sK1,sK2) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_179]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_2,plain,
% 7.97/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.97/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_192,plain,
% 7.97/1.49      ( ~ r2_hidden(X0_45,X0_44)
% 7.97/1.49      | r2_hidden(X0_45,X1_44)
% 7.97/1.49      | ~ r1_tarski(X0_44,X1_44) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_490,plain,
% 7.97/1.49      ( r2_hidden(X0_45,X0_44) != iProver_top
% 7.97/1.49      | r2_hidden(X0_45,X1_44) = iProver_top
% 7.97/1.49      | r1_tarski(X0_44,X1_44) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_802,plain,
% 7.97/1.49      ( r2_hidden(X0_45,sK2) = iProver_top
% 7.97/1.49      | r2_hidden(X0_45,sK1) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_501,c_490]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_8458,plain,
% 7.97/1.49      ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44),sK2) = iProver_top
% 7.97/1.49      | r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),X0_44) = iProver_top
% 7.97/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_1402,c_802]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_0,plain,
% 7.97/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_194,plain,
% 7.97/1.49      ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44) | r1_tarski(X0_44,X1_44) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_488,plain,
% 7.97/1.49      ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
% 7.97/1.49      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_194]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_10580,plain,
% 7.97/1.49      ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,sK1)),sK2) = iProver_top
% 7.97/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_8458,c_488]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_16,negated_conjecture,
% 7.97/1.49      ( v1_relat_1(sK3) ),
% 7.97/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_178,negated_conjecture,
% 7.97/1.49      ( v1_relat_1(sK3) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_502,plain,
% 7.97/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_178]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_9,plain,
% 7.97/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 7.97/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_185,plain,
% 7.97/1.49      ( ~ v1_relat_1(X0_43) | v1_relat_1(k2_wellord1(X0_43,X0_44)) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_496,plain,
% 7.97/1.49      ( v1_relat_1(X0_43) != iProver_top
% 7.97/1.49      | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_6,plain,
% 7.97/1.49      ( ~ v1_relat_1(X0)
% 7.97/1.49      | k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 7.97/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_188,plain,
% 7.97/1.49      ( ~ v1_relat_1(X0_43)
% 7.97/1.49      | k3_tarski(k4_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_493,plain,
% 7.97/1.49      ( k3_tarski(k4_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
% 7.97/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1231,plain,
% 7.97/1.49      ( k3_tarski(k4_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k1_relat_1(k2_wellord1(X0_43,X0_44)),k2_relat_1(k2_wellord1(X0_43,X0_44)))) = k3_relat_1(k2_wellord1(X0_43,X0_44))
% 7.97/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_496,c_493]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_7161,plain,
% 7.97/1.49      ( k3_tarski(k4_enumset1(k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k1_relat_1(k2_wellord1(sK3,X0_44)),k2_relat_1(k2_wellord1(sK3,X0_44)))) = k3_relat_1(k2_wellord1(sK3,X0_44)) ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_502,c_1231]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3,plain,
% 7.97/1.49      ( r1_tarski(X0,X1)
% 7.97/1.49      | ~ r1_tarski(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2)),X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_191,plain,
% 7.97/1.49      ( r1_tarski(X0_44,X1_44)
% 7.97/1.49      | ~ r1_tarski(k3_tarski(k4_enumset1(X0_44,X0_44,X0_44,X0_44,X0_44,X2_44)),X1_44) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_491,plain,
% 7.97/1.49      ( r1_tarski(X0_44,X1_44) = iProver_top
% 7.97/1.49      | r1_tarski(k3_tarski(k4_enumset1(X0_44,X0_44,X0_44,X0_44,X0_44,X2_44)),X1_44) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_7810,plain,
% 7.97/1.49      ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
% 7.97/1.49      | r1_tarski(k1_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_7161,c_491]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_14801,plain,
% 7.97/1.49      ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
% 7.97/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_10580,c_7810]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_17,plain,
% 7.97/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_24151,plain,
% 7.97/1.49      ( r1_tarski(k1_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
% 7.97/1.49      inference(global_propositional_subsumption,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_14801,c_17]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_8,plain,
% 7.97/1.49      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.97/1.49      | ~ v1_relat_1(X0)
% 7.97/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.97/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_186,plain,
% 7.97/1.49      ( ~ r1_tarski(k1_relat_1(X0_43),X0_44)
% 7.97/1.49      | ~ v1_relat_1(X0_43)
% 7.97/1.49      | k7_relat_1(X0_43,X0_44) = X0_43 ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_495,plain,
% 7.97/1.49      ( k7_relat_1(X0_43,X0_44) = X0_43
% 7.97/1.49      | r1_tarski(k1_relat_1(X0_43),X0_44) != iProver_top
% 7.97/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_24155,plain,
% 7.97/1.49      ( k7_relat_1(k2_wellord1(sK3,sK1),sK2) = k2_wellord1(sK3,sK1)
% 7.97/1.49      | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_24151,c_495]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_5,plain,
% 7.97/1.49      ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
% 7.97/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_189,plain,
% 7.97/1.49      ( k4_enumset1(X0_44,X0_44,X0_44,X0_44,X0_44,X1_44) = k4_enumset1(X1_44,X1_44,X1_44,X1_44,X1_44,X0_44) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_807,plain,
% 7.97/1.49      ( r1_tarski(X0_44,X1_44) = iProver_top
% 7.97/1.49      | r1_tarski(k3_tarski(k4_enumset1(X2_44,X2_44,X2_44,X2_44,X2_44,X0_44)),X1_44) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_189,c_491]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_7813,plain,
% 7.97/1.49      ( r1_tarski(k3_relat_1(k2_wellord1(sK3,X0_44)),X1_44) != iProver_top
% 7.97/1.49      | r1_tarski(k2_relat_1(k2_wellord1(sK3,X0_44)),X1_44) = iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_7161,c_807]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_14800,plain,
% 7.97/1.49      ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top
% 7.97/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_10580,c_7813]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_23848,plain,
% 7.97/1.49      ( r1_tarski(k2_relat_1(k2_wellord1(sK3,sK1)),sK2) = iProver_top ),
% 7.97/1.49      inference(global_propositional_subsumption,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_14800,c_17]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_7,plain,
% 7.97/1.49      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.97/1.49      | ~ v1_relat_1(X0)
% 7.97/1.49      | k8_relat_1(X1,X0) = X0 ),
% 7.97/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_187,plain,
% 7.97/1.49      ( ~ r1_tarski(k2_relat_1(X0_43),X0_44)
% 7.97/1.49      | ~ v1_relat_1(X0_43)
% 7.97/1.49      | k8_relat_1(X0_44,X0_43) = X0_43 ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_494,plain,
% 7.97/1.49      ( k8_relat_1(X0_44,X0_43) = X0_43
% 7.97/1.49      | r1_tarski(k2_relat_1(X0_43),X0_44) != iProver_top
% 7.97/1.49      | v1_relat_1(X0_43) != iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_23852,plain,
% 7.97/1.49      ( k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k2_wellord1(sK3,sK1)
% 7.97/1.49      | v1_relat_1(k2_wellord1(sK3,sK1)) != iProver_top ),
% 7.97/1.49      inference(superposition,[status(thm)],[c_23848,c_494]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_538,plain,
% 7.97/1.49      ( X0_43 != k2_wellord1(X1_43,X0_44)
% 7.97/1.49      | k2_wellord1(sK3,sK1) = X0_43
% 7.97/1.49      | k2_wellord1(sK3,sK1) != k2_wellord1(X1_43,X0_44) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_526]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_14610,plain,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k2_wellord1(X0_43,X0_44)
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k8_relat_1(sK2,k2_wellord1(sK3,sK1))
% 7.97/1.49      | k8_relat_1(sK2,k2_wellord1(sK3,sK1)) != k2_wellord1(X0_43,X0_44) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_538]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_14611,plain,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1)
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k8_relat_1(sK2,k2_wellord1(sK3,sK1))
% 7.97/1.49      | k8_relat_1(sK2,k2_wellord1(sK3,sK1)) != k2_wellord1(sK3,sK1) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_14610]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_209,plain,
% 7.97/1.49      ( X0_43 != X1_43
% 7.97/1.49      | k8_relat_1(X0_44,X0_43) = k8_relat_1(X0_44,X1_43) ),
% 7.97/1.49      theory(equality) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_819,plain,
% 7.97/1.49      ( X0_43 != k7_relat_1(X1_43,X0_44)
% 7.97/1.49      | k8_relat_1(X0_44,X0_43) = k8_relat_1(X0_44,k7_relat_1(X1_43,X0_44)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_209]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1434,plain,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),X0_44)
% 7.97/1.49      | k8_relat_1(X0_44,k2_wellord1(sK3,sK1)) = k8_relat_1(X0_44,k7_relat_1(k2_wellord1(sK3,sK1),X0_44)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_819]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_7378,plain,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k7_relat_1(k2_wellord1(sK3,sK1),sK2)
% 7.97/1.49      | k8_relat_1(sK2,k2_wellord1(sK3,sK1)) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_1434]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_815,plain,
% 7.97/1.49      ( X0_43 != k8_relat_1(X0_44,X1_43)
% 7.97/1.49      | X0_43 = k8_relat_1(X0_44,k7_relat_1(X2_43,X0_44))
% 7.97/1.49      | k8_relat_1(X0_44,k7_relat_1(X2_43,X0_44)) != k8_relat_1(X0_44,X1_43) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_726]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1559,plain,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k8_relat_1(X0_44,k2_wellord1(sK3,sK1))
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44))
% 7.97/1.49      | k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) != k8_relat_1(X0_44,k2_wellord1(sK3,sK1)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_815]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_5230,plain,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k8_relat_1(sK2,k2_wellord1(sK3,sK1))
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X0_44),sK2))
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X0_44),sK2)) != k8_relat_1(sK2,k2_wellord1(sK3,sK1)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_1559]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_5235,plain,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k8_relat_1(sK2,k2_wellord1(sK3,sK1))
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2))
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) != k8_relat_1(sK2,k2_wellord1(sK3,sK1)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_5230]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_541,plain,
% 7.97/1.49      ( k2_wellord1(X0_43,X0_44) != X1_43
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X1_43
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(X0_43,X0_44) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3244,plain,
% 7.97/1.49      ( k2_wellord1(X0_43,X0_44) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2))
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(X0_43,X0_44)
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,X1_44),sK2)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_541]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_3245,plain,
% 7.97/1.49      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(sK3,sK1)
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2))
% 7.97/1.49      | k2_wellord1(sK3,sK1) != k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_3244]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_10,plain,
% 7.97/1.49      ( ~ v1_relat_1(X0)
% 7.97/1.49      | k8_relat_1(X1,k7_relat_1(X0,X1)) = k2_wellord1(X0,X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_184,plain,
% 7.97/1.49      ( ~ v1_relat_1(X0_43)
% 7.97/1.49      | k8_relat_1(X0_44,k7_relat_1(X0_43,X0_44)) = k2_wellord1(X0_43,X0_44) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_1394,plain,
% 7.97/1.49      ( ~ v1_relat_1(k2_wellord1(sK3,sK1))
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) = k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_184]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_580,plain,
% 7.97/1.49      ( X0_43 != X1_43
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X1_43
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = X0_43 ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_638,plain,
% 7.97/1.49      ( X0_43 != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = X0_43
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_580]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_959,plain,
% 7.97/1.49      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(k2_wellord1(sK3,sK1),sK2)
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2))
% 7.97/1.49      | k8_relat_1(sK2,k7_relat_1(k2_wellord1(sK3,sK1),sK2)) != k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_638]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_13,plain,
% 7.97/1.49      ( ~ v1_relat_1(X0)
% 7.97/1.49      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_181,plain,
% 7.97/1.49      ( ~ v1_relat_1(X0_43)
% 7.97/1.49      | k2_wellord1(k2_wellord1(X0_43,X0_44),X1_44) = k2_wellord1(k2_wellord1(X0_43,X1_44),X0_44) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_630,plain,
% 7.97/1.49      ( ~ v1_relat_1(sK3)
% 7.97/1.49      | k2_wellord1(k2_wellord1(sK3,sK2),sK1) = k2_wellord1(k2_wellord1(sK3,sK1),sK2) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_181]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_520,plain,
% 7.97/1.49      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != X0_43
% 7.97/1.49      | k2_wellord1(sK3,sK1) != X0_43
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_200]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_525,plain,
% 7.97/1.49      ( k2_wellord1(k2_wellord1(sK3,sK2),sK1) != k2_wellord1(sK3,sK1)
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1)
% 7.97/1.49      | k2_wellord1(sK3,sK1) != k2_wellord1(sK3,sK1) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_520]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_14,negated_conjecture,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 7.97/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_180,negated_conjecture,
% 7.97/1.49      ( k2_wellord1(sK3,sK1) != k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
% 7.97/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_239,plain,
% 7.97/1.49      ( v1_relat_1(X0_43) != iProver_top
% 7.97/1.49      | v1_relat_1(k2_wellord1(X0_43,X0_44)) = iProver_top ),
% 7.97/1.49      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_241,plain,
% 7.97/1.49      ( v1_relat_1(k2_wellord1(sK3,sK1)) = iProver_top
% 7.97/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_239]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_240,plain,
% 7.97/1.49      ( v1_relat_1(k2_wellord1(sK3,sK1)) | ~ v1_relat_1(sK3) ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_185]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_197,plain,( X0_44 = X0_44 ),theory(equality) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_221,plain,
% 7.97/1.49      ( sK1 = sK1 ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_197]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_196,plain,( X0_43 = X0_43 ),theory(equality) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_220,plain,
% 7.97/1.49      ( sK3 = sK3 ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_196]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_210,plain,
% 7.97/1.49      ( X0_44 != X1_44
% 7.97/1.49      | X0_43 != X1_43
% 7.97/1.49      | k2_wellord1(X0_43,X0_44) = k2_wellord1(X1_43,X1_44) ),
% 7.97/1.49      theory(equality) ).
% 7.97/1.49  
% 7.97/1.49  cnf(c_218,plain,
% 7.97/1.49      ( sK1 != sK1
% 7.97/1.49      | k2_wellord1(sK3,sK1) = k2_wellord1(sK3,sK1)
% 7.97/1.49      | sK3 != sK3 ),
% 7.97/1.49      inference(instantiation,[status(thm)],[c_210]) ).
% 7.97/1.49  
% 7.97/1.49  cnf(contradiction,plain,
% 7.97/1.49      ( $false ),
% 7.97/1.49      inference(minisat,
% 7.97/1.49                [status(thm)],
% 7.97/1.49                [c_29001,c_27231,c_26536,c_24155,c_23852,c_14611,c_7378,
% 7.97/1.49                 c_5235,c_3245,c_1394,c_959,c_630,c_525,c_180,c_241,
% 7.97/1.49                 c_240,c_221,c_220,c_218,c_17,c_16]) ).
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.97/1.49  
% 7.97/1.49  ------                               Statistics
% 7.97/1.49  
% 7.97/1.49  ------ General
% 7.97/1.49  
% 7.97/1.49  abstr_ref_over_cycles:                  0
% 7.97/1.49  abstr_ref_under_cycles:                 0
% 7.97/1.49  gc_basic_clause_elim:                   0
% 7.97/1.49  forced_gc_time:                         0
% 7.97/1.49  parsing_time:                           0.007
% 7.97/1.49  unif_index_cands_time:                  0.
% 7.97/1.49  unif_index_add_time:                    0.
% 7.97/1.49  orderings_time:                         0.
% 7.97/1.49  out_proof_time:                         0.012
% 7.97/1.49  total_time:                             0.963
% 7.97/1.49  num_of_symbols:                         47
% 7.97/1.49  num_of_terms:                           28049
% 7.97/1.49  
% 7.97/1.49  ------ Preprocessing
% 7.97/1.49  
% 7.97/1.49  num_of_splits:                          0
% 7.97/1.49  num_of_split_atoms:                     0
% 7.97/1.49  num_of_reused_defs:                     0
% 7.97/1.49  num_eq_ax_congr_red:                    14
% 7.97/1.49  num_of_sem_filtered_clauses:            1
% 7.97/1.49  num_of_subtypes:                        4
% 7.97/1.49  monotx_restored_types:                  0
% 7.97/1.49  sat_num_of_epr_types:                   0
% 7.97/1.49  sat_num_of_non_cyclic_types:            0
% 7.97/1.49  sat_guarded_non_collapsed_types:        1
% 7.97/1.49  num_pure_diseq_elim:                    0
% 7.97/1.49  simp_replaced_by:                       0
% 7.97/1.49  res_preprocessed:                       82
% 7.97/1.49  prep_upred:                             0
% 7.97/1.49  prep_unflattend:                        0
% 7.97/1.49  smt_new_axioms:                         0
% 7.97/1.49  pred_elim_cands:                        3
% 7.97/1.49  pred_elim:                              0
% 7.97/1.49  pred_elim_cl:                           0
% 7.97/1.49  pred_elim_cycles:                       1
% 7.97/1.49  merged_defs:                            0
% 7.97/1.49  merged_defs_ncl:                        0
% 7.97/1.49  bin_hyper_res:                          0
% 7.97/1.49  prep_cycles:                            3
% 7.97/1.49  pred_elim_time:                         0.
% 7.97/1.49  splitting_time:                         0.
% 7.97/1.49  sem_filter_time:                        0.
% 7.97/1.49  monotx_time:                            0.
% 7.97/1.49  subtype_inf_time:                       0.
% 7.97/1.49  
% 7.97/1.49  ------ Problem properties
% 7.97/1.49  
% 7.97/1.49  clauses:                                17
% 7.97/1.49  conjectures:                            3
% 7.97/1.49  epr:                                    4
% 7.97/1.49  horn:                                   16
% 7.97/1.49  ground:                                 3
% 7.97/1.49  unary:                                  4
% 7.97/1.49  binary:                                 7
% 7.97/1.49  lits:                                   36
% 7.97/1.49  lits_eq:                                7
% 7.97/1.49  fd_pure:                                0
% 7.97/1.49  fd_pseudo:                              0
% 7.97/1.49  fd_cond:                                0
% 7.97/1.49  fd_pseudo_cond:                         0
% 7.97/1.49  ac_symbols:                             0
% 7.97/1.49  
% 7.97/1.49  ------ Propositional Solver
% 7.97/1.49  
% 7.97/1.49  prop_solver_calls:                      30
% 7.97/1.49  prop_fast_solver_calls:                 808
% 7.97/1.49  smt_solver_calls:                       0
% 7.97/1.49  smt_fast_solver_calls:                  0
% 7.97/1.49  prop_num_of_clauses:                    8878
% 7.97/1.49  prop_preprocess_simplified:             12598
% 7.97/1.49  prop_fo_subsumed:                       15
% 7.97/1.49  prop_solver_time:                       0.
% 7.97/1.49  smt_solver_time:                        0.
% 7.97/1.49  smt_fast_solver_time:                   0.
% 7.97/1.49  prop_fast_solver_time:                  0.
% 7.97/1.49  prop_unsat_core_time:                   0.001
% 7.97/1.49  
% 7.97/1.49  ------ QBF
% 7.97/1.49  
% 7.97/1.49  qbf_q_res:                              0
% 7.97/1.49  qbf_num_tautologies:                    0
% 7.97/1.49  qbf_prep_cycles:                        0
% 7.97/1.49  
% 7.97/1.49  ------ BMC1
% 7.97/1.49  
% 7.97/1.49  bmc1_current_bound:                     -1
% 7.97/1.49  bmc1_last_solved_bound:                 -1
% 7.97/1.49  bmc1_unsat_core_size:                   -1
% 7.97/1.49  bmc1_unsat_core_parents_size:           -1
% 7.97/1.49  bmc1_merge_next_fun:                    0
% 7.97/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.97/1.49  
% 7.97/1.49  ------ Instantiation
% 7.97/1.49  
% 7.97/1.49  inst_num_of_clauses:                    2531
% 7.97/1.49  inst_num_in_passive:                    645
% 7.97/1.49  inst_num_in_active:                     817
% 7.97/1.49  inst_num_in_unprocessed:                1068
% 7.97/1.49  inst_num_of_loops:                      1065
% 7.97/1.49  inst_num_of_learning_restarts:          0
% 7.97/1.49  inst_num_moves_active_passive:          243
% 7.97/1.49  inst_lit_activity:                      0
% 7.97/1.49  inst_lit_activity_moves:                0
% 7.97/1.49  inst_num_tautologies:                   0
% 7.97/1.49  inst_num_prop_implied:                  0
% 7.97/1.49  inst_num_existing_simplified:           0
% 7.97/1.49  inst_num_eq_res_simplified:             0
% 7.97/1.49  inst_num_child_elim:                    0
% 7.97/1.49  inst_num_of_dismatching_blockings:      3778
% 7.97/1.49  inst_num_of_non_proper_insts:           4899
% 7.97/1.49  inst_num_of_duplicates:                 0
% 7.97/1.49  inst_inst_num_from_inst_to_res:         0
% 7.97/1.49  inst_dismatching_checking_time:         0.
% 7.97/1.49  
% 7.97/1.49  ------ Resolution
% 7.97/1.49  
% 7.97/1.49  res_num_of_clauses:                     0
% 7.97/1.49  res_num_in_passive:                     0
% 7.97/1.49  res_num_in_active:                      0
% 7.97/1.49  res_num_of_loops:                       85
% 7.97/1.49  res_forward_subset_subsumed:            390
% 7.97/1.49  res_backward_subset_subsumed:           0
% 7.97/1.49  res_forward_subsumed:                   0
% 7.97/1.49  res_backward_subsumed:                  0
% 7.97/1.49  res_forward_subsumption_resolution:     0
% 7.97/1.49  res_backward_subsumption_resolution:    0
% 7.97/1.49  res_clause_to_clause_subsumption:       13921
% 7.97/1.49  res_orphan_elimination:                 0
% 7.97/1.49  res_tautology_del:                      665
% 7.97/1.49  res_num_eq_res_simplified:              0
% 7.97/1.49  res_num_sel_changes:                    0
% 7.97/1.49  res_moves_from_active_to_pass:          0
% 7.97/1.49  
% 7.97/1.49  ------ Superposition
% 7.97/1.49  
% 7.97/1.49  sup_time_total:                         0.
% 7.97/1.49  sup_time_generating:                    0.
% 7.97/1.49  sup_time_sim_full:                      0.
% 7.97/1.49  sup_time_sim_immed:                     0.
% 7.97/1.49  
% 7.97/1.49  sup_num_of_clauses:                     1792
% 7.97/1.49  sup_num_in_active:                      203
% 7.97/1.49  sup_num_in_passive:                     1589
% 7.97/1.49  sup_num_of_loops:                       212
% 7.97/1.49  sup_fw_superposition:                   2909
% 7.97/1.49  sup_bw_superposition:                   2710
% 7.97/1.49  sup_immediate_simplified:               1709
% 7.97/1.49  sup_given_eliminated:                   0
% 7.97/1.49  comparisons_done:                       0
% 7.97/1.49  comparisons_avoided:                    0
% 7.97/1.49  
% 7.97/1.49  ------ Simplifications
% 7.97/1.49  
% 7.97/1.49  
% 7.97/1.49  sim_fw_subset_subsumed:                 9
% 7.97/1.49  sim_bw_subset_subsumed:                 9
% 7.97/1.49  sim_fw_subsumed:                        285
% 7.97/1.49  sim_bw_subsumed:                        5
% 7.97/1.49  sim_fw_subsumption_res:                 0
% 7.97/1.49  sim_bw_subsumption_res:                 0
% 7.97/1.49  sim_tautology_del:                      60
% 7.97/1.49  sim_eq_tautology_del:                   104
% 7.97/1.49  sim_eq_res_simp:                        0
% 7.97/1.49  sim_fw_demodulated:                     610
% 7.97/1.49  sim_bw_demodulated:                     7
% 7.97/1.49  sim_light_normalised:                   936
% 7.97/1.49  sim_joinable_taut:                      0
% 7.97/1.49  sim_joinable_simp:                      0
% 7.97/1.49  sim_ac_normalised:                      0
% 7.97/1.49  sim_smt_subsumption:                    0
% 7.97/1.49  
%------------------------------------------------------------------------------
