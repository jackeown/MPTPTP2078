%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:20 EST 2020

% Result     : Theorem 11.78s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 404 expanded)
%              Number of clauses        :   71 ( 130 expanded)
%              Number of leaves         :   24 ( 101 expanded)
%              Depth                    :   19
%              Number of atoms          :  294 ( 746 expanded)
%              Number of equality atoms :  165 ( 418 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36])).

fof(f64,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f69])).

fof(f71,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f19,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f61,f71])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_242,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1306,plain,
    ( X0 != X1
    | k10_relat_1(sK0,sK2) != X1
    | k10_relat_1(sK0,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_1686,plain,
    ( X0 != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = X0
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_3405,plain,
    ( k10_relat_1(X0,X1) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(X0,X1)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1686])).

cnf(c_14176,plain,
    ( k10_relat_1(X0,sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(X0,sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_3405])).

cnf(c_47818,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_14176])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_512,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_516,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_519,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1448,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_516,c_519])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1456,plain,
    ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1448,c_8,c_9])).

cnf(c_13,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_514,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1769,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) = iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_514])).

cnf(c_33,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11683,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1769,c_33,c_36])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_521,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11691,plain,
    ( k2_xboole_0(k9_relat_1(k6_relat_1(X0),X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_11683,c_521])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_522,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11718,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11691,c_522])).

cnf(c_20039,plain,
    ( k2_xboole_0(k9_relat_1(k6_relat_1(X0),X0),X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11718,c_521])).

cnf(c_25696,plain,
    ( k2_xboole_0(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_512,c_20039])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_523,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1969,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_523,c_522])).

cnf(c_25987,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_25696,c_1969])).

cnf(c_14,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_513,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_28030,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) = iProver_top
    | r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) != iProver_top
    | v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top
    | v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25987,c_513])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_518,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3419,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_516,c_518])).

cnf(c_3432,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3419,c_9])).

cnf(c_3445,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_516,c_3432])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_510,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_515,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3289,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_510,c_515])).

cnf(c_15,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_919,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_15,c_9])).

cnf(c_3754,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k6_relat_1(X1))) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(superposition,[status(thm)],[c_3289,c_919])).

cnf(c_7983,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(superposition,[status(thm)],[c_3445,c_3754])).

cnf(c_28035,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = iProver_top
    | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) != iProver_top
    | v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top
    | v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28030,c_9,c_7983])).

cnf(c_1616,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1619,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1616])).

cnf(c_28737,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = iProver_top
    | v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top
    | v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28035,c_1619])).

cnf(c_517,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_28744,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28737,c_516,c_517])).

cnf(c_5,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_520,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_524,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2241,plain,
    ( k10_relat_1(X0,X1) = k1_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),k10_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_520,c_524])).

cnf(c_15922,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k1_relat_1(k6_relat_1(k10_relat_1(sK0,X0)))
    | r1_tarski(k1_relat_1(k6_relat_1(k10_relat_1(sK0,X0))),k10_relat_1(k7_relat_1(sK0,X1),X0)) != iProver_top
    | v1_relat_1(k6_relat_1(k10_relat_1(sK0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7983,c_2241])).

cnf(c_15958,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(sK0,X1)
    | r1_tarski(k10_relat_1(sK0,X1),k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top
    | v1_relat_1(k6_relat_1(k10_relat_1(sK0,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15922,c_9,c_7983])).

cnf(c_16291,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(sK0,X1)
    | r1_tarski(k10_relat_1(sK0,X1),k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15958,c_516])).

cnf(c_28750,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_28744,c_16291])).

cnf(c_241,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1687,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_16,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47818,c_28750,c_1687,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.78/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/2.01  
% 11.78/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.78/2.01  
% 11.78/2.01  ------  iProver source info
% 11.78/2.01  
% 11.78/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.78/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.78/2.01  git: non_committed_changes: false
% 11.78/2.01  git: last_make_outside_of_git: false
% 11.78/2.01  
% 11.78/2.01  ------ 
% 11.78/2.01  ------ Parsing...
% 11.78/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.78/2.01  
% 11.78/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.78/2.01  
% 11.78/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.78/2.01  
% 11.78/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/2.01  ------ Proving...
% 11.78/2.01  ------ Problem Properties 
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  clauses                                 19
% 11.78/2.01  conjectures                             4
% 11.78/2.01  EPR                                     4
% 11.78/2.01  Horn                                    19
% 11.78/2.01  unary                                   10
% 11.78/2.01  binary                                  5
% 11.78/2.01  lits                                    34
% 11.78/2.01  lits eq                                 9
% 11.78/2.01  fd_pure                                 0
% 11.78/2.01  fd_pseudo                               0
% 11.78/2.01  fd_cond                                 0
% 11.78/2.01  fd_pseudo_cond                          1
% 11.78/2.01  AC symbols                              0
% 11.78/2.01  
% 11.78/2.01  ------ Input Options Time Limit: Unbounded
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  ------ 
% 11.78/2.01  Current options:
% 11.78/2.01  ------ 
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  ------ Proving...
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  % SZS status Theorem for theBenchmark.p
% 11.78/2.01  
% 11.78/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.78/2.01  
% 11.78/2.01  fof(f20,conjecture,(
% 11.78/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f21,negated_conjecture,(
% 11.78/2.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 11.78/2.01    inference(negated_conjecture,[],[f20])).
% 11.78/2.01  
% 11.78/2.01  fof(f32,plain,(
% 11.78/2.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 11.78/2.01    inference(ennf_transformation,[],[f21])).
% 11.78/2.01  
% 11.78/2.01  fof(f33,plain,(
% 11.78/2.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.78/2.01    inference(flattening,[],[f32])).
% 11.78/2.01  
% 11.78/2.01  fof(f37,plain,(
% 11.78/2.01    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 11.78/2.01    introduced(choice_axiom,[])).
% 11.78/2.01  
% 11.78/2.01  fof(f36,plain,(
% 11.78/2.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 11.78/2.01    introduced(choice_axiom,[])).
% 11.78/2.01  
% 11.78/2.01  fof(f38,plain,(
% 11.78/2.01    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 11.78/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36])).
% 11.78/2.01  
% 11.78/2.01  fof(f64,plain,(
% 11.78/2.01    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 11.78/2.01    inference(cnf_transformation,[],[f38])).
% 11.78/2.01  
% 11.78/2.01  fof(f15,axiom,(
% 11.78/2.01    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f56,plain,(
% 11.78/2.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.78/2.01    inference(cnf_transformation,[],[f15])).
% 11.78/2.01  
% 11.78/2.01  fof(f12,axiom,(
% 11.78/2.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f25,plain,(
% 11.78/2.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 11.78/2.01    inference(ennf_transformation,[],[f12])).
% 11.78/2.01  
% 11.78/2.01  fof(f52,plain,(
% 11.78/2.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f25])).
% 11.78/2.01  
% 11.78/2.01  fof(f14,axiom,(
% 11.78/2.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f55,plain,(
% 11.78/2.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.78/2.01    inference(cnf_transformation,[],[f14])).
% 11.78/2.01  
% 11.78/2.01  fof(f54,plain,(
% 11.78/2.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.78/2.01    inference(cnf_transformation,[],[f14])).
% 11.78/2.01  
% 11.78/2.01  fof(f17,axiom,(
% 11.78/2.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f28,plain,(
% 11.78/2.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.78/2.01    inference(ennf_transformation,[],[f17])).
% 11.78/2.01  
% 11.78/2.01  fof(f29,plain,(
% 11.78/2.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.78/2.01    inference(flattening,[],[f28])).
% 11.78/2.01  
% 11.78/2.01  fof(f59,plain,(
% 11.78/2.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f29])).
% 11.78/2.01  
% 11.78/2.01  fof(f57,plain,(
% 11.78/2.01    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 11.78/2.01    inference(cnf_transformation,[],[f15])).
% 11.78/2.01  
% 11.78/2.01  fof(f3,axiom,(
% 11.78/2.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f23,plain,(
% 11.78/2.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.78/2.01    inference(ennf_transformation,[],[f3])).
% 11.78/2.01  
% 11.78/2.01  fof(f43,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f23])).
% 11.78/2.01  
% 11.78/2.01  fof(f2,axiom,(
% 11.78/2.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f22,plain,(
% 11.78/2.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.78/2.01    inference(ennf_transformation,[],[f2])).
% 11.78/2.01  
% 11.78/2.01  fof(f42,plain,(
% 11.78/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f22])).
% 11.78/2.01  
% 11.78/2.01  fof(f1,axiom,(
% 11.78/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f34,plain,(
% 11.78/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.78/2.01    inference(nnf_transformation,[],[f1])).
% 11.78/2.01  
% 11.78/2.01  fof(f35,plain,(
% 11.78/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.78/2.01    inference(flattening,[],[f34])).
% 11.78/2.01  
% 11.78/2.01  fof(f40,plain,(
% 11.78/2.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.78/2.01    inference(cnf_transformation,[],[f35])).
% 11.78/2.01  
% 11.78/2.01  fof(f74,plain,(
% 11.78/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.78/2.01    inference(equality_resolution,[],[f40])).
% 11.78/2.01  
% 11.78/2.01  fof(f18,axiom,(
% 11.78/2.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f30,plain,(
% 11.78/2.01    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.78/2.01    inference(ennf_transformation,[],[f18])).
% 11.78/2.01  
% 11.78/2.01  fof(f31,plain,(
% 11.78/2.01    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.78/2.01    inference(flattening,[],[f30])).
% 11.78/2.01  
% 11.78/2.01  fof(f60,plain,(
% 11.78/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f31])).
% 11.78/2.01  
% 11.78/2.01  fof(f13,axiom,(
% 11.78/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f26,plain,(
% 11.78/2.01    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.78/2.01    inference(ennf_transformation,[],[f13])).
% 11.78/2.01  
% 11.78/2.01  fof(f53,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f26])).
% 11.78/2.01  
% 11.78/2.01  fof(f62,plain,(
% 11.78/2.01    v1_relat_1(sK0)),
% 11.78/2.01    inference(cnf_transformation,[],[f38])).
% 11.78/2.01  
% 11.78/2.01  fof(f16,axiom,(
% 11.78/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f27,plain,(
% 11.78/2.01    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 11.78/2.01    inference(ennf_transformation,[],[f16])).
% 11.78/2.01  
% 11.78/2.01  fof(f58,plain,(
% 11.78/2.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f27])).
% 11.78/2.01  
% 11.78/2.01  fof(f10,axiom,(
% 11.78/2.01    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f50,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f10])).
% 11.78/2.01  
% 11.78/2.01  fof(f4,axiom,(
% 11.78/2.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f44,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f4])).
% 11.78/2.01  
% 11.78/2.01  fof(f5,axiom,(
% 11.78/2.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f45,plain,(
% 11.78/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f5])).
% 11.78/2.01  
% 11.78/2.01  fof(f6,axiom,(
% 11.78/2.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f46,plain,(
% 11.78/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f6])).
% 11.78/2.01  
% 11.78/2.01  fof(f7,axiom,(
% 11.78/2.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f47,plain,(
% 11.78/2.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f7])).
% 11.78/2.01  
% 11.78/2.01  fof(f8,axiom,(
% 11.78/2.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f48,plain,(
% 11.78/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f8])).
% 11.78/2.01  
% 11.78/2.01  fof(f9,axiom,(
% 11.78/2.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f49,plain,(
% 11.78/2.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f9])).
% 11.78/2.01  
% 11.78/2.01  fof(f66,plain,(
% 11.78/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.78/2.01    inference(definition_unfolding,[],[f48,f49])).
% 11.78/2.01  
% 11.78/2.01  fof(f67,plain,(
% 11.78/2.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.78/2.01    inference(definition_unfolding,[],[f47,f66])).
% 11.78/2.01  
% 11.78/2.01  fof(f68,plain,(
% 11.78/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.78/2.01    inference(definition_unfolding,[],[f46,f67])).
% 11.78/2.01  
% 11.78/2.01  fof(f69,plain,(
% 11.78/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.78/2.01    inference(definition_unfolding,[],[f45,f68])).
% 11.78/2.01  
% 11.78/2.01  fof(f70,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.78/2.01    inference(definition_unfolding,[],[f44,f69])).
% 11.78/2.01  
% 11.78/2.01  fof(f71,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.78/2.01    inference(definition_unfolding,[],[f50,f70])).
% 11.78/2.01  
% 11.78/2.01  fof(f72,plain,(
% 11.78/2.01    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 11.78/2.01    inference(definition_unfolding,[],[f58,f71])).
% 11.78/2.01  
% 11.78/2.01  fof(f19,axiom,(
% 11.78/2.01    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f61,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 11.78/2.01    inference(cnf_transformation,[],[f19])).
% 11.78/2.01  
% 11.78/2.01  fof(f73,plain,(
% 11.78/2.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.78/2.01    inference(definition_unfolding,[],[f61,f71])).
% 11.78/2.01  
% 11.78/2.01  fof(f11,axiom,(
% 11.78/2.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 11.78/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.01  
% 11.78/2.01  fof(f24,plain,(
% 11.78/2.01    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.78/2.01    inference(ennf_transformation,[],[f11])).
% 11.78/2.01  
% 11.78/2.01  fof(f51,plain,(
% 11.78/2.01    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f24])).
% 11.78/2.01  
% 11.78/2.01  fof(f41,plain,(
% 11.78/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.78/2.01    inference(cnf_transformation,[],[f35])).
% 11.78/2.01  
% 11.78/2.01  fof(f65,plain,(
% 11.78/2.01    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 11.78/2.01    inference(cnf_transformation,[],[f38])).
% 11.78/2.01  
% 11.78/2.01  cnf(c_242,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1306,plain,
% 11.78/2.01      ( X0 != X1
% 11.78/2.01      | k10_relat_1(sK0,sK2) != X1
% 11.78/2.01      | k10_relat_1(sK0,sK2) = X0 ),
% 11.78/2.01      inference(instantiation,[status(thm)],[c_242]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1686,plain,
% 11.78/2.01      ( X0 != k10_relat_1(sK0,sK2)
% 11.78/2.01      | k10_relat_1(sK0,sK2) = X0
% 11.78/2.01      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 11.78/2.01      inference(instantiation,[status(thm)],[c_1306]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_3405,plain,
% 11.78/2.01      ( k10_relat_1(X0,X1) != k10_relat_1(sK0,sK2)
% 11.78/2.01      | k10_relat_1(sK0,sK2) = k10_relat_1(X0,X1)
% 11.78/2.01      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 11.78/2.01      inference(instantiation,[status(thm)],[c_1686]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_14176,plain,
% 11.78/2.01      ( k10_relat_1(X0,sK2) != k10_relat_1(sK0,sK2)
% 11.78/2.01      | k10_relat_1(sK0,sK2) = k10_relat_1(X0,sK2)
% 11.78/2.01      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 11.78/2.01      inference(instantiation,[status(thm)],[c_3405]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_47818,plain,
% 11.78/2.01      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
% 11.78/2.01      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
% 11.78/2.01      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 11.78/2.01      inference(instantiation,[status(thm)],[c_14176]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_17,negated_conjecture,
% 11.78/2.01      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 11.78/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_512,plain,
% 11.78/2.01      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_11,plain,
% 11.78/2.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 11.78/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_516,plain,
% 11.78/2.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_6,plain,
% 11.78/2.01      ( ~ v1_relat_1(X0)
% 11.78/2.01      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 11.78/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_519,plain,
% 11.78/2.01      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 11.78/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1448,plain,
% 11.78/2.01      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_516,c_519]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_8,plain,
% 11.78/2.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 11.78/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_9,plain,
% 11.78/2.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 11.78/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1456,plain,
% 11.78/2.01      ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
% 11.78/2.01      inference(light_normalisation,[status(thm)],[c_1448,c_8,c_9]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_13,plain,
% 11.78/2.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 11.78/2.01      | ~ v1_funct_1(X0)
% 11.78/2.01      | ~ v1_relat_1(X0) ),
% 11.78/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_514,plain,
% 11.78/2.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 11.78/2.01      | v1_funct_1(X0) != iProver_top
% 11.78/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1769,plain,
% 11.78/2.01      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) = iProver_top
% 11.78/2.01      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 11.78/2.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_1456,c_514]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_33,plain,
% 11.78/2.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_10,plain,
% 11.78/2.01      ( v1_funct_1(k6_relat_1(X0)) ),
% 11.78/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_36,plain,
% 11.78/2.01      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_11683,plain,
% 11.78/2.01      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) = iProver_top ),
% 11.78/2.01      inference(global_propositional_subsumption,
% 11.78/2.01                [status(thm)],
% 11.78/2.01                [c_1769,c_33,c_36]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_4,plain,
% 11.78/2.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.78/2.01      inference(cnf_transformation,[],[f43]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_521,plain,
% 11.78/2.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_11691,plain,
% 11.78/2.01      ( k2_xboole_0(k9_relat_1(k6_relat_1(X0),X0),X0) = X0 ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_11683,c_521]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_3,plain,
% 11.78/2.01      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.78/2.01      inference(cnf_transformation,[],[f42]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_522,plain,
% 11.78/2.01      ( r1_tarski(X0,X1) = iProver_top
% 11.78/2.01      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_11718,plain,
% 11.78/2.01      ( r1_tarski(X0,X1) != iProver_top
% 11.78/2.01      | r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X1) = iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_11691,c_522]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_20039,plain,
% 11.78/2.01      ( k2_xboole_0(k9_relat_1(k6_relat_1(X0),X0),X1) = X1
% 11.78/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_11718,c_521]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_25696,plain,
% 11.78/2.01      ( k2_xboole_0(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) = sK1 ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_512,c_20039]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1,plain,
% 11.78/2.01      ( r1_tarski(X0,X0) ),
% 11.78/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_523,plain,
% 11.78/2.01      ( r1_tarski(X0,X0) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1969,plain,
% 11.78/2.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_523,c_522]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_25987,plain,
% 11.78/2.01      ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) = iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_25696,c_1969]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_14,plain,
% 11.78/2.01      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 11.78/2.01      | ~ r1_tarski(X0,k1_relat_1(X1))
% 11.78/2.01      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 11.78/2.01      | ~ v1_funct_1(X1)
% 11.78/2.01      | ~ v1_relat_1(X1) ),
% 11.78/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_513,plain,
% 11.78/2.01      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 11.78/2.01      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 11.78/2.01      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 11.78/2.01      | v1_funct_1(X1) != iProver_top
% 11.78/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_28030,plain,
% 11.78/2.01      ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) = iProver_top
% 11.78/2.01      | r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) != iProver_top
% 11.78/2.01      | v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top
% 11.78/2.01      | v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_25987,c_513]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_7,plain,
% 11.78/2.01      ( ~ v1_relat_1(X0)
% 11.78/2.01      | ~ v1_relat_1(X1)
% 11.78/2.01      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 11.78/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_518,plain,
% 11.78/2.01      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 11.78/2.01      | v1_relat_1(X0) != iProver_top
% 11.78/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_3419,plain,
% 11.78/2.01      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
% 11.78/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_516,c_518]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_3432,plain,
% 11.78/2.01      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)
% 11.78/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.78/2.01      inference(demodulation,[status(thm)],[c_3419,c_9]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_3445,plain,
% 11.78/2.01      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_516,c_3432]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_19,negated_conjecture,
% 11.78/2.01      ( v1_relat_1(sK0) ),
% 11.78/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_510,plain,
% 11.78/2.01      ( v1_relat_1(sK0) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_12,plain,
% 11.78/2.01      ( ~ v1_relat_1(X0)
% 11.78/2.01      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 11.78/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_515,plain,
% 11.78/2.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 11.78/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_3289,plain,
% 11.78/2.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_510,c_515]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_15,plain,
% 11.78/2.01      ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 11.78/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_919,plain,
% 11.78/2.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_15,c_9]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_3754,plain,
% 11.78/2.01      ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k6_relat_1(X1))) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_3289,c_919]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_7983,plain,
% 11.78/2.01      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_3445,c_3754]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_28035,plain,
% 11.78/2.01      ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = iProver_top
% 11.78/2.01      | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) != iProver_top
% 11.78/2.01      | v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top
% 11.78/2.01      | v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top ),
% 11.78/2.01      inference(demodulation,[status(thm)],[c_28030,c_9,c_7983]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1616,plain,
% 11.78/2.01      ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) ),
% 11.78/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1619,plain,
% 11.78/2.01      ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_1616]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_28737,plain,
% 11.78/2.01      ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = iProver_top
% 11.78/2.01      | v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top
% 11.78/2.01      | v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) != iProver_top ),
% 11.78/2.01      inference(global_propositional_subsumption,
% 11.78/2.01                [status(thm)],
% 11.78/2.01                [c_28035,c_1619]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_517,plain,
% 11.78/2.01      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_28744,plain,
% 11.78/2.01      ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = iProver_top ),
% 11.78/2.01      inference(forward_subsumption_resolution,
% 11.78/2.01                [status(thm)],
% 11.78/2.01                [c_28737,c_516,c_517]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_5,plain,
% 11.78/2.01      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 11.78/2.01      inference(cnf_transformation,[],[f51]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_520,plain,
% 11.78/2.01      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 11.78/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_0,plain,
% 11.78/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.78/2.01      inference(cnf_transformation,[],[f41]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_524,plain,
% 11.78/2.01      ( X0 = X1
% 11.78/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.78/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.78/2.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_2241,plain,
% 11.78/2.01      ( k10_relat_1(X0,X1) = k1_relat_1(X0)
% 11.78/2.01      | r1_tarski(k1_relat_1(X0),k10_relat_1(X0,X1)) != iProver_top
% 11.78/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_520,c_524]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_15922,plain,
% 11.78/2.01      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k1_relat_1(k6_relat_1(k10_relat_1(sK0,X0)))
% 11.78/2.01      | r1_tarski(k1_relat_1(k6_relat_1(k10_relat_1(sK0,X0))),k10_relat_1(k7_relat_1(sK0,X1),X0)) != iProver_top
% 11.78/2.01      | v1_relat_1(k6_relat_1(k10_relat_1(sK0,X0))) != iProver_top ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_7983,c_2241]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_15958,plain,
% 11.78/2.01      ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(sK0,X1)
% 11.78/2.01      | r1_tarski(k10_relat_1(sK0,X1),k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top
% 11.78/2.01      | v1_relat_1(k6_relat_1(k10_relat_1(sK0,X1))) != iProver_top ),
% 11.78/2.01      inference(demodulation,[status(thm)],[c_15922,c_9,c_7983]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_16291,plain,
% 11.78/2.01      ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(sK0,X1)
% 11.78/2.01      | r1_tarski(k10_relat_1(sK0,X1),k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top ),
% 11.78/2.01      inference(forward_subsumption_resolution,
% 11.78/2.01                [status(thm)],
% 11.78/2.01                [c_15958,c_516]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_28750,plain,
% 11.78/2.01      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 11.78/2.01      inference(superposition,[status(thm)],[c_28744,c_16291]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_241,plain,( X0 = X0 ),theory(equality) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_1687,plain,
% 11.78/2.01      ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 11.78/2.01      inference(instantiation,[status(thm)],[c_241]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(c_16,negated_conjecture,
% 11.78/2.01      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 11.78/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.78/2.01  
% 11.78/2.01  cnf(contradiction,plain,
% 11.78/2.01      ( $false ),
% 11.78/2.01      inference(minisat,[status(thm)],[c_47818,c_28750,c_1687,c_16]) ).
% 11.78/2.01  
% 11.78/2.01  
% 11.78/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.78/2.01  
% 11.78/2.01  ------                               Statistics
% 11.78/2.01  
% 11.78/2.01  ------ Selected
% 11.78/2.01  
% 11.78/2.01  total_time:                             1.394
% 11.78/2.01  
%------------------------------------------------------------------------------
