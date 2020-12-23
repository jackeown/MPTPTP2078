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
% DateTime   : Thu Dec  3 11:43:50 EST 2020

% Result     : Theorem 19.74s
% Output     : CNFRefutation 19.74s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 711 expanded)
%              Number of clauses        :   46 ( 120 expanded)
%              Number of leaves         :   28 ( 218 expanded)
%              Depth                    :   16
%              Number of atoms          :  251 ( 949 expanded)
%              Number of equality atoms :  143 ( 746 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f30])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK5(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).

fof(f65,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f54])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f71])).

fof(f73,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f77,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f77])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f45,f75])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f59,f76,f77,f77,f77])).

fof(f83,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f51,f74,f73,f57])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f34])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f60,f76,f77,f77,f77])).

fof(f21,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f29,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f22])).

fof(f70,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_521,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(sK5(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_514,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1543,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | r2_hidden(sK5(X0),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_521,c_514])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_515,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_110,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_111,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_110])).

cnf(c_190,plain,
    ( ~ r2_hidden(X0,X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X2
    | k1_xboole_0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_111])).

cnf(c_191,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_513,plain,
    ( k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_3253,plain,
    ( k6_enumset1(k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0)) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_515,c_513])).

cnf(c_7,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_0,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_576,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_7,c_0,c_5])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_619,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_617,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_758,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_617])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_782,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_758,c_3])).

cnf(c_783,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_782,c_617])).

cnf(c_1070,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_619,c_783])).

cnf(c_1085,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1070,c_3])).

cnf(c_18667,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_576,c_1085])).

cnf(c_72431,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3253,c_18667])).

cnf(c_72440,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_72431])).

cnf(c_72435,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_521,c_72431])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_519,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1061,plain,
    ( k6_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_519,c_513])).

cnf(c_29549,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1061,c_18667])).

cnf(c_345,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_752,plain,
    ( k2_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_753,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_610,plain,
    ( k1_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_611,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_6,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_46,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_45,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_72440,c_72435,c_29549,c_753,c_611,c_46,c_45,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:25:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.74/3.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.74/3.04  
% 19.74/3.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.74/3.04  
% 19.74/3.04  ------  iProver source info
% 19.74/3.04  
% 19.74/3.04  git: date: 2020-06-30 10:37:57 +0100
% 19.74/3.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.74/3.04  git: non_committed_changes: false
% 19.74/3.04  git: last_make_outside_of_git: false
% 19.74/3.04  
% 19.74/3.04  ------ 
% 19.74/3.04  
% 19.74/3.04  ------ Input Options
% 19.74/3.04  
% 19.74/3.04  --out_options                           all
% 19.74/3.04  --tptp_safe_out                         true
% 19.74/3.04  --problem_path                          ""
% 19.74/3.04  --include_path                          ""
% 19.74/3.04  --clausifier                            res/vclausify_rel
% 19.74/3.04  --clausifier_options                    --mode clausify
% 19.74/3.04  --stdin                                 false
% 19.74/3.04  --stats_out                             all
% 19.74/3.04  
% 19.74/3.04  ------ General Options
% 19.74/3.04  
% 19.74/3.04  --fof                                   false
% 19.74/3.04  --time_out_real                         305.
% 19.74/3.04  --time_out_virtual                      -1.
% 19.74/3.04  --symbol_type_check                     false
% 19.74/3.04  --clausify_out                          false
% 19.74/3.04  --sig_cnt_out                           false
% 19.74/3.04  --trig_cnt_out                          false
% 19.74/3.04  --trig_cnt_out_tolerance                1.
% 19.74/3.04  --trig_cnt_out_sk_spl                   false
% 19.74/3.04  --abstr_cl_out                          false
% 19.74/3.04  
% 19.74/3.04  ------ Global Options
% 19.74/3.04  
% 19.74/3.04  --schedule                              default
% 19.74/3.04  --add_important_lit                     false
% 19.74/3.04  --prop_solver_per_cl                    1000
% 19.74/3.04  --min_unsat_core                        false
% 19.74/3.04  --soft_assumptions                      false
% 19.74/3.04  --soft_lemma_size                       3
% 19.74/3.04  --prop_impl_unit_size                   0
% 19.74/3.04  --prop_impl_unit                        []
% 19.74/3.04  --share_sel_clauses                     true
% 19.74/3.04  --reset_solvers                         false
% 19.74/3.04  --bc_imp_inh                            [conj_cone]
% 19.74/3.04  --conj_cone_tolerance                   3.
% 19.74/3.04  --extra_neg_conj                        none
% 19.74/3.04  --large_theory_mode                     true
% 19.74/3.04  --prolific_symb_bound                   200
% 19.74/3.04  --lt_threshold                          2000
% 19.74/3.04  --clause_weak_htbl                      true
% 19.74/3.04  --gc_record_bc_elim                     false
% 19.74/3.04  
% 19.74/3.04  ------ Preprocessing Options
% 19.74/3.04  
% 19.74/3.04  --preprocessing_flag                    true
% 19.74/3.04  --time_out_prep_mult                    0.1
% 19.74/3.04  --splitting_mode                        input
% 19.74/3.04  --splitting_grd                         true
% 19.74/3.04  --splitting_cvd                         false
% 19.74/3.04  --splitting_cvd_svl                     false
% 19.74/3.04  --splitting_nvd                         32
% 19.74/3.04  --sub_typing                            true
% 19.74/3.04  --prep_gs_sim                           true
% 19.74/3.04  --prep_unflatten                        true
% 19.74/3.04  --prep_res_sim                          true
% 19.74/3.04  --prep_upred                            true
% 19.74/3.04  --prep_sem_filter                       exhaustive
% 19.74/3.04  --prep_sem_filter_out                   false
% 19.74/3.04  --pred_elim                             true
% 19.74/3.04  --res_sim_input                         true
% 19.74/3.04  --eq_ax_congr_red                       true
% 19.74/3.04  --pure_diseq_elim                       true
% 19.74/3.04  --brand_transform                       false
% 19.74/3.04  --non_eq_to_eq                          false
% 19.74/3.04  --prep_def_merge                        true
% 19.74/3.04  --prep_def_merge_prop_impl              false
% 19.74/3.04  --prep_def_merge_mbd                    true
% 19.74/3.04  --prep_def_merge_tr_red                 false
% 19.74/3.04  --prep_def_merge_tr_cl                  false
% 19.74/3.04  --smt_preprocessing                     true
% 19.74/3.04  --smt_ac_axioms                         fast
% 19.74/3.04  --preprocessed_out                      false
% 19.74/3.04  --preprocessed_stats                    false
% 19.74/3.04  
% 19.74/3.04  ------ Abstraction refinement Options
% 19.74/3.04  
% 19.74/3.04  --abstr_ref                             []
% 19.74/3.04  --abstr_ref_prep                        false
% 19.74/3.04  --abstr_ref_until_sat                   false
% 19.74/3.04  --abstr_ref_sig_restrict                funpre
% 19.74/3.04  --abstr_ref_af_restrict_to_split_sk     false
% 19.74/3.04  --abstr_ref_under                       []
% 19.74/3.04  
% 19.74/3.04  ------ SAT Options
% 19.74/3.04  
% 19.74/3.04  --sat_mode                              false
% 19.74/3.04  --sat_fm_restart_options                ""
% 19.74/3.04  --sat_gr_def                            false
% 19.74/3.04  --sat_epr_types                         true
% 19.74/3.04  --sat_non_cyclic_types                  false
% 19.74/3.04  --sat_finite_models                     false
% 19.74/3.04  --sat_fm_lemmas                         false
% 19.74/3.04  --sat_fm_prep                           false
% 19.74/3.04  --sat_fm_uc_incr                        true
% 19.74/3.04  --sat_out_model                         small
% 19.74/3.04  --sat_out_clauses                       false
% 19.74/3.04  
% 19.74/3.04  ------ QBF Options
% 19.74/3.04  
% 19.74/3.04  --qbf_mode                              false
% 19.74/3.04  --qbf_elim_univ                         false
% 19.74/3.04  --qbf_dom_inst                          none
% 19.74/3.04  --qbf_dom_pre_inst                      false
% 19.74/3.04  --qbf_sk_in                             false
% 19.74/3.04  --qbf_pred_elim                         true
% 19.74/3.04  --qbf_split                             512
% 19.74/3.04  
% 19.74/3.04  ------ BMC1 Options
% 19.74/3.04  
% 19.74/3.04  --bmc1_incremental                      false
% 19.74/3.04  --bmc1_axioms                           reachable_all
% 19.74/3.04  --bmc1_min_bound                        0
% 19.74/3.04  --bmc1_max_bound                        -1
% 19.74/3.04  --bmc1_max_bound_default                -1
% 19.74/3.04  --bmc1_symbol_reachability              true
% 19.74/3.04  --bmc1_property_lemmas                  false
% 19.74/3.04  --bmc1_k_induction                      false
% 19.74/3.04  --bmc1_non_equiv_states                 false
% 19.74/3.04  --bmc1_deadlock                         false
% 19.74/3.04  --bmc1_ucm                              false
% 19.74/3.04  --bmc1_add_unsat_core                   none
% 19.74/3.04  --bmc1_unsat_core_children              false
% 19.74/3.04  --bmc1_unsat_core_extrapolate_axioms    false
% 19.74/3.04  --bmc1_out_stat                         full
% 19.74/3.04  --bmc1_ground_init                      false
% 19.74/3.04  --bmc1_pre_inst_next_state              false
% 19.74/3.04  --bmc1_pre_inst_state                   false
% 19.74/3.04  --bmc1_pre_inst_reach_state             false
% 19.74/3.04  --bmc1_out_unsat_core                   false
% 19.74/3.04  --bmc1_aig_witness_out                  false
% 19.74/3.04  --bmc1_verbose                          false
% 19.74/3.04  --bmc1_dump_clauses_tptp                false
% 19.74/3.04  --bmc1_dump_unsat_core_tptp             false
% 19.74/3.04  --bmc1_dump_file                        -
% 19.74/3.04  --bmc1_ucm_expand_uc_limit              128
% 19.74/3.04  --bmc1_ucm_n_expand_iterations          6
% 19.74/3.04  --bmc1_ucm_extend_mode                  1
% 19.74/3.04  --bmc1_ucm_init_mode                    2
% 19.74/3.04  --bmc1_ucm_cone_mode                    none
% 19.74/3.04  --bmc1_ucm_reduced_relation_type        0
% 19.74/3.04  --bmc1_ucm_relax_model                  4
% 19.74/3.04  --bmc1_ucm_full_tr_after_sat            true
% 19.74/3.04  --bmc1_ucm_expand_neg_assumptions       false
% 19.74/3.04  --bmc1_ucm_layered_model                none
% 19.74/3.04  --bmc1_ucm_max_lemma_size               10
% 19.74/3.04  
% 19.74/3.04  ------ AIG Options
% 19.74/3.04  
% 19.74/3.04  --aig_mode                              false
% 19.74/3.04  
% 19.74/3.04  ------ Instantiation Options
% 19.74/3.04  
% 19.74/3.04  --instantiation_flag                    true
% 19.74/3.04  --inst_sos_flag                         false
% 19.74/3.04  --inst_sos_phase                        true
% 19.74/3.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.74/3.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.74/3.04  --inst_lit_sel_side                     num_symb
% 19.74/3.04  --inst_solver_per_active                1400
% 19.74/3.04  --inst_solver_calls_frac                1.
% 19.74/3.04  --inst_passive_queue_type               priority_queues
% 19.74/3.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.74/3.04  --inst_passive_queues_freq              [25;2]
% 19.74/3.04  --inst_dismatching                      true
% 19.74/3.04  --inst_eager_unprocessed_to_passive     true
% 19.74/3.04  --inst_prop_sim_given                   true
% 19.74/3.04  --inst_prop_sim_new                     false
% 19.74/3.04  --inst_subs_new                         false
% 19.74/3.04  --inst_eq_res_simp                      false
% 19.74/3.04  --inst_subs_given                       false
% 19.74/3.04  --inst_orphan_elimination               true
% 19.74/3.04  --inst_learning_loop_flag               true
% 19.74/3.04  --inst_learning_start                   3000
% 19.74/3.04  --inst_learning_factor                  2
% 19.74/3.04  --inst_start_prop_sim_after_learn       3
% 19.74/3.04  --inst_sel_renew                        solver
% 19.74/3.04  --inst_lit_activity_flag                true
% 19.74/3.04  --inst_restr_to_given                   false
% 19.74/3.04  --inst_activity_threshold               500
% 19.74/3.04  --inst_out_proof                        true
% 19.74/3.04  
% 19.74/3.04  ------ Resolution Options
% 19.74/3.04  
% 19.74/3.04  --resolution_flag                       true
% 19.74/3.04  --res_lit_sel                           adaptive
% 19.74/3.04  --res_lit_sel_side                      none
% 19.74/3.04  --res_ordering                          kbo
% 19.74/3.04  --res_to_prop_solver                    active
% 19.74/3.04  --res_prop_simpl_new                    false
% 19.74/3.04  --res_prop_simpl_given                  true
% 19.74/3.04  --res_passive_queue_type                priority_queues
% 19.74/3.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.74/3.04  --res_passive_queues_freq               [15;5]
% 19.74/3.04  --res_forward_subs                      full
% 19.74/3.04  --res_backward_subs                     full
% 19.74/3.04  --res_forward_subs_resolution           true
% 19.74/3.04  --res_backward_subs_resolution          true
% 19.74/3.04  --res_orphan_elimination                true
% 19.74/3.04  --res_time_limit                        2.
% 19.74/3.04  --res_out_proof                         true
% 19.74/3.04  
% 19.74/3.04  ------ Superposition Options
% 19.74/3.04  
% 19.74/3.04  --superposition_flag                    true
% 19.74/3.04  --sup_passive_queue_type                priority_queues
% 19.74/3.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.74/3.04  --sup_passive_queues_freq               [8;1;4]
% 19.74/3.04  --demod_completeness_check              fast
% 19.74/3.04  --demod_use_ground                      true
% 19.74/3.04  --sup_to_prop_solver                    passive
% 19.74/3.04  --sup_prop_simpl_new                    true
% 19.74/3.04  --sup_prop_simpl_given                  true
% 19.74/3.04  --sup_fun_splitting                     false
% 19.74/3.04  --sup_smt_interval                      50000
% 19.74/3.04  
% 19.74/3.04  ------ Superposition Simplification Setup
% 19.74/3.04  
% 19.74/3.04  --sup_indices_passive                   []
% 19.74/3.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.74/3.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.74/3.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.74/3.04  --sup_full_triv                         [TrivRules;PropSubs]
% 19.74/3.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.74/3.04  --sup_full_bw                           [BwDemod]
% 19.74/3.04  --sup_immed_triv                        [TrivRules]
% 19.74/3.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.74/3.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.74/3.04  --sup_immed_bw_main                     []
% 19.74/3.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.74/3.04  --sup_input_triv                        [Unflattening;TrivRules]
% 19.74/3.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.74/3.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.74/3.04  
% 19.74/3.04  ------ Combination Options
% 19.74/3.04  
% 19.74/3.04  --comb_res_mult                         3
% 19.74/3.04  --comb_sup_mult                         2
% 19.74/3.04  --comb_inst_mult                        10
% 19.74/3.04  
% 19.74/3.04  ------ Debug Options
% 19.74/3.04  
% 19.74/3.04  --dbg_backtrace                         false
% 19.74/3.04  --dbg_dump_prop_clauses                 false
% 19.74/3.04  --dbg_dump_prop_clauses_file            -
% 19.74/3.04  --dbg_out_stat                          false
% 19.74/3.04  ------ Parsing...
% 19.74/3.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.74/3.04  
% 19.74/3.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.74/3.04  
% 19.74/3.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.74/3.04  
% 19.74/3.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.74/3.04  ------ Proving...
% 19.74/3.04  ------ Problem Properties 
% 19.74/3.04  
% 19.74/3.04  
% 19.74/3.04  clauses                                 16
% 19.74/3.04  conjectures                             1
% 19.74/3.04  EPR                                     0
% 19.74/3.04  Horn                                    12
% 19.74/3.04  unary                                   5
% 19.74/3.04  binary                                  8
% 19.74/3.04  lits                                    30
% 19.74/3.04  lits eq                                 14
% 19.74/3.04  fd_pure                                 0
% 19.74/3.04  fd_pseudo                               0
% 19.74/3.04  fd_cond                                 1
% 19.74/3.04  fd_pseudo_cond                          3
% 19.74/3.04  AC symbols                              0
% 19.74/3.04  
% 19.74/3.04  ------ Schedule dynamic 5 is on 
% 19.74/3.04  
% 19.74/3.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.74/3.04  
% 19.74/3.04  
% 19.74/3.04  ------ 
% 19.74/3.04  Current options:
% 19.74/3.04  ------ 
% 19.74/3.04  
% 19.74/3.04  ------ Input Options
% 19.74/3.04  
% 19.74/3.04  --out_options                           all
% 19.74/3.04  --tptp_safe_out                         true
% 19.74/3.04  --problem_path                          ""
% 19.74/3.04  --include_path                          ""
% 19.74/3.04  --clausifier                            res/vclausify_rel
% 19.74/3.04  --clausifier_options                    --mode clausify
% 19.74/3.04  --stdin                                 false
% 19.74/3.04  --stats_out                             all
% 19.74/3.04  
% 19.74/3.04  ------ General Options
% 19.74/3.04  
% 19.74/3.04  --fof                                   false
% 19.74/3.04  --time_out_real                         305.
% 19.74/3.04  --time_out_virtual                      -1.
% 19.74/3.04  --symbol_type_check                     false
% 19.74/3.04  --clausify_out                          false
% 19.74/3.04  --sig_cnt_out                           false
% 19.74/3.04  --trig_cnt_out                          false
% 19.74/3.04  --trig_cnt_out_tolerance                1.
% 19.74/3.04  --trig_cnt_out_sk_spl                   false
% 19.74/3.04  --abstr_cl_out                          false
% 19.74/3.04  
% 19.74/3.04  ------ Global Options
% 19.74/3.04  
% 19.74/3.04  --schedule                              default
% 19.74/3.04  --add_important_lit                     false
% 19.74/3.04  --prop_solver_per_cl                    1000
% 19.74/3.04  --min_unsat_core                        false
% 19.74/3.04  --soft_assumptions                      false
% 19.74/3.04  --soft_lemma_size                       3
% 19.74/3.04  --prop_impl_unit_size                   0
% 19.74/3.04  --prop_impl_unit                        []
% 19.74/3.04  --share_sel_clauses                     true
% 19.74/3.04  --reset_solvers                         false
% 19.74/3.04  --bc_imp_inh                            [conj_cone]
% 19.74/3.04  --conj_cone_tolerance                   3.
% 19.74/3.04  --extra_neg_conj                        none
% 19.74/3.04  --large_theory_mode                     true
% 19.74/3.04  --prolific_symb_bound                   200
% 19.74/3.04  --lt_threshold                          2000
% 19.74/3.04  --clause_weak_htbl                      true
% 19.74/3.04  --gc_record_bc_elim                     false
% 19.74/3.04  
% 19.74/3.04  ------ Preprocessing Options
% 19.74/3.04  
% 19.74/3.04  --preprocessing_flag                    true
% 19.74/3.04  --time_out_prep_mult                    0.1
% 19.74/3.04  --splitting_mode                        input
% 19.74/3.04  --splitting_grd                         true
% 19.74/3.04  --splitting_cvd                         false
% 19.74/3.04  --splitting_cvd_svl                     false
% 19.74/3.04  --splitting_nvd                         32
% 19.74/3.04  --sub_typing                            true
% 19.74/3.04  --prep_gs_sim                           true
% 19.74/3.04  --prep_unflatten                        true
% 19.74/3.04  --prep_res_sim                          true
% 19.74/3.04  --prep_upred                            true
% 19.74/3.04  --prep_sem_filter                       exhaustive
% 19.74/3.04  --prep_sem_filter_out                   false
% 19.74/3.04  --pred_elim                             true
% 19.74/3.04  --res_sim_input                         true
% 19.74/3.04  --eq_ax_congr_red                       true
% 19.74/3.04  --pure_diseq_elim                       true
% 19.74/3.04  --brand_transform                       false
% 19.74/3.04  --non_eq_to_eq                          false
% 19.74/3.04  --prep_def_merge                        true
% 19.74/3.04  --prep_def_merge_prop_impl              false
% 19.74/3.04  --prep_def_merge_mbd                    true
% 19.74/3.04  --prep_def_merge_tr_red                 false
% 19.74/3.04  --prep_def_merge_tr_cl                  false
% 19.74/3.04  --smt_preprocessing                     true
% 19.74/3.04  --smt_ac_axioms                         fast
% 19.74/3.04  --preprocessed_out                      false
% 19.74/3.04  --preprocessed_stats                    false
% 19.74/3.04  
% 19.74/3.04  ------ Abstraction refinement Options
% 19.74/3.04  
% 19.74/3.04  --abstr_ref                             []
% 19.74/3.04  --abstr_ref_prep                        false
% 19.74/3.04  --abstr_ref_until_sat                   false
% 19.74/3.04  --abstr_ref_sig_restrict                funpre
% 19.74/3.04  --abstr_ref_af_restrict_to_split_sk     false
% 19.74/3.04  --abstr_ref_under                       []
% 19.74/3.04  
% 19.74/3.04  ------ SAT Options
% 19.74/3.04  
% 19.74/3.04  --sat_mode                              false
% 19.74/3.04  --sat_fm_restart_options                ""
% 19.74/3.04  --sat_gr_def                            false
% 19.74/3.04  --sat_epr_types                         true
% 19.74/3.04  --sat_non_cyclic_types                  false
% 19.74/3.04  --sat_finite_models                     false
% 19.74/3.04  --sat_fm_lemmas                         false
% 19.74/3.04  --sat_fm_prep                           false
% 19.74/3.04  --sat_fm_uc_incr                        true
% 19.74/3.04  --sat_out_model                         small
% 19.74/3.04  --sat_out_clauses                       false
% 19.74/3.04  
% 19.74/3.04  ------ QBF Options
% 19.74/3.04  
% 19.74/3.04  --qbf_mode                              false
% 19.74/3.04  --qbf_elim_univ                         false
% 19.74/3.04  --qbf_dom_inst                          none
% 19.74/3.04  --qbf_dom_pre_inst                      false
% 19.74/3.04  --qbf_sk_in                             false
% 19.74/3.04  --qbf_pred_elim                         true
% 19.74/3.04  --qbf_split                             512
% 19.74/3.04  
% 19.74/3.04  ------ BMC1 Options
% 19.74/3.04  
% 19.74/3.04  --bmc1_incremental                      false
% 19.74/3.04  --bmc1_axioms                           reachable_all
% 19.74/3.04  --bmc1_min_bound                        0
% 19.74/3.04  --bmc1_max_bound                        -1
% 19.74/3.04  --bmc1_max_bound_default                -1
% 19.74/3.04  --bmc1_symbol_reachability              true
% 19.74/3.04  --bmc1_property_lemmas                  false
% 19.74/3.04  --bmc1_k_induction                      false
% 19.74/3.04  --bmc1_non_equiv_states                 false
% 19.74/3.04  --bmc1_deadlock                         false
% 19.74/3.04  --bmc1_ucm                              false
% 19.74/3.04  --bmc1_add_unsat_core                   none
% 19.74/3.04  --bmc1_unsat_core_children              false
% 19.74/3.04  --bmc1_unsat_core_extrapolate_axioms    false
% 19.74/3.04  --bmc1_out_stat                         full
% 19.74/3.04  --bmc1_ground_init                      false
% 19.74/3.04  --bmc1_pre_inst_next_state              false
% 19.74/3.04  --bmc1_pre_inst_state                   false
% 19.74/3.04  --bmc1_pre_inst_reach_state             false
% 19.74/3.04  --bmc1_out_unsat_core                   false
% 19.74/3.04  --bmc1_aig_witness_out                  false
% 19.74/3.04  --bmc1_verbose                          false
% 19.74/3.04  --bmc1_dump_clauses_tptp                false
% 19.74/3.04  --bmc1_dump_unsat_core_tptp             false
% 19.74/3.04  --bmc1_dump_file                        -
% 19.74/3.04  --bmc1_ucm_expand_uc_limit              128
% 19.74/3.04  --bmc1_ucm_n_expand_iterations          6
% 19.74/3.04  --bmc1_ucm_extend_mode                  1
% 19.74/3.04  --bmc1_ucm_init_mode                    2
% 19.74/3.04  --bmc1_ucm_cone_mode                    none
% 19.74/3.04  --bmc1_ucm_reduced_relation_type        0
% 19.74/3.04  --bmc1_ucm_relax_model                  4
% 19.74/3.04  --bmc1_ucm_full_tr_after_sat            true
% 19.74/3.04  --bmc1_ucm_expand_neg_assumptions       false
% 19.74/3.04  --bmc1_ucm_layered_model                none
% 19.74/3.04  --bmc1_ucm_max_lemma_size               10
% 19.74/3.04  
% 19.74/3.04  ------ AIG Options
% 19.74/3.04  
% 19.74/3.04  --aig_mode                              false
% 19.74/3.04  
% 19.74/3.04  ------ Instantiation Options
% 19.74/3.04  
% 19.74/3.04  --instantiation_flag                    true
% 19.74/3.04  --inst_sos_flag                         false
% 19.74/3.04  --inst_sos_phase                        true
% 19.74/3.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.74/3.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.74/3.04  --inst_lit_sel_side                     none
% 19.74/3.04  --inst_solver_per_active                1400
% 19.74/3.04  --inst_solver_calls_frac                1.
% 19.74/3.04  --inst_passive_queue_type               priority_queues
% 19.74/3.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.74/3.04  --inst_passive_queues_freq              [25;2]
% 19.74/3.04  --inst_dismatching                      true
% 19.74/3.04  --inst_eager_unprocessed_to_passive     true
% 19.74/3.04  --inst_prop_sim_given                   true
% 19.74/3.04  --inst_prop_sim_new                     false
% 19.74/3.04  --inst_subs_new                         false
% 19.74/3.04  --inst_eq_res_simp                      false
% 19.74/3.04  --inst_subs_given                       false
% 19.74/3.04  --inst_orphan_elimination               true
% 19.74/3.04  --inst_learning_loop_flag               true
% 19.74/3.04  --inst_learning_start                   3000
% 19.74/3.04  --inst_learning_factor                  2
% 19.74/3.04  --inst_start_prop_sim_after_learn       3
% 19.74/3.04  --inst_sel_renew                        solver
% 19.74/3.04  --inst_lit_activity_flag                true
% 19.74/3.04  --inst_restr_to_given                   false
% 19.74/3.04  --inst_activity_threshold               500
% 19.74/3.04  --inst_out_proof                        true
% 19.74/3.04  
% 19.74/3.04  ------ Resolution Options
% 19.74/3.04  
% 19.74/3.04  --resolution_flag                       false
% 19.74/3.04  --res_lit_sel                           adaptive
% 19.74/3.04  --res_lit_sel_side                      none
% 19.74/3.04  --res_ordering                          kbo
% 19.74/3.04  --res_to_prop_solver                    active
% 19.74/3.04  --res_prop_simpl_new                    false
% 19.74/3.04  --res_prop_simpl_given                  true
% 19.74/3.04  --res_passive_queue_type                priority_queues
% 19.74/3.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.74/3.04  --res_passive_queues_freq               [15;5]
% 19.74/3.04  --res_forward_subs                      full
% 19.74/3.04  --res_backward_subs                     full
% 19.74/3.04  --res_forward_subs_resolution           true
% 19.74/3.04  --res_backward_subs_resolution          true
% 19.74/3.04  --res_orphan_elimination                true
% 19.74/3.04  --res_time_limit                        2.
% 19.74/3.04  --res_out_proof                         true
% 19.74/3.04  
% 19.74/3.04  ------ Superposition Options
% 19.74/3.04  
% 19.74/3.04  --superposition_flag                    true
% 19.74/3.04  --sup_passive_queue_type                priority_queues
% 19.74/3.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.74/3.04  --sup_passive_queues_freq               [8;1;4]
% 19.74/3.04  --demod_completeness_check              fast
% 19.74/3.04  --demod_use_ground                      true
% 19.74/3.04  --sup_to_prop_solver                    passive
% 19.74/3.04  --sup_prop_simpl_new                    true
% 19.74/3.04  --sup_prop_simpl_given                  true
% 19.74/3.04  --sup_fun_splitting                     false
% 19.74/3.04  --sup_smt_interval                      50000
% 19.74/3.04  
% 19.74/3.04  ------ Superposition Simplification Setup
% 19.74/3.04  
% 19.74/3.04  --sup_indices_passive                   []
% 19.74/3.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.74/3.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.74/3.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.74/3.04  --sup_full_triv                         [TrivRules;PropSubs]
% 19.74/3.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.74/3.04  --sup_full_bw                           [BwDemod]
% 19.74/3.04  --sup_immed_triv                        [TrivRules]
% 19.74/3.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.74/3.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.74/3.04  --sup_immed_bw_main                     []
% 19.74/3.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.74/3.04  --sup_input_triv                        [Unflattening;TrivRules]
% 19.74/3.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.74/3.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.74/3.04  
% 19.74/3.04  ------ Combination Options
% 19.74/3.04  
% 19.74/3.04  --comb_res_mult                         3
% 19.74/3.04  --comb_sup_mult                         2
% 19.74/3.04  --comb_inst_mult                        10
% 19.74/3.04  
% 19.74/3.04  ------ Debug Options
% 19.74/3.04  
% 19.74/3.04  --dbg_backtrace                         false
% 19.74/3.04  --dbg_dump_prop_clauses                 false
% 19.74/3.04  --dbg_dump_prop_clauses_file            -
% 19.74/3.04  --dbg_out_stat                          false
% 19.74/3.04  
% 19.74/3.04  
% 19.74/3.04  
% 19.74/3.04  
% 19.74/3.04  ------ Proving...
% 19.74/3.04  
% 19.74/3.04  
% 19.74/3.04  % SZS status Theorem for theBenchmark.p
% 19.74/3.04  
% 19.74/3.04  % SZS output start CNFRefutation for theBenchmark.p
% 19.74/3.04  
% 19.74/3.04  fof(f1,axiom,(
% 19.74/3.04    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f24,plain,(
% 19.74/3.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 19.74/3.04    inference(ennf_transformation,[],[f1])).
% 19.74/3.04  
% 19.74/3.04  fof(f30,plain,(
% 19.74/3.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 19.74/3.04    introduced(choice_axiom,[])).
% 19.74/3.04  
% 19.74/3.04  fof(f31,plain,(
% 19.74/3.04    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 19.74/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f30])).
% 19.74/3.04  
% 19.74/3.04  fof(f44,plain,(
% 19.74/3.04    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 19.74/3.04    inference(cnf_transformation,[],[f31])).
% 19.74/3.04  
% 19.74/3.04  fof(f20,axiom,(
% 19.74/3.04    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f27,plain,(
% 19.74/3.04    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 19.74/3.04    inference(ennf_transformation,[],[f20])).
% 19.74/3.04  
% 19.74/3.04  fof(f28,plain,(
% 19.74/3.04    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.74/3.04    inference(flattening,[],[f27])).
% 19.74/3.04  
% 19.74/3.04  fof(f42,plain,(
% 19.74/3.04    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK5(X1),k2_relat_1(X1)))),
% 19.74/3.04    introduced(choice_axiom,[])).
% 19.74/3.04  
% 19.74/3.04  fof(f43,plain,(
% 19.74/3.04    ! [X0,X1] : (r2_hidden(sK5(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.74/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f42])).
% 19.74/3.04  
% 19.74/3.04  fof(f69,plain,(
% 19.74/3.04    ( ! [X0,X1] : (r2_hidden(sK5(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f43])).
% 19.74/3.04  
% 19.74/3.04  fof(f19,axiom,(
% 19.74/3.04    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f36,plain,(
% 19.74/3.04    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 19.74/3.04    inference(nnf_transformation,[],[f19])).
% 19.74/3.04  
% 19.74/3.04  fof(f37,plain,(
% 19.74/3.04    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 19.74/3.04    inference(rectify,[],[f36])).
% 19.74/3.04  
% 19.74/3.04  fof(f40,plain,(
% 19.74/3.04    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 19.74/3.04    introduced(choice_axiom,[])).
% 19.74/3.04  
% 19.74/3.04  fof(f39,plain,(
% 19.74/3.04    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0))) )),
% 19.74/3.04    introduced(choice_axiom,[])).
% 19.74/3.04  
% 19.74/3.04  fof(f38,plain,(
% 19.74/3.04    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 19.74/3.04    introduced(choice_axiom,[])).
% 19.74/3.04  
% 19.74/3.04  fof(f41,plain,(
% 19.74/3.04    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 19.74/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).
% 19.74/3.04  
% 19.74/3.04  fof(f65,plain,(
% 19.74/3.04    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 19.74/3.04    inference(cnf_transformation,[],[f41])).
% 19.74/3.04  
% 19.74/3.04  fof(f85,plain,(
% 19.74/3.04    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 19.74/3.04    inference(equality_resolution,[],[f65])).
% 19.74/3.04  
% 19.74/3.04  fof(f3,axiom,(
% 19.74/3.04    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f25,plain,(
% 19.74/3.04    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 19.74/3.04    inference(ennf_transformation,[],[f3])).
% 19.74/3.04  
% 19.74/3.04  fof(f46,plain,(
% 19.74/3.04    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f25])).
% 19.74/3.04  
% 19.74/3.04  fof(f17,axiom,(
% 19.74/3.04    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f33,plain,(
% 19.74/3.04    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 19.74/3.04    inference(nnf_transformation,[],[f17])).
% 19.74/3.04  
% 19.74/3.04  fof(f62,plain,(
% 19.74/3.04    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f33])).
% 19.74/3.04  
% 19.74/3.04  fof(f9,axiom,(
% 19.74/3.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f52,plain,(
% 19.74/3.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f9])).
% 19.74/3.04  
% 19.74/3.04  fof(f12,axiom,(
% 19.74/3.04    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f55,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f12])).
% 19.74/3.04  
% 19.74/3.04  fof(f10,axiom,(
% 19.74/3.04    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f53,plain,(
% 19.74/3.04    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f10])).
% 19.74/3.04  
% 19.74/3.04  fof(f13,axiom,(
% 19.74/3.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f56,plain,(
% 19.74/3.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f13])).
% 19.74/3.04  
% 19.74/3.04  fof(f11,axiom,(
% 19.74/3.04    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f54,plain,(
% 19.74/3.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f11])).
% 19.74/3.04  
% 19.74/3.04  fof(f71,plain,(
% 19.74/3.04    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 19.74/3.04    inference(definition_unfolding,[],[f56,f54])).
% 19.74/3.04  
% 19.74/3.04  fof(f72,plain,(
% 19.74/3.04    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 19.74/3.04    inference(definition_unfolding,[],[f53,f71])).
% 19.74/3.04  
% 19.74/3.04  fof(f73,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.74/3.04    inference(definition_unfolding,[],[f55,f72])).
% 19.74/3.04  
% 19.74/3.04  fof(f77,plain,(
% 19.74/3.04    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 19.74/3.04    inference(definition_unfolding,[],[f52,f73])).
% 19.74/3.04  
% 19.74/3.04  fof(f81,plain,(
% 19.74/3.04    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 19.74/3.04    inference(definition_unfolding,[],[f62,f77])).
% 19.74/3.04  
% 19.74/3.04  fof(f16,axiom,(
% 19.74/3.04    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f32,plain,(
% 19.74/3.04    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 19.74/3.04    inference(nnf_transformation,[],[f16])).
% 19.74/3.04  
% 19.74/3.04  fof(f59,plain,(
% 19.74/3.04    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f32])).
% 19.74/3.04  
% 19.74/3.04  fof(f2,axiom,(
% 19.74/3.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f45,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.74/3.04    inference(cnf_transformation,[],[f2])).
% 19.74/3.04  
% 19.74/3.04  fof(f7,axiom,(
% 19.74/3.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f50,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 19.74/3.04    inference(cnf_transformation,[],[f7])).
% 19.74/3.04  
% 19.74/3.04  fof(f15,axiom,(
% 19.74/3.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f58,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.74/3.04    inference(cnf_transformation,[],[f15])).
% 19.74/3.04  
% 19.74/3.04  fof(f74,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.74/3.04    inference(definition_unfolding,[],[f58,f73])).
% 19.74/3.04  
% 19.74/3.04  fof(f75,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 19.74/3.04    inference(definition_unfolding,[],[f50,f74])).
% 19.74/3.04  
% 19.74/3.04  fof(f76,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 19.74/3.04    inference(definition_unfolding,[],[f45,f75])).
% 19.74/3.04  
% 19.74/3.04  fof(f80,plain,(
% 19.74/3.04    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 19.74/3.04    inference(definition_unfolding,[],[f59,f76,f77,f77,f77])).
% 19.74/3.04  
% 19.74/3.04  fof(f83,plain,(
% 19.74/3.04    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 19.74/3.04    inference(equality_resolution,[],[f80])).
% 19.74/3.04  
% 19.74/3.04  fof(f8,axiom,(
% 19.74/3.04    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f51,plain,(
% 19.74/3.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f8])).
% 19.74/3.04  
% 19.74/3.04  fof(f14,axiom,(
% 19.74/3.04    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f57,plain,(
% 19.74/3.04    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f14])).
% 19.74/3.04  
% 19.74/3.04  fof(f78,plain,(
% 19.74/3.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7)))) )),
% 19.74/3.04    inference(definition_unfolding,[],[f51,f74,f73,f57])).
% 19.74/3.04  
% 19.74/3.04  fof(f6,axiom,(
% 19.74/3.04    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f49,plain,(
% 19.74/3.04    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f6])).
% 19.74/3.04  
% 19.74/3.04  fof(f5,axiom,(
% 19.74/3.04    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f48,plain,(
% 19.74/3.04    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f5])).
% 19.74/3.04  
% 19.74/3.04  fof(f4,axiom,(
% 19.74/3.04    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f47,plain,(
% 19.74/3.04    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.74/3.04    inference(cnf_transformation,[],[f4])).
% 19.74/3.04  
% 19.74/3.04  fof(f18,axiom,(
% 19.74/3.04    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f23,plain,(
% 19.74/3.04    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 19.74/3.04    inference(unused_predicate_definition_removal,[],[f18])).
% 19.74/3.04  
% 19.74/3.04  fof(f26,plain,(
% 19.74/3.04    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 19.74/3.04    inference(ennf_transformation,[],[f23])).
% 19.74/3.04  
% 19.74/3.04  fof(f34,plain,(
% 19.74/3.04    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 19.74/3.04    introduced(choice_axiom,[])).
% 19.74/3.04  
% 19.74/3.04  fof(f35,plain,(
% 19.74/3.04    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 19.74/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f34])).
% 19.74/3.04  
% 19.74/3.04  fof(f63,plain,(
% 19.74/3.04    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 19.74/3.04    inference(cnf_transformation,[],[f35])).
% 19.74/3.04  
% 19.74/3.04  fof(f60,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 19.74/3.04    inference(cnf_transformation,[],[f32])).
% 19.74/3.04  
% 19.74/3.04  fof(f79,plain,(
% 19.74/3.04    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 19.74/3.04    inference(definition_unfolding,[],[f60,f76,f77,f77,f77])).
% 19.74/3.04  
% 19.74/3.04  fof(f21,conjecture,(
% 19.74/3.04    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 19.74/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/3.04  
% 19.74/3.04  fof(f22,negated_conjecture,(
% 19.74/3.04    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 19.74/3.04    inference(negated_conjecture,[],[f21])).
% 19.74/3.04  
% 19.74/3.04  fof(f29,plain,(
% 19.74/3.04    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 19.74/3.04    inference(ennf_transformation,[],[f22])).
% 19.74/3.04  
% 19.74/3.04  fof(f70,plain,(
% 19.74/3.04    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 19.74/3.04    inference(cnf_transformation,[],[f29])).
% 19.74/3.04  
% 19.74/3.04  cnf(c_1,plain,
% 19.74/3.04      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 19.74/3.04      inference(cnf_transformation,[],[f44]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_521,plain,
% 19.74/3.04      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 19.74/3.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_16,plain,
% 19.74/3.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.74/3.04      | r2_hidden(sK5(X1),k2_relat_1(X1))
% 19.74/3.04      | ~ v1_relat_1(X1) ),
% 19.74/3.04      inference(cnf_transformation,[],[f69]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_514,plain,
% 19.74/3.04      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 19.74/3.04      | r2_hidden(sK5(X1),k2_relat_1(X1)) = iProver_top
% 19.74/3.04      | v1_relat_1(X1) != iProver_top ),
% 19.74/3.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_1543,plain,
% 19.74/3.04      ( k1_relat_1(X0) = k1_xboole_0
% 19.74/3.04      | r2_hidden(sK5(X0),k2_relat_1(X0)) = iProver_top
% 19.74/3.04      | v1_relat_1(X0) != iProver_top ),
% 19.74/3.04      inference(superposition,[status(thm)],[c_521,c_514]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_15,plain,
% 19.74/3.04      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 19.74/3.04      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
% 19.74/3.04      inference(cnf_transformation,[],[f85]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_515,plain,
% 19.74/3.04      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 19.74/3.04      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
% 19.74/3.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_2,plain,
% 19.74/3.04      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 19.74/3.04      inference(cnf_transformation,[],[f46]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_8,plain,
% 19.74/3.04      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 19.74/3.04      | ~ r2_hidden(X0,X1) ),
% 19.74/3.04      inference(cnf_transformation,[],[f81]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_110,plain,
% 19.74/3.04      ( ~ r2_hidden(X0,X1)
% 19.74/3.04      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 19.74/3.04      inference(prop_impl,[status(thm)],[c_8]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_111,plain,
% 19.74/3.04      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 19.74/3.04      | ~ r2_hidden(X0,X1) ),
% 19.74/3.04      inference(renaming,[status(thm)],[c_110]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_190,plain,
% 19.74/3.04      ( ~ r2_hidden(X0,X1)
% 19.74/3.04      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X2
% 19.74/3.04      | k1_xboole_0 != X1
% 19.74/3.04      | k1_xboole_0 = X2 ),
% 19.74/3.04      inference(resolution_lifted,[status(thm)],[c_2,c_111]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_191,plain,
% 19.74/3.04      ( ~ r2_hidden(X0,k1_xboole_0)
% 19.74/3.04      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 19.74/3.04      inference(unflattening,[status(thm)],[c_190]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_513,plain,
% 19.74/3.04      ( k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 19.74/3.04      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.74/3.04      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_3253,plain,
% 19.74/3.04      ( k6_enumset1(k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0)) = k1_xboole_0
% 19.74/3.04      | r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 19.74/3.04      inference(superposition,[status(thm)],[c_515,c_513]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_7,plain,
% 19.74/3.04      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 19.74/3.04      inference(cnf_transformation,[],[f83]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_0,plain,
% 19.74/3.04      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 19.74/3.04      inference(cnf_transformation,[],[f78]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_5,plain,
% 19.74/3.04      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.74/3.04      inference(cnf_transformation,[],[f49]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_576,plain,
% 19.74/3.04      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 19.74/3.04      inference(demodulation,[status(thm)],[c_7,c_0,c_5]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_4,plain,
% 19.74/3.04      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.74/3.04      inference(cnf_transformation,[],[f48]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_619,plain,
% 19.74/3.04      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.74/3.04      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_617,plain,
% 19.74/3.04      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 19.74/3.04      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_758,plain,
% 19.74/3.04      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 19.74/3.04      inference(superposition,[status(thm)],[c_5,c_617]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_3,plain,
% 19.74/3.04      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.74/3.04      inference(cnf_transformation,[],[f47]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_782,plain,
% 19.74/3.04      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.74/3.04      inference(light_normalisation,[status(thm)],[c_758,c_3]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_783,plain,
% 19.74/3.04      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 19.74/3.04      inference(demodulation,[status(thm)],[c_782,c_617]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_1070,plain,
% 19.74/3.04      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 19.74/3.04      inference(superposition,[status(thm)],[c_619,c_783]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_1085,plain,
% 19.74/3.04      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 19.74/3.04      inference(demodulation,[status(thm)],[c_1070,c_3]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_18667,plain,
% 19.74/3.04      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 19.74/3.04      inference(demodulation,[status(thm)],[c_576,c_1085]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_72431,plain,
% 19.74/3.04      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 19.74/3.04      inference(forward_subsumption_resolution,
% 19.74/3.04                [status(thm)],
% 19.74/3.04                [c_3253,c_18667]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_72440,plain,
% 19.74/3.04      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 19.74/3.04      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.74/3.04      inference(superposition,[status(thm)],[c_1543,c_72431]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_72435,plain,
% 19.74/3.04      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.74/3.04      inference(superposition,[status(thm)],[c_521,c_72431]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_11,plain,
% 19.74/3.04      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 19.74/3.04      inference(cnf_transformation,[],[f63]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_519,plain,
% 19.74/3.04      ( r2_hidden(sK1(X0),X0) = iProver_top
% 19.74/3.04      | v1_relat_1(X0) = iProver_top ),
% 19.74/3.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_1061,plain,
% 19.74/3.04      ( k6_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0)) = k1_xboole_0
% 19.74/3.04      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 19.74/3.04      inference(superposition,[status(thm)],[c_519,c_513]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_29549,plain,
% 19.74/3.04      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 19.74/3.04      inference(forward_subsumption_resolution,
% 19.74/3.04                [status(thm)],
% 19.74/3.04                [c_1061,c_18667]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_345,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_752,plain,
% 19.74/3.04      ( k2_relat_1(k1_xboole_0) != X0
% 19.74/3.04      | k1_xboole_0 != X0
% 19.74/3.04      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 19.74/3.04      inference(instantiation,[status(thm)],[c_345]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_753,plain,
% 19.74/3.04      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 19.74/3.04      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 19.74/3.04      | k1_xboole_0 != k1_xboole_0 ),
% 19.74/3.04      inference(instantiation,[status(thm)],[c_752]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_610,plain,
% 19.74/3.04      ( k1_relat_1(k1_xboole_0) != X0
% 19.74/3.04      | k1_xboole_0 != X0
% 19.74/3.04      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 19.74/3.04      inference(instantiation,[status(thm)],[c_345]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_611,plain,
% 19.74/3.04      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 19.74/3.04      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 19.74/3.04      | k1_xboole_0 != k1_xboole_0 ),
% 19.74/3.04      inference(instantiation,[status(thm)],[c_610]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_6,plain,
% 19.74/3.04      ( X0 = X1
% 19.74/3.04      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 19.74/3.04      inference(cnf_transformation,[],[f79]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_46,plain,
% 19.74/3.04      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 19.74/3.04      | k1_xboole_0 = k1_xboole_0 ),
% 19.74/3.04      inference(instantiation,[status(thm)],[c_6]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_45,plain,
% 19.74/3.04      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 19.74/3.04      inference(instantiation,[status(thm)],[c_7]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(c_17,negated_conjecture,
% 19.74/3.04      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
% 19.74/3.04      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 19.74/3.04      inference(cnf_transformation,[],[f70]) ).
% 19.74/3.04  
% 19.74/3.04  cnf(contradiction,plain,
% 19.74/3.04      ( $false ),
% 19.74/3.04      inference(minisat,
% 19.74/3.04                [status(thm)],
% 19.74/3.04                [c_72440,c_72435,c_29549,c_753,c_611,c_46,c_45,c_17]) ).
% 19.74/3.04  
% 19.74/3.04  
% 19.74/3.04  % SZS output end CNFRefutation for theBenchmark.p
% 19.74/3.04  
% 19.74/3.04  ------                               Statistics
% 19.74/3.04  
% 19.74/3.04  ------ General
% 19.74/3.04  
% 19.74/3.04  abstr_ref_over_cycles:                  0
% 19.74/3.04  abstr_ref_under_cycles:                 0
% 19.74/3.04  gc_basic_clause_elim:                   0
% 19.74/3.04  forced_gc_time:                         0
% 19.74/3.04  parsing_time:                           0.01
% 19.74/3.04  unif_index_cands_time:                  0.
% 19.74/3.04  unif_index_add_time:                    0.
% 19.74/3.04  orderings_time:                         0.
% 19.74/3.04  out_proof_time:                         0.009
% 19.74/3.04  total_time:                             2.056
% 19.74/3.04  num_of_symbols:                         47
% 19.74/3.04  num_of_terms:                           87855
% 19.74/3.04  
% 19.74/3.04  ------ Preprocessing
% 19.74/3.04  
% 19.74/3.04  num_of_splits:                          0
% 19.74/3.04  num_of_split_atoms:                     0
% 19.74/3.04  num_of_reused_defs:                     0
% 19.74/3.04  num_eq_ax_congr_red:                    30
% 19.74/3.04  num_of_sem_filtered_clauses:            1
% 19.74/3.04  num_of_subtypes:                        0
% 19.74/3.04  monotx_restored_types:                  0
% 19.74/3.04  sat_num_of_epr_types:                   0
% 19.74/3.04  sat_num_of_non_cyclic_types:            0
% 19.74/3.04  sat_guarded_non_collapsed_types:        0
% 19.74/3.04  num_pure_diseq_elim:                    0
% 19.74/3.04  simp_replaced_by:                       0
% 19.74/3.04  res_preprocessed:                       85
% 19.74/3.04  prep_upred:                             0
% 19.74/3.04  prep_unflattend:                        6
% 19.74/3.04  smt_new_axioms:                         0
% 19.74/3.04  pred_elim_cands:                        2
% 19.74/3.04  pred_elim:                              1
% 19.74/3.04  pred_elim_cl:                           2
% 19.74/3.04  pred_elim_cycles:                       3
% 19.74/3.04  merged_defs:                            2
% 19.74/3.04  merged_defs_ncl:                        0
% 19.74/3.04  bin_hyper_res:                          2
% 19.74/3.04  prep_cycles:                            4
% 19.74/3.04  pred_elim_time:                         0.001
% 19.74/3.04  splitting_time:                         0.
% 19.74/3.04  sem_filter_time:                        0.
% 19.74/3.04  monotx_time:                            0.
% 19.74/3.04  subtype_inf_time:                       0.
% 19.74/3.04  
% 19.74/3.04  ------ Problem properties
% 19.74/3.04  
% 19.74/3.04  clauses:                                16
% 19.74/3.04  conjectures:                            1
% 19.74/3.04  epr:                                    0
% 19.74/3.04  horn:                                   12
% 19.74/3.04  ground:                                 1
% 19.74/3.04  unary:                                  5
% 19.74/3.04  binary:                                 8
% 19.74/3.04  lits:                                   30
% 19.74/3.04  lits_eq:                                14
% 19.74/3.04  fd_pure:                                0
% 19.74/3.04  fd_pseudo:                              0
% 19.74/3.04  fd_cond:                                1
% 19.74/3.04  fd_pseudo_cond:                         3
% 19.74/3.04  ac_symbols:                             1
% 19.74/3.04  
% 19.74/3.04  ------ Propositional Solver
% 19.74/3.04  
% 19.74/3.04  prop_solver_calls:                      30
% 19.74/3.04  prop_fast_solver_calls:                 569
% 19.74/3.04  smt_solver_calls:                       0
% 19.74/3.04  smt_fast_solver_calls:                  0
% 19.74/3.04  prop_num_of_clauses:                    8508
% 19.74/3.04  prop_preprocess_simplified:             10876
% 19.74/3.04  prop_fo_subsumed:                       0
% 19.74/3.04  prop_solver_time:                       0.
% 19.74/3.04  smt_solver_time:                        0.
% 19.74/3.04  smt_fast_solver_time:                   0.
% 19.74/3.04  prop_fast_solver_time:                  0.
% 19.74/3.04  prop_unsat_core_time:                   0.
% 19.74/3.04  
% 19.74/3.04  ------ QBF
% 19.74/3.04  
% 19.74/3.04  qbf_q_res:                              0
% 19.74/3.04  qbf_num_tautologies:                    0
% 19.74/3.04  qbf_prep_cycles:                        0
% 19.74/3.04  
% 19.74/3.04  ------ BMC1
% 19.74/3.04  
% 19.74/3.04  bmc1_current_bound:                     -1
% 19.74/3.04  bmc1_last_solved_bound:                 -1
% 19.74/3.04  bmc1_unsat_core_size:                   -1
% 19.74/3.04  bmc1_unsat_core_parents_size:           -1
% 19.74/3.04  bmc1_merge_next_fun:                    0
% 19.74/3.04  bmc1_unsat_core_clauses_time:           0.
% 19.74/3.04  
% 19.74/3.04  ------ Instantiation
% 19.74/3.04  
% 19.74/3.04  inst_num_of_clauses:                    1047
% 19.74/3.04  inst_num_in_passive:                    691
% 19.74/3.04  inst_num_in_active:                     274
% 19.74/3.04  inst_num_in_unprocessed:                84
% 19.74/3.04  inst_num_of_loops:                      630
% 19.74/3.04  inst_num_of_learning_restarts:          0
% 19.74/3.04  inst_num_moves_active_passive:          351
% 19.74/3.04  inst_lit_activity:                      0
% 19.74/3.04  inst_lit_activity_moves:                0
% 19.74/3.04  inst_num_tautologies:                   0
% 19.74/3.04  inst_num_prop_implied:                  0
% 19.74/3.04  inst_num_existing_simplified:           0
% 19.74/3.04  inst_num_eq_res_simplified:             0
% 19.74/3.04  inst_num_child_elim:                    0
% 19.74/3.04  inst_num_of_dismatching_blockings:      389
% 19.74/3.04  inst_num_of_non_proper_insts:           985
% 19.74/3.04  inst_num_of_duplicates:                 0
% 19.74/3.04  inst_inst_num_from_inst_to_res:         0
% 19.74/3.04  inst_dismatching_checking_time:         0.
% 19.74/3.04  
% 19.74/3.04  ------ Resolution
% 19.74/3.04  
% 19.74/3.04  res_num_of_clauses:                     0
% 19.74/3.04  res_num_in_passive:                     0
% 19.74/3.04  res_num_in_active:                      0
% 19.74/3.04  res_num_of_loops:                       89
% 19.74/3.04  res_forward_subset_subsumed:            86
% 19.74/3.04  res_backward_subset_subsumed:           6
% 19.74/3.04  res_forward_subsumed:                   0
% 19.74/3.04  res_backward_subsumed:                  0
% 19.74/3.04  res_forward_subsumption_resolution:     0
% 19.74/3.04  res_backward_subsumption_resolution:    0
% 19.74/3.04  res_clause_to_clause_subsumption:       478056
% 19.74/3.04  res_orphan_elimination:                 0
% 19.74/3.04  res_tautology_del:                      102
% 19.74/3.04  res_num_eq_res_simplified:              0
% 19.74/3.04  res_num_sel_changes:                    0
% 19.74/3.04  res_moves_from_active_to_pass:          0
% 19.74/3.04  
% 19.74/3.04  ------ Superposition
% 19.74/3.04  
% 19.74/3.04  sup_time_total:                         0.
% 19.74/3.04  sup_time_generating:                    0.
% 19.74/3.04  sup_time_sim_full:                      0.
% 19.74/3.04  sup_time_sim_immed:                     0.
% 19.74/3.04  
% 19.74/3.04  sup_num_of_clauses:                     4930
% 19.74/3.04  sup_num_in_active:                      108
% 19.74/3.04  sup_num_in_passive:                     4822
% 19.74/3.04  sup_num_of_loops:                       125
% 19.74/3.04  sup_fw_superposition:                   17764
% 19.74/3.04  sup_bw_superposition:                   12558
% 19.74/3.04  sup_immediate_simplified:               11815
% 19.74/3.04  sup_given_eliminated:                   9
% 19.74/3.04  comparisons_done:                       0
% 19.74/3.04  comparisons_avoided:                    0
% 19.74/3.04  
% 19.74/3.04  ------ Simplifications
% 19.74/3.04  
% 19.74/3.04  
% 19.74/3.04  sim_fw_subset_subsumed:                 0
% 19.74/3.04  sim_bw_subset_subsumed:                 0
% 19.74/3.04  sim_fw_subsumed:                        609
% 19.74/3.04  sim_bw_subsumed:                        2
% 19.74/3.04  sim_fw_subsumption_res:                 2
% 19.74/3.04  sim_bw_subsumption_res:                 0
% 19.74/3.04  sim_tautology_del:                      1
% 19.74/3.04  sim_eq_tautology_del:                   1952
% 19.74/3.04  sim_eq_res_simp:                        0
% 19.74/3.04  sim_fw_demodulated:                     6847
% 19.74/3.04  sim_bw_demodulated:                     1247
% 19.74/3.04  sim_light_normalised:                   5020
% 19.74/3.04  sim_joinable_taut:                      791
% 19.74/3.04  sim_joinable_simp:                      0
% 19.74/3.04  sim_ac_normalised:                      0
% 19.74/3.04  sim_smt_subsumption:                    0
% 19.74/3.04  
%------------------------------------------------------------------------------
