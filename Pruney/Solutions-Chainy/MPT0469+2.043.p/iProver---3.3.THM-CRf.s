%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:49 EST 2020

% Result     : Theorem 15.87s
% Output     : CNFRefutation 15.87s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 798 expanded)
%              Number of clauses        :   46 ( 120 expanded)
%              Number of leaves         :   29 ( 247 expanded)
%              Depth                    :   17
%              Number of atoms          :  254 (1036 expanded)
%              Number of equality atoms :  146 ( 833 expanded)
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

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f31])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK5(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f43])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
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
    inference(nnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f75,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f74])).

fof(f76,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f54,f75])).

fof(f80,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f53,f76])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f80])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f76])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f77])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f63,f79,f80,f80,f80])).

fof(f86,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f52,f77,f76,f59])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f19])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f35])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f64,f79,f80,f80,f80])).

fof(f22,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f30,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f23])).

fof(f72,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_521,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(sK5(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

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
    inference(cnf_transformation,[],[f88])).

cnf(c_515,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_110,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_6])).

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

cnf(c_9,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_0,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_576,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_9,c_0,c_5])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(cnf_transformation,[],[f48])).

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
    inference(cnf_transformation,[],[f65])).

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

cnf(c_8,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_39,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_72440,c_72435,c_29549,c_753,c_611,c_40,c_39,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:27:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.87/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.87/2.48  
% 15.87/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.87/2.48  
% 15.87/2.48  ------  iProver source info
% 15.87/2.48  
% 15.87/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.87/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.87/2.48  git: non_committed_changes: false
% 15.87/2.48  git: last_make_outside_of_git: false
% 15.87/2.48  
% 15.87/2.48  ------ 
% 15.87/2.48  
% 15.87/2.48  ------ Input Options
% 15.87/2.48  
% 15.87/2.48  --out_options                           all
% 15.87/2.48  --tptp_safe_out                         true
% 15.87/2.48  --problem_path                          ""
% 15.87/2.48  --include_path                          ""
% 15.87/2.48  --clausifier                            res/vclausify_rel
% 15.87/2.48  --clausifier_options                    --mode clausify
% 15.87/2.48  --stdin                                 false
% 15.87/2.48  --stats_out                             all
% 15.87/2.48  
% 15.87/2.48  ------ General Options
% 15.87/2.48  
% 15.87/2.48  --fof                                   false
% 15.87/2.48  --time_out_real                         305.
% 15.87/2.48  --time_out_virtual                      -1.
% 15.87/2.48  --symbol_type_check                     false
% 15.87/2.48  --clausify_out                          false
% 15.87/2.48  --sig_cnt_out                           false
% 15.87/2.48  --trig_cnt_out                          false
% 15.87/2.48  --trig_cnt_out_tolerance                1.
% 15.87/2.48  --trig_cnt_out_sk_spl                   false
% 15.87/2.48  --abstr_cl_out                          false
% 15.87/2.48  
% 15.87/2.48  ------ Global Options
% 15.87/2.48  
% 15.87/2.48  --schedule                              default
% 15.87/2.48  --add_important_lit                     false
% 15.87/2.48  --prop_solver_per_cl                    1000
% 15.87/2.48  --min_unsat_core                        false
% 15.87/2.48  --soft_assumptions                      false
% 15.87/2.48  --soft_lemma_size                       3
% 15.87/2.48  --prop_impl_unit_size                   0
% 15.87/2.48  --prop_impl_unit                        []
% 15.87/2.48  --share_sel_clauses                     true
% 15.87/2.48  --reset_solvers                         false
% 15.87/2.48  --bc_imp_inh                            [conj_cone]
% 15.87/2.48  --conj_cone_tolerance                   3.
% 15.87/2.48  --extra_neg_conj                        none
% 15.87/2.48  --large_theory_mode                     true
% 15.87/2.48  --prolific_symb_bound                   200
% 15.87/2.48  --lt_threshold                          2000
% 15.87/2.48  --clause_weak_htbl                      true
% 15.87/2.48  --gc_record_bc_elim                     false
% 15.87/2.48  
% 15.87/2.48  ------ Preprocessing Options
% 15.87/2.48  
% 15.87/2.48  --preprocessing_flag                    true
% 15.87/2.48  --time_out_prep_mult                    0.1
% 15.87/2.48  --splitting_mode                        input
% 15.87/2.48  --splitting_grd                         true
% 15.87/2.48  --splitting_cvd                         false
% 15.87/2.48  --splitting_cvd_svl                     false
% 15.87/2.48  --splitting_nvd                         32
% 15.87/2.48  --sub_typing                            true
% 15.87/2.48  --prep_gs_sim                           true
% 15.87/2.48  --prep_unflatten                        true
% 15.87/2.48  --prep_res_sim                          true
% 15.87/2.48  --prep_upred                            true
% 15.87/2.48  --prep_sem_filter                       exhaustive
% 15.87/2.48  --prep_sem_filter_out                   false
% 15.87/2.48  --pred_elim                             true
% 15.87/2.48  --res_sim_input                         true
% 15.87/2.48  --eq_ax_congr_red                       true
% 15.87/2.48  --pure_diseq_elim                       true
% 15.87/2.48  --brand_transform                       false
% 15.87/2.48  --non_eq_to_eq                          false
% 15.87/2.48  --prep_def_merge                        true
% 15.87/2.48  --prep_def_merge_prop_impl              false
% 15.87/2.48  --prep_def_merge_mbd                    true
% 15.87/2.48  --prep_def_merge_tr_red                 false
% 15.87/2.48  --prep_def_merge_tr_cl                  false
% 15.87/2.48  --smt_preprocessing                     true
% 15.87/2.48  --smt_ac_axioms                         fast
% 15.87/2.48  --preprocessed_out                      false
% 15.87/2.48  --preprocessed_stats                    false
% 15.87/2.48  
% 15.87/2.48  ------ Abstraction refinement Options
% 15.87/2.48  
% 15.87/2.48  --abstr_ref                             []
% 15.87/2.48  --abstr_ref_prep                        false
% 15.87/2.48  --abstr_ref_until_sat                   false
% 15.87/2.48  --abstr_ref_sig_restrict                funpre
% 15.87/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.87/2.48  --abstr_ref_under                       []
% 15.87/2.48  
% 15.87/2.48  ------ SAT Options
% 15.87/2.48  
% 15.87/2.48  --sat_mode                              false
% 15.87/2.48  --sat_fm_restart_options                ""
% 15.87/2.48  --sat_gr_def                            false
% 15.87/2.48  --sat_epr_types                         true
% 15.87/2.48  --sat_non_cyclic_types                  false
% 15.87/2.48  --sat_finite_models                     false
% 15.87/2.48  --sat_fm_lemmas                         false
% 15.87/2.48  --sat_fm_prep                           false
% 15.87/2.48  --sat_fm_uc_incr                        true
% 15.87/2.48  --sat_out_model                         small
% 15.87/2.48  --sat_out_clauses                       false
% 15.87/2.48  
% 15.87/2.48  ------ QBF Options
% 15.87/2.48  
% 15.87/2.48  --qbf_mode                              false
% 15.87/2.48  --qbf_elim_univ                         false
% 15.87/2.48  --qbf_dom_inst                          none
% 15.87/2.48  --qbf_dom_pre_inst                      false
% 15.87/2.48  --qbf_sk_in                             false
% 15.87/2.48  --qbf_pred_elim                         true
% 15.87/2.48  --qbf_split                             512
% 15.87/2.48  
% 15.87/2.48  ------ BMC1 Options
% 15.87/2.48  
% 15.87/2.48  --bmc1_incremental                      false
% 15.87/2.48  --bmc1_axioms                           reachable_all
% 15.87/2.48  --bmc1_min_bound                        0
% 15.87/2.48  --bmc1_max_bound                        -1
% 15.87/2.48  --bmc1_max_bound_default                -1
% 15.87/2.48  --bmc1_symbol_reachability              true
% 15.87/2.48  --bmc1_property_lemmas                  false
% 15.87/2.48  --bmc1_k_induction                      false
% 15.87/2.48  --bmc1_non_equiv_states                 false
% 15.87/2.48  --bmc1_deadlock                         false
% 15.87/2.48  --bmc1_ucm                              false
% 15.87/2.48  --bmc1_add_unsat_core                   none
% 15.87/2.48  --bmc1_unsat_core_children              false
% 15.87/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.87/2.48  --bmc1_out_stat                         full
% 15.87/2.48  --bmc1_ground_init                      false
% 15.87/2.48  --bmc1_pre_inst_next_state              false
% 15.87/2.48  --bmc1_pre_inst_state                   false
% 15.87/2.48  --bmc1_pre_inst_reach_state             false
% 15.87/2.48  --bmc1_out_unsat_core                   false
% 15.87/2.48  --bmc1_aig_witness_out                  false
% 15.87/2.48  --bmc1_verbose                          false
% 15.87/2.48  --bmc1_dump_clauses_tptp                false
% 15.87/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.87/2.48  --bmc1_dump_file                        -
% 15.87/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.87/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.87/2.48  --bmc1_ucm_extend_mode                  1
% 15.87/2.48  --bmc1_ucm_init_mode                    2
% 15.87/2.48  --bmc1_ucm_cone_mode                    none
% 15.87/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.87/2.48  --bmc1_ucm_relax_model                  4
% 15.87/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.87/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.87/2.48  --bmc1_ucm_layered_model                none
% 15.87/2.48  --bmc1_ucm_max_lemma_size               10
% 15.87/2.48  
% 15.87/2.48  ------ AIG Options
% 15.87/2.48  
% 15.87/2.48  --aig_mode                              false
% 15.87/2.48  
% 15.87/2.48  ------ Instantiation Options
% 15.87/2.48  
% 15.87/2.48  --instantiation_flag                    true
% 15.87/2.48  --inst_sos_flag                         false
% 15.87/2.48  --inst_sos_phase                        true
% 15.87/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.87/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.87/2.48  --inst_lit_sel_side                     num_symb
% 15.87/2.48  --inst_solver_per_active                1400
% 15.87/2.48  --inst_solver_calls_frac                1.
% 15.87/2.48  --inst_passive_queue_type               priority_queues
% 15.87/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.87/2.48  --inst_passive_queues_freq              [25;2]
% 15.87/2.48  --inst_dismatching                      true
% 15.87/2.48  --inst_eager_unprocessed_to_passive     true
% 15.87/2.48  --inst_prop_sim_given                   true
% 15.87/2.48  --inst_prop_sim_new                     false
% 15.87/2.48  --inst_subs_new                         false
% 15.87/2.48  --inst_eq_res_simp                      false
% 15.87/2.48  --inst_subs_given                       false
% 15.87/2.48  --inst_orphan_elimination               true
% 15.87/2.48  --inst_learning_loop_flag               true
% 15.87/2.48  --inst_learning_start                   3000
% 15.87/2.48  --inst_learning_factor                  2
% 15.87/2.48  --inst_start_prop_sim_after_learn       3
% 15.87/2.48  --inst_sel_renew                        solver
% 15.87/2.48  --inst_lit_activity_flag                true
% 15.87/2.48  --inst_restr_to_given                   false
% 15.87/2.48  --inst_activity_threshold               500
% 15.87/2.48  --inst_out_proof                        true
% 15.87/2.48  
% 15.87/2.48  ------ Resolution Options
% 15.87/2.48  
% 15.87/2.48  --resolution_flag                       true
% 15.87/2.48  --res_lit_sel                           adaptive
% 15.87/2.48  --res_lit_sel_side                      none
% 15.87/2.48  --res_ordering                          kbo
% 15.87/2.48  --res_to_prop_solver                    active
% 15.87/2.48  --res_prop_simpl_new                    false
% 15.87/2.48  --res_prop_simpl_given                  true
% 15.87/2.48  --res_passive_queue_type                priority_queues
% 15.87/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.87/2.48  --res_passive_queues_freq               [15;5]
% 15.87/2.48  --res_forward_subs                      full
% 15.87/2.48  --res_backward_subs                     full
% 15.87/2.48  --res_forward_subs_resolution           true
% 15.87/2.48  --res_backward_subs_resolution          true
% 15.87/2.48  --res_orphan_elimination                true
% 15.87/2.48  --res_time_limit                        2.
% 15.87/2.48  --res_out_proof                         true
% 15.87/2.48  
% 15.87/2.48  ------ Superposition Options
% 15.87/2.48  
% 15.87/2.48  --superposition_flag                    true
% 15.87/2.48  --sup_passive_queue_type                priority_queues
% 15.87/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.87/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.87/2.48  --demod_completeness_check              fast
% 15.87/2.48  --demod_use_ground                      true
% 15.87/2.48  --sup_to_prop_solver                    passive
% 15.87/2.48  --sup_prop_simpl_new                    true
% 15.87/2.48  --sup_prop_simpl_given                  true
% 15.87/2.48  --sup_fun_splitting                     false
% 15.87/2.48  --sup_smt_interval                      50000
% 15.87/2.48  
% 15.87/2.48  ------ Superposition Simplification Setup
% 15.87/2.48  
% 15.87/2.48  --sup_indices_passive                   []
% 15.87/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.87/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.87/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.87/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.87/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.87/2.48  --sup_full_bw                           [BwDemod]
% 15.87/2.48  --sup_immed_triv                        [TrivRules]
% 15.87/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.87/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.87/2.48  --sup_immed_bw_main                     []
% 15.87/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.87/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.87/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.87/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.87/2.48  
% 15.87/2.48  ------ Combination Options
% 15.87/2.48  
% 15.87/2.48  --comb_res_mult                         3
% 15.87/2.48  --comb_sup_mult                         2
% 15.87/2.48  --comb_inst_mult                        10
% 15.87/2.48  
% 15.87/2.48  ------ Debug Options
% 15.87/2.48  
% 15.87/2.48  --dbg_backtrace                         false
% 15.87/2.48  --dbg_dump_prop_clauses                 false
% 15.87/2.48  --dbg_dump_prop_clauses_file            -
% 15.87/2.48  --dbg_out_stat                          false
% 15.87/2.48  ------ Parsing...
% 15.87/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.87/2.48  
% 15.87/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.87/2.48  
% 15.87/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.87/2.48  
% 15.87/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.87/2.48  ------ Proving...
% 15.87/2.48  ------ Problem Properties 
% 15.87/2.48  
% 15.87/2.48  
% 15.87/2.48  clauses                                 16
% 15.87/2.48  conjectures                             1
% 15.87/2.48  EPR                                     0
% 15.87/2.48  Horn                                    12
% 15.87/2.48  unary                                   5
% 15.87/2.48  binary                                  8
% 15.87/2.48  lits                                    30
% 15.87/2.48  lits eq                                 14
% 15.87/2.48  fd_pure                                 0
% 15.87/2.48  fd_pseudo                               0
% 15.87/2.48  fd_cond                                 1
% 15.87/2.48  fd_pseudo_cond                          3
% 15.87/2.48  AC symbols                              0
% 15.87/2.48  
% 15.87/2.48  ------ Schedule dynamic 5 is on 
% 15.87/2.48  
% 15.87/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.87/2.48  
% 15.87/2.48  
% 15.87/2.48  ------ 
% 15.87/2.48  Current options:
% 15.87/2.48  ------ 
% 15.87/2.48  
% 15.87/2.48  ------ Input Options
% 15.87/2.48  
% 15.87/2.48  --out_options                           all
% 15.87/2.48  --tptp_safe_out                         true
% 15.87/2.48  --problem_path                          ""
% 15.87/2.48  --include_path                          ""
% 15.87/2.48  --clausifier                            res/vclausify_rel
% 15.87/2.48  --clausifier_options                    --mode clausify
% 15.87/2.48  --stdin                                 false
% 15.87/2.48  --stats_out                             all
% 15.87/2.48  
% 15.87/2.48  ------ General Options
% 15.87/2.48  
% 15.87/2.48  --fof                                   false
% 15.87/2.48  --time_out_real                         305.
% 15.87/2.48  --time_out_virtual                      -1.
% 15.87/2.48  --symbol_type_check                     false
% 15.87/2.48  --clausify_out                          false
% 15.87/2.48  --sig_cnt_out                           false
% 15.87/2.48  --trig_cnt_out                          false
% 15.87/2.48  --trig_cnt_out_tolerance                1.
% 15.87/2.48  --trig_cnt_out_sk_spl                   false
% 15.87/2.48  --abstr_cl_out                          false
% 15.87/2.48  
% 15.87/2.48  ------ Global Options
% 15.87/2.48  
% 15.87/2.48  --schedule                              default
% 15.87/2.48  --add_important_lit                     false
% 15.87/2.48  --prop_solver_per_cl                    1000
% 15.87/2.48  --min_unsat_core                        false
% 15.87/2.48  --soft_assumptions                      false
% 15.87/2.48  --soft_lemma_size                       3
% 15.87/2.48  --prop_impl_unit_size                   0
% 15.87/2.48  --prop_impl_unit                        []
% 15.87/2.48  --share_sel_clauses                     true
% 15.87/2.48  --reset_solvers                         false
% 15.87/2.48  --bc_imp_inh                            [conj_cone]
% 15.87/2.48  --conj_cone_tolerance                   3.
% 15.87/2.48  --extra_neg_conj                        none
% 15.87/2.48  --large_theory_mode                     true
% 15.87/2.48  --prolific_symb_bound                   200
% 15.87/2.48  --lt_threshold                          2000
% 15.87/2.48  --clause_weak_htbl                      true
% 15.87/2.48  --gc_record_bc_elim                     false
% 15.87/2.48  
% 15.87/2.48  ------ Preprocessing Options
% 15.87/2.48  
% 15.87/2.48  --preprocessing_flag                    true
% 15.87/2.48  --time_out_prep_mult                    0.1
% 15.87/2.48  --splitting_mode                        input
% 15.87/2.48  --splitting_grd                         true
% 15.87/2.48  --splitting_cvd                         false
% 15.87/2.48  --splitting_cvd_svl                     false
% 15.87/2.48  --splitting_nvd                         32
% 15.87/2.48  --sub_typing                            true
% 15.87/2.48  --prep_gs_sim                           true
% 15.87/2.48  --prep_unflatten                        true
% 15.87/2.48  --prep_res_sim                          true
% 15.87/2.48  --prep_upred                            true
% 15.87/2.48  --prep_sem_filter                       exhaustive
% 15.87/2.48  --prep_sem_filter_out                   false
% 15.87/2.48  --pred_elim                             true
% 15.87/2.48  --res_sim_input                         true
% 15.87/2.48  --eq_ax_congr_red                       true
% 15.87/2.48  --pure_diseq_elim                       true
% 15.87/2.48  --brand_transform                       false
% 15.87/2.48  --non_eq_to_eq                          false
% 15.87/2.48  --prep_def_merge                        true
% 15.87/2.48  --prep_def_merge_prop_impl              false
% 15.87/2.48  --prep_def_merge_mbd                    true
% 15.87/2.48  --prep_def_merge_tr_red                 false
% 15.87/2.48  --prep_def_merge_tr_cl                  false
% 15.87/2.48  --smt_preprocessing                     true
% 15.87/2.48  --smt_ac_axioms                         fast
% 15.87/2.48  --preprocessed_out                      false
% 15.87/2.48  --preprocessed_stats                    false
% 15.87/2.48  
% 15.87/2.48  ------ Abstraction refinement Options
% 15.87/2.48  
% 15.87/2.48  --abstr_ref                             []
% 15.87/2.48  --abstr_ref_prep                        false
% 15.87/2.48  --abstr_ref_until_sat                   false
% 15.87/2.48  --abstr_ref_sig_restrict                funpre
% 15.87/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.87/2.48  --abstr_ref_under                       []
% 15.87/2.48  
% 15.87/2.48  ------ SAT Options
% 15.87/2.48  
% 15.87/2.48  --sat_mode                              false
% 15.87/2.48  --sat_fm_restart_options                ""
% 15.87/2.48  --sat_gr_def                            false
% 15.87/2.48  --sat_epr_types                         true
% 15.87/2.48  --sat_non_cyclic_types                  false
% 15.87/2.48  --sat_finite_models                     false
% 15.87/2.48  --sat_fm_lemmas                         false
% 15.87/2.48  --sat_fm_prep                           false
% 15.87/2.48  --sat_fm_uc_incr                        true
% 15.87/2.48  --sat_out_model                         small
% 15.87/2.48  --sat_out_clauses                       false
% 15.87/2.48  
% 15.87/2.48  ------ QBF Options
% 15.87/2.48  
% 15.87/2.48  --qbf_mode                              false
% 15.87/2.48  --qbf_elim_univ                         false
% 15.87/2.48  --qbf_dom_inst                          none
% 15.87/2.48  --qbf_dom_pre_inst                      false
% 15.87/2.48  --qbf_sk_in                             false
% 15.87/2.48  --qbf_pred_elim                         true
% 15.87/2.48  --qbf_split                             512
% 15.87/2.48  
% 15.87/2.48  ------ BMC1 Options
% 15.87/2.48  
% 15.87/2.48  --bmc1_incremental                      false
% 15.87/2.48  --bmc1_axioms                           reachable_all
% 15.87/2.48  --bmc1_min_bound                        0
% 15.87/2.48  --bmc1_max_bound                        -1
% 15.87/2.48  --bmc1_max_bound_default                -1
% 15.87/2.48  --bmc1_symbol_reachability              true
% 15.87/2.48  --bmc1_property_lemmas                  false
% 15.87/2.48  --bmc1_k_induction                      false
% 15.87/2.48  --bmc1_non_equiv_states                 false
% 15.87/2.48  --bmc1_deadlock                         false
% 15.87/2.48  --bmc1_ucm                              false
% 15.87/2.48  --bmc1_add_unsat_core                   none
% 15.87/2.48  --bmc1_unsat_core_children              false
% 15.87/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.87/2.48  --bmc1_out_stat                         full
% 15.87/2.48  --bmc1_ground_init                      false
% 15.87/2.48  --bmc1_pre_inst_next_state              false
% 15.87/2.48  --bmc1_pre_inst_state                   false
% 15.87/2.48  --bmc1_pre_inst_reach_state             false
% 15.87/2.48  --bmc1_out_unsat_core                   false
% 15.87/2.48  --bmc1_aig_witness_out                  false
% 15.87/2.48  --bmc1_verbose                          false
% 15.87/2.48  --bmc1_dump_clauses_tptp                false
% 15.87/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.87/2.48  --bmc1_dump_file                        -
% 15.87/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.87/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.87/2.48  --bmc1_ucm_extend_mode                  1
% 15.87/2.48  --bmc1_ucm_init_mode                    2
% 15.87/2.48  --bmc1_ucm_cone_mode                    none
% 15.87/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.87/2.48  --bmc1_ucm_relax_model                  4
% 15.87/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.87/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.87/2.48  --bmc1_ucm_layered_model                none
% 15.87/2.48  --bmc1_ucm_max_lemma_size               10
% 15.87/2.48  
% 15.87/2.48  ------ AIG Options
% 15.87/2.48  
% 15.87/2.48  --aig_mode                              false
% 15.87/2.48  
% 15.87/2.48  ------ Instantiation Options
% 15.87/2.48  
% 15.87/2.48  --instantiation_flag                    true
% 15.87/2.48  --inst_sos_flag                         false
% 15.87/2.48  --inst_sos_phase                        true
% 15.87/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.87/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.87/2.48  --inst_lit_sel_side                     none
% 15.87/2.48  --inst_solver_per_active                1400
% 15.87/2.48  --inst_solver_calls_frac                1.
% 15.87/2.48  --inst_passive_queue_type               priority_queues
% 15.87/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.87/2.48  --inst_passive_queues_freq              [25;2]
% 15.87/2.48  --inst_dismatching                      true
% 15.87/2.48  --inst_eager_unprocessed_to_passive     true
% 15.87/2.48  --inst_prop_sim_given                   true
% 15.87/2.48  --inst_prop_sim_new                     false
% 15.87/2.48  --inst_subs_new                         false
% 15.87/2.48  --inst_eq_res_simp                      false
% 15.87/2.48  --inst_subs_given                       false
% 15.87/2.48  --inst_orphan_elimination               true
% 15.87/2.48  --inst_learning_loop_flag               true
% 15.87/2.48  --inst_learning_start                   3000
% 15.87/2.48  --inst_learning_factor                  2
% 15.87/2.48  --inst_start_prop_sim_after_learn       3
% 15.87/2.48  --inst_sel_renew                        solver
% 15.87/2.48  --inst_lit_activity_flag                true
% 15.87/2.48  --inst_restr_to_given                   false
% 15.87/2.48  --inst_activity_threshold               500
% 15.87/2.48  --inst_out_proof                        true
% 15.87/2.48  
% 15.87/2.48  ------ Resolution Options
% 15.87/2.48  
% 15.87/2.48  --resolution_flag                       false
% 15.87/2.48  --res_lit_sel                           adaptive
% 15.87/2.48  --res_lit_sel_side                      none
% 15.87/2.48  --res_ordering                          kbo
% 15.87/2.48  --res_to_prop_solver                    active
% 15.87/2.48  --res_prop_simpl_new                    false
% 15.87/2.48  --res_prop_simpl_given                  true
% 15.87/2.48  --res_passive_queue_type                priority_queues
% 15.87/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.87/2.48  --res_passive_queues_freq               [15;5]
% 15.87/2.48  --res_forward_subs                      full
% 15.87/2.48  --res_backward_subs                     full
% 15.87/2.48  --res_forward_subs_resolution           true
% 15.87/2.48  --res_backward_subs_resolution          true
% 15.87/2.48  --res_orphan_elimination                true
% 15.87/2.48  --res_time_limit                        2.
% 15.87/2.48  --res_out_proof                         true
% 15.87/2.48  
% 15.87/2.48  ------ Superposition Options
% 15.87/2.48  
% 15.87/2.48  --superposition_flag                    true
% 15.87/2.48  --sup_passive_queue_type                priority_queues
% 15.87/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.87/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.87/2.48  --demod_completeness_check              fast
% 15.87/2.48  --demod_use_ground                      true
% 15.87/2.48  --sup_to_prop_solver                    passive
% 15.87/2.48  --sup_prop_simpl_new                    true
% 15.87/2.48  --sup_prop_simpl_given                  true
% 15.87/2.48  --sup_fun_splitting                     false
% 15.87/2.48  --sup_smt_interval                      50000
% 15.87/2.48  
% 15.87/2.48  ------ Superposition Simplification Setup
% 15.87/2.48  
% 15.87/2.48  --sup_indices_passive                   []
% 15.87/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.87/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.87/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.87/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.87/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.87/2.48  --sup_full_bw                           [BwDemod]
% 15.87/2.48  --sup_immed_triv                        [TrivRules]
% 15.87/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.87/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.87/2.48  --sup_immed_bw_main                     []
% 15.87/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.87/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.87/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.87/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.87/2.48  
% 15.87/2.48  ------ Combination Options
% 15.87/2.48  
% 15.87/2.48  --comb_res_mult                         3
% 15.87/2.48  --comb_sup_mult                         2
% 15.87/2.48  --comb_inst_mult                        10
% 15.87/2.48  
% 15.87/2.48  ------ Debug Options
% 15.87/2.48  
% 15.87/2.48  --dbg_backtrace                         false
% 15.87/2.48  --dbg_dump_prop_clauses                 false
% 15.87/2.48  --dbg_dump_prop_clauses_file            -
% 15.87/2.48  --dbg_out_stat                          false
% 15.87/2.48  
% 15.87/2.48  
% 15.87/2.48  
% 15.87/2.48  
% 15.87/2.48  ------ Proving...
% 15.87/2.48  
% 15.87/2.48  
% 15.87/2.48  % SZS status Theorem for theBenchmark.p
% 15.87/2.48  
% 15.87/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.87/2.48  
% 15.87/2.48  fof(f1,axiom,(
% 15.87/2.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f25,plain,(
% 15.87/2.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 15.87/2.48    inference(ennf_transformation,[],[f1])).
% 15.87/2.48  
% 15.87/2.48  fof(f31,plain,(
% 15.87/2.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 15.87/2.48    introduced(choice_axiom,[])).
% 15.87/2.48  
% 15.87/2.48  fof(f32,plain,(
% 15.87/2.48    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 15.87/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f31])).
% 15.87/2.48  
% 15.87/2.48  fof(f45,plain,(
% 15.87/2.48    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 15.87/2.48    inference(cnf_transformation,[],[f32])).
% 15.87/2.48  
% 15.87/2.48  fof(f21,axiom,(
% 15.87/2.48    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f28,plain,(
% 15.87/2.48    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 15.87/2.48    inference(ennf_transformation,[],[f21])).
% 15.87/2.48  
% 15.87/2.48  fof(f29,plain,(
% 15.87/2.48    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 15.87/2.48    inference(flattening,[],[f28])).
% 15.87/2.48  
% 15.87/2.48  fof(f43,plain,(
% 15.87/2.48    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK5(X1),k2_relat_1(X1)))),
% 15.87/2.48    introduced(choice_axiom,[])).
% 15.87/2.48  
% 15.87/2.48  fof(f44,plain,(
% 15.87/2.48    ! [X0,X1] : (r2_hidden(sK5(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 15.87/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f43])).
% 15.87/2.48  
% 15.87/2.48  fof(f71,plain,(
% 15.87/2.48    ( ! [X0,X1] : (r2_hidden(sK5(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f44])).
% 15.87/2.48  
% 15.87/2.48  fof(f20,axiom,(
% 15.87/2.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f37,plain,(
% 15.87/2.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 15.87/2.48    inference(nnf_transformation,[],[f20])).
% 15.87/2.48  
% 15.87/2.48  fof(f38,plain,(
% 15.87/2.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.87/2.48    inference(rectify,[],[f37])).
% 15.87/2.48  
% 15.87/2.48  fof(f41,plain,(
% 15.87/2.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 15.87/2.48    introduced(choice_axiom,[])).
% 15.87/2.48  
% 15.87/2.48  fof(f40,plain,(
% 15.87/2.48    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0))) )),
% 15.87/2.48    introduced(choice_axiom,[])).
% 15.87/2.48  
% 15.87/2.48  fof(f39,plain,(
% 15.87/2.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 15.87/2.48    introduced(choice_axiom,[])).
% 15.87/2.48  
% 15.87/2.48  fof(f42,plain,(
% 15.87/2.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.87/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).
% 15.87/2.48  
% 15.87/2.48  fof(f67,plain,(
% 15.87/2.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 15.87/2.48    inference(cnf_transformation,[],[f42])).
% 15.87/2.48  
% 15.87/2.48  fof(f88,plain,(
% 15.87/2.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 15.87/2.48    inference(equality_resolution,[],[f67])).
% 15.87/2.48  
% 15.87/2.48  fof(f3,axiom,(
% 15.87/2.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f26,plain,(
% 15.87/2.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 15.87/2.48    inference(ennf_transformation,[],[f3])).
% 15.87/2.48  
% 15.87/2.48  fof(f47,plain,(
% 15.87/2.48    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f26])).
% 15.87/2.48  
% 15.87/2.48  fof(f16,axiom,(
% 15.87/2.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f33,plain,(
% 15.87/2.48    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 15.87/2.48    inference(nnf_transformation,[],[f16])).
% 15.87/2.48  
% 15.87/2.48  fof(f61,plain,(
% 15.87/2.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f33])).
% 15.87/2.48  
% 15.87/2.48  fof(f9,axiom,(
% 15.87/2.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f53,plain,(
% 15.87/2.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f9])).
% 15.87/2.48  
% 15.87/2.48  fof(f10,axiom,(
% 15.87/2.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f54,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f10])).
% 15.87/2.48  
% 15.87/2.48  fof(f11,axiom,(
% 15.87/2.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f55,plain,(
% 15.87/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f11])).
% 15.87/2.48  
% 15.87/2.48  fof(f12,axiom,(
% 15.87/2.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f56,plain,(
% 15.87/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f12])).
% 15.87/2.48  
% 15.87/2.48  fof(f14,axiom,(
% 15.87/2.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f58,plain,(
% 15.87/2.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f14])).
% 15.87/2.48  
% 15.87/2.48  fof(f13,axiom,(
% 15.87/2.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f57,plain,(
% 15.87/2.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f13])).
% 15.87/2.48  
% 15.87/2.48  fof(f73,plain,(
% 15.87/2.48    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 15.87/2.48    inference(definition_unfolding,[],[f58,f57])).
% 15.87/2.48  
% 15.87/2.48  fof(f74,plain,(
% 15.87/2.48    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.87/2.48    inference(definition_unfolding,[],[f56,f73])).
% 15.87/2.48  
% 15.87/2.48  fof(f75,plain,(
% 15.87/2.48    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.87/2.48    inference(definition_unfolding,[],[f55,f74])).
% 15.87/2.48  
% 15.87/2.48  fof(f76,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.87/2.48    inference(definition_unfolding,[],[f54,f75])).
% 15.87/2.48  
% 15.87/2.48  fof(f80,plain,(
% 15.87/2.48    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 15.87/2.48    inference(definition_unfolding,[],[f53,f76])).
% 15.87/2.48  
% 15.87/2.48  fof(f82,plain,(
% 15.87/2.48    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 15.87/2.48    inference(definition_unfolding,[],[f61,f80])).
% 15.87/2.48  
% 15.87/2.48  fof(f18,axiom,(
% 15.87/2.48    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f34,plain,(
% 15.87/2.48    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 15.87/2.48    inference(nnf_transformation,[],[f18])).
% 15.87/2.48  
% 15.87/2.48  fof(f63,plain,(
% 15.87/2.48    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f34])).
% 15.87/2.48  
% 15.87/2.48  fof(f2,axiom,(
% 15.87/2.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f46,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.87/2.48    inference(cnf_transformation,[],[f2])).
% 15.87/2.48  
% 15.87/2.48  fof(f7,axiom,(
% 15.87/2.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f51,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 15.87/2.48    inference(cnf_transformation,[],[f7])).
% 15.87/2.48  
% 15.87/2.48  fof(f17,axiom,(
% 15.87/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f62,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.87/2.48    inference(cnf_transformation,[],[f17])).
% 15.87/2.48  
% 15.87/2.48  fof(f77,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 15.87/2.48    inference(definition_unfolding,[],[f62,f76])).
% 15.87/2.48  
% 15.87/2.48  fof(f78,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 15.87/2.48    inference(definition_unfolding,[],[f51,f77])).
% 15.87/2.48  
% 15.87/2.48  fof(f79,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 15.87/2.48    inference(definition_unfolding,[],[f46,f78])).
% 15.87/2.48  
% 15.87/2.48  fof(f85,plain,(
% 15.87/2.48    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 15.87/2.48    inference(definition_unfolding,[],[f63,f79,f80,f80,f80])).
% 15.87/2.48  
% 15.87/2.48  fof(f86,plain,(
% 15.87/2.48    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 15.87/2.48    inference(equality_resolution,[],[f85])).
% 15.87/2.48  
% 15.87/2.48  fof(f8,axiom,(
% 15.87/2.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f52,plain,(
% 15.87/2.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f8])).
% 15.87/2.48  
% 15.87/2.48  fof(f15,axiom,(
% 15.87/2.48    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f59,plain,(
% 15.87/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f15])).
% 15.87/2.48  
% 15.87/2.48  fof(f81,plain,(
% 15.87/2.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7)))) )),
% 15.87/2.48    inference(definition_unfolding,[],[f52,f77,f76,f59])).
% 15.87/2.48  
% 15.87/2.48  fof(f6,axiom,(
% 15.87/2.48    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f50,plain,(
% 15.87/2.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f6])).
% 15.87/2.48  
% 15.87/2.48  fof(f5,axiom,(
% 15.87/2.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f49,plain,(
% 15.87/2.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f5])).
% 15.87/2.48  
% 15.87/2.48  fof(f4,axiom,(
% 15.87/2.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f48,plain,(
% 15.87/2.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.87/2.48    inference(cnf_transformation,[],[f4])).
% 15.87/2.48  
% 15.87/2.48  fof(f19,axiom,(
% 15.87/2.48    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f24,plain,(
% 15.87/2.48    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 15.87/2.48    inference(unused_predicate_definition_removal,[],[f19])).
% 15.87/2.48  
% 15.87/2.48  fof(f27,plain,(
% 15.87/2.48    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 15.87/2.48    inference(ennf_transformation,[],[f24])).
% 15.87/2.48  
% 15.87/2.48  fof(f35,plain,(
% 15.87/2.48    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 15.87/2.48    introduced(choice_axiom,[])).
% 15.87/2.48  
% 15.87/2.48  fof(f36,plain,(
% 15.87/2.48    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 15.87/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f35])).
% 15.87/2.48  
% 15.87/2.48  fof(f65,plain,(
% 15.87/2.48    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 15.87/2.48    inference(cnf_transformation,[],[f36])).
% 15.87/2.48  
% 15.87/2.48  fof(f64,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 15.87/2.48    inference(cnf_transformation,[],[f34])).
% 15.87/2.48  
% 15.87/2.48  fof(f84,plain,(
% 15.87/2.48    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 15.87/2.48    inference(definition_unfolding,[],[f64,f79,f80,f80,f80])).
% 15.87/2.48  
% 15.87/2.48  fof(f22,conjecture,(
% 15.87/2.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 15.87/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.87/2.48  
% 15.87/2.48  fof(f23,negated_conjecture,(
% 15.87/2.48    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 15.87/2.48    inference(negated_conjecture,[],[f22])).
% 15.87/2.48  
% 15.87/2.48  fof(f30,plain,(
% 15.87/2.48    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 15.87/2.48    inference(ennf_transformation,[],[f23])).
% 15.87/2.48  
% 15.87/2.48  fof(f72,plain,(
% 15.87/2.48    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 15.87/2.48    inference(cnf_transformation,[],[f30])).
% 15.87/2.48  
% 15.87/2.48  cnf(c_1,plain,
% 15.87/2.48      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 15.87/2.48      inference(cnf_transformation,[],[f45]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_521,plain,
% 15.87/2.48      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 15.87/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_16,plain,
% 15.87/2.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.87/2.48      | r2_hidden(sK5(X1),k2_relat_1(X1))
% 15.87/2.48      | ~ v1_relat_1(X1) ),
% 15.87/2.48      inference(cnf_transformation,[],[f71]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_514,plain,
% 15.87/2.48      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 15.87/2.48      | r2_hidden(sK5(X1),k2_relat_1(X1)) = iProver_top
% 15.87/2.48      | v1_relat_1(X1) != iProver_top ),
% 15.87/2.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_1543,plain,
% 15.87/2.48      ( k1_relat_1(X0) = k1_xboole_0
% 15.87/2.48      | r2_hidden(sK5(X0),k2_relat_1(X0)) = iProver_top
% 15.87/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.87/2.48      inference(superposition,[status(thm)],[c_521,c_514]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_15,plain,
% 15.87/2.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.87/2.48      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
% 15.87/2.48      inference(cnf_transformation,[],[f88]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_515,plain,
% 15.87/2.48      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 15.87/2.48      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
% 15.87/2.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_2,plain,
% 15.87/2.48      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.87/2.48      inference(cnf_transformation,[],[f47]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_6,plain,
% 15.87/2.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 15.87/2.48      | ~ r2_hidden(X0,X1) ),
% 15.87/2.48      inference(cnf_transformation,[],[f82]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_110,plain,
% 15.87/2.48      ( ~ r2_hidden(X0,X1)
% 15.87/2.48      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 15.87/2.48      inference(prop_impl,[status(thm)],[c_6]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_111,plain,
% 15.87/2.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 15.87/2.48      | ~ r2_hidden(X0,X1) ),
% 15.87/2.48      inference(renaming,[status(thm)],[c_110]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_190,plain,
% 15.87/2.48      ( ~ r2_hidden(X0,X1)
% 15.87/2.48      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X2
% 15.87/2.48      | k1_xboole_0 != X1
% 15.87/2.48      | k1_xboole_0 = X2 ),
% 15.87/2.48      inference(resolution_lifted,[status(thm)],[c_2,c_111]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_191,plain,
% 15.87/2.48      ( ~ r2_hidden(X0,k1_xboole_0)
% 15.87/2.48      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 15.87/2.48      inference(unflattening,[status(thm)],[c_190]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_513,plain,
% 15.87/2.48      ( k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 15.87/2.48      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.87/2.48      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_3253,plain,
% 15.87/2.48      ( k6_enumset1(k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0),k4_tarski(sK4(k1_xboole_0,X0),X0)) = k1_xboole_0
% 15.87/2.48      | r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 15.87/2.48      inference(superposition,[status(thm)],[c_515,c_513]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_9,plain,
% 15.87/2.48      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 15.87/2.48      inference(cnf_transformation,[],[f86]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_0,plain,
% 15.87/2.48      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 15.87/2.48      inference(cnf_transformation,[],[f81]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_5,plain,
% 15.87/2.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.87/2.48      inference(cnf_transformation,[],[f50]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_576,plain,
% 15.87/2.48      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 15.87/2.48      inference(demodulation,[status(thm)],[c_9,c_0,c_5]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_4,plain,
% 15.87/2.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.87/2.48      inference(cnf_transformation,[],[f49]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_619,plain,
% 15.87/2.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.87/2.48      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_617,plain,
% 15.87/2.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.87/2.48      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_758,plain,
% 15.87/2.48      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 15.87/2.48      inference(superposition,[status(thm)],[c_5,c_617]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_3,plain,
% 15.87/2.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.87/2.48      inference(cnf_transformation,[],[f48]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_782,plain,
% 15.87/2.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.87/2.48      inference(light_normalisation,[status(thm)],[c_758,c_3]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_783,plain,
% 15.87/2.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 15.87/2.48      inference(demodulation,[status(thm)],[c_782,c_617]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_1070,plain,
% 15.87/2.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 15.87/2.48      inference(superposition,[status(thm)],[c_619,c_783]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_1085,plain,
% 15.87/2.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 15.87/2.48      inference(demodulation,[status(thm)],[c_1070,c_3]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_18667,plain,
% 15.87/2.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 15.87/2.48      inference(demodulation,[status(thm)],[c_576,c_1085]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_72431,plain,
% 15.87/2.48      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 15.87/2.48      inference(forward_subsumption_resolution,
% 15.87/2.48                [status(thm)],
% 15.87/2.48                [c_3253,c_18667]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_72440,plain,
% 15.87/2.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 15.87/2.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.87/2.48      inference(superposition,[status(thm)],[c_1543,c_72431]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_72435,plain,
% 15.87/2.48      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.87/2.48      inference(superposition,[status(thm)],[c_521,c_72431]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_11,plain,
% 15.87/2.48      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 15.87/2.48      inference(cnf_transformation,[],[f65]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_519,plain,
% 15.87/2.48      ( r2_hidden(sK1(X0),X0) = iProver_top
% 15.87/2.48      | v1_relat_1(X0) = iProver_top ),
% 15.87/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_1061,plain,
% 15.87/2.48      ( k6_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0)) = k1_xboole_0
% 15.87/2.48      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 15.87/2.48      inference(superposition,[status(thm)],[c_519,c_513]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_29549,plain,
% 15.87/2.48      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 15.87/2.48      inference(forward_subsumption_resolution,
% 15.87/2.48                [status(thm)],
% 15.87/2.48                [c_1061,c_18667]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_345,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_752,plain,
% 15.87/2.48      ( k2_relat_1(k1_xboole_0) != X0
% 15.87/2.48      | k1_xboole_0 != X0
% 15.87/2.48      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 15.87/2.48      inference(instantiation,[status(thm)],[c_345]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_753,plain,
% 15.87/2.48      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 15.87/2.48      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 15.87/2.48      | k1_xboole_0 != k1_xboole_0 ),
% 15.87/2.48      inference(instantiation,[status(thm)],[c_752]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_610,plain,
% 15.87/2.48      ( k1_relat_1(k1_xboole_0) != X0
% 15.87/2.48      | k1_xboole_0 != X0
% 15.87/2.48      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 15.87/2.48      inference(instantiation,[status(thm)],[c_345]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_611,plain,
% 15.87/2.48      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 15.87/2.48      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 15.87/2.48      | k1_xboole_0 != k1_xboole_0 ),
% 15.87/2.48      inference(instantiation,[status(thm)],[c_610]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_8,plain,
% 15.87/2.48      ( X0 = X1
% 15.87/2.48      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 15.87/2.48      inference(cnf_transformation,[],[f84]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_40,plain,
% 15.87/2.48      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 15.87/2.48      | k1_xboole_0 = k1_xboole_0 ),
% 15.87/2.48      inference(instantiation,[status(thm)],[c_8]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_39,plain,
% 15.87/2.48      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k5_xboole_0(k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 15.87/2.48      inference(instantiation,[status(thm)],[c_9]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(c_17,negated_conjecture,
% 15.87/2.48      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
% 15.87/2.48      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 15.87/2.48      inference(cnf_transformation,[],[f72]) ).
% 15.87/2.48  
% 15.87/2.48  cnf(contradiction,plain,
% 15.87/2.48      ( $false ),
% 15.87/2.48      inference(minisat,
% 15.87/2.48                [status(thm)],
% 15.87/2.48                [c_72440,c_72435,c_29549,c_753,c_611,c_40,c_39,c_17]) ).
% 15.87/2.48  
% 15.87/2.48  
% 15.87/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.87/2.48  
% 15.87/2.48  ------                               Statistics
% 15.87/2.48  
% 15.87/2.48  ------ General
% 15.87/2.48  
% 15.87/2.48  abstr_ref_over_cycles:                  0
% 15.87/2.48  abstr_ref_under_cycles:                 0
% 15.87/2.48  gc_basic_clause_elim:                   0
% 15.87/2.48  forced_gc_time:                         0
% 15.87/2.48  parsing_time:                           0.008
% 15.87/2.48  unif_index_cands_time:                  0.
% 15.87/2.48  unif_index_add_time:                    0.
% 15.87/2.48  orderings_time:                         0.
% 15.87/2.48  out_proof_time:                         0.008
% 15.87/2.48  total_time:                             1.994
% 15.87/2.48  num_of_symbols:                         47
% 15.87/2.48  num_of_terms:                           87855
% 15.87/2.48  
% 15.87/2.48  ------ Preprocessing
% 15.87/2.48  
% 15.87/2.48  num_of_splits:                          0
% 15.87/2.48  num_of_split_atoms:                     0
% 15.87/2.48  num_of_reused_defs:                     0
% 15.87/2.48  num_eq_ax_congr_red:                    30
% 15.87/2.48  num_of_sem_filtered_clauses:            1
% 15.87/2.48  num_of_subtypes:                        0
% 15.87/2.48  monotx_restored_types:                  0
% 15.87/2.48  sat_num_of_epr_types:                   0
% 15.87/2.48  sat_num_of_non_cyclic_types:            0
% 15.87/2.48  sat_guarded_non_collapsed_types:        0
% 15.87/2.48  num_pure_diseq_elim:                    0
% 15.87/2.48  simp_replaced_by:                       0
% 15.87/2.48  res_preprocessed:                       85
% 15.87/2.48  prep_upred:                             0
% 15.87/2.48  prep_unflattend:                        6
% 15.87/2.48  smt_new_axioms:                         0
% 15.87/2.48  pred_elim_cands:                        2
% 15.87/2.48  pred_elim:                              1
% 15.87/2.48  pred_elim_cl:                           2
% 15.87/2.48  pred_elim_cycles:                       3
% 15.87/2.48  merged_defs:                            2
% 15.87/2.48  merged_defs_ncl:                        0
% 15.87/2.48  bin_hyper_res:                          2
% 15.87/2.48  prep_cycles:                            4
% 15.87/2.48  pred_elim_time:                         0.001
% 15.87/2.48  splitting_time:                         0.
% 15.87/2.48  sem_filter_time:                        0.
% 15.87/2.48  monotx_time:                            0.
% 15.87/2.48  subtype_inf_time:                       0.
% 15.87/2.48  
% 15.87/2.48  ------ Problem properties
% 15.87/2.48  
% 15.87/2.48  clauses:                                16
% 15.87/2.48  conjectures:                            1
% 15.87/2.48  epr:                                    0
% 15.87/2.48  horn:                                   12
% 15.87/2.48  ground:                                 1
% 15.87/2.48  unary:                                  5
% 15.87/2.48  binary:                                 8
% 15.87/2.48  lits:                                   30
% 15.87/2.48  lits_eq:                                14
% 15.87/2.48  fd_pure:                                0
% 15.87/2.48  fd_pseudo:                              0
% 15.87/2.48  fd_cond:                                1
% 15.87/2.48  fd_pseudo_cond:                         3
% 15.87/2.48  ac_symbols:                             1
% 15.87/2.48  
% 15.87/2.48  ------ Propositional Solver
% 15.87/2.48  
% 15.87/2.48  prop_solver_calls:                      30
% 15.87/2.48  prop_fast_solver_calls:                 569
% 15.87/2.48  smt_solver_calls:                       0
% 15.87/2.48  smt_fast_solver_calls:                  0
% 15.87/2.48  prop_num_of_clauses:                    8508
% 15.87/2.48  prop_preprocess_simplified:             10876
% 15.87/2.48  prop_fo_subsumed:                       0
% 15.87/2.48  prop_solver_time:                       0.
% 15.87/2.48  smt_solver_time:                        0.
% 15.87/2.48  smt_fast_solver_time:                   0.
% 15.87/2.48  prop_fast_solver_time:                  0.
% 15.87/2.48  prop_unsat_core_time:                   0.
% 15.87/2.48  
% 15.87/2.48  ------ QBF
% 15.87/2.48  
% 15.87/2.48  qbf_q_res:                              0
% 15.87/2.48  qbf_num_tautologies:                    0
% 15.87/2.48  qbf_prep_cycles:                        0
% 15.87/2.48  
% 15.87/2.48  ------ BMC1
% 15.87/2.48  
% 15.87/2.48  bmc1_current_bound:                     -1
% 15.87/2.48  bmc1_last_solved_bound:                 -1
% 15.87/2.48  bmc1_unsat_core_size:                   -1
% 15.87/2.48  bmc1_unsat_core_parents_size:           -1
% 15.87/2.48  bmc1_merge_next_fun:                    0
% 15.87/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.87/2.48  
% 15.87/2.48  ------ Instantiation
% 15.87/2.48  
% 15.87/2.48  inst_num_of_clauses:                    1047
% 15.87/2.48  inst_num_in_passive:                    691
% 15.87/2.48  inst_num_in_active:                     274
% 15.87/2.48  inst_num_in_unprocessed:                84
% 15.87/2.48  inst_num_of_loops:                      630
% 15.87/2.48  inst_num_of_learning_restarts:          0
% 15.87/2.48  inst_num_moves_active_passive:          351
% 15.87/2.48  inst_lit_activity:                      0
% 15.87/2.48  inst_lit_activity_moves:                0
% 15.87/2.48  inst_num_tautologies:                   0
% 15.87/2.48  inst_num_prop_implied:                  0
% 15.87/2.48  inst_num_existing_simplified:           0
% 15.87/2.48  inst_num_eq_res_simplified:             0
% 15.87/2.48  inst_num_child_elim:                    0
% 15.87/2.48  inst_num_of_dismatching_blockings:      389
% 15.87/2.48  inst_num_of_non_proper_insts:           985
% 15.87/2.48  inst_num_of_duplicates:                 0
% 15.87/2.48  inst_inst_num_from_inst_to_res:         0
% 15.87/2.48  inst_dismatching_checking_time:         0.
% 15.87/2.48  
% 15.87/2.48  ------ Resolution
% 15.87/2.48  
% 15.87/2.48  res_num_of_clauses:                     0
% 15.87/2.48  res_num_in_passive:                     0
% 15.87/2.48  res_num_in_active:                      0
% 15.87/2.48  res_num_of_loops:                       89
% 15.87/2.48  res_forward_subset_subsumed:            86
% 15.87/2.48  res_backward_subset_subsumed:           6
% 15.87/2.48  res_forward_subsumed:                   0
% 15.87/2.48  res_backward_subsumed:                  0
% 15.87/2.48  res_forward_subsumption_resolution:     0
% 15.87/2.48  res_backward_subsumption_resolution:    0
% 15.87/2.48  res_clause_to_clause_subsumption:       478056
% 15.87/2.48  res_orphan_elimination:                 0
% 15.87/2.48  res_tautology_del:                      102
% 15.87/2.48  res_num_eq_res_simplified:              0
% 15.87/2.48  res_num_sel_changes:                    0
% 15.87/2.48  res_moves_from_active_to_pass:          0
% 15.87/2.48  
% 15.87/2.48  ------ Superposition
% 15.87/2.48  
% 15.87/2.48  sup_time_total:                         0.
% 15.87/2.48  sup_time_generating:                    0.
% 15.87/2.48  sup_time_sim_full:                      0.
% 15.87/2.48  sup_time_sim_immed:                     0.
% 15.87/2.48  
% 15.87/2.48  sup_num_of_clauses:                     4930
% 15.87/2.48  sup_num_in_active:                      108
% 15.87/2.48  sup_num_in_passive:                     4822
% 15.87/2.48  sup_num_of_loops:                       125
% 15.87/2.48  sup_fw_superposition:                   17764
% 15.87/2.48  sup_bw_superposition:                   12558
% 15.87/2.48  sup_immediate_simplified:               11815
% 15.87/2.48  sup_given_eliminated:                   9
% 15.87/2.48  comparisons_done:                       0
% 15.87/2.48  comparisons_avoided:                    0
% 15.87/2.48  
% 15.87/2.48  ------ Simplifications
% 15.87/2.48  
% 15.87/2.48  
% 15.87/2.48  sim_fw_subset_subsumed:                 0
% 15.87/2.48  sim_bw_subset_subsumed:                 0
% 15.87/2.48  sim_fw_subsumed:                        609
% 15.87/2.48  sim_bw_subsumed:                        2
% 15.87/2.48  sim_fw_subsumption_res:                 2
% 15.87/2.48  sim_bw_subsumption_res:                 0
% 15.87/2.48  sim_tautology_del:                      1
% 15.87/2.48  sim_eq_tautology_del:                   1952
% 15.87/2.48  sim_eq_res_simp:                        0
% 15.87/2.48  sim_fw_demodulated:                     6847
% 15.87/2.48  sim_bw_demodulated:                     1247
% 15.87/2.48  sim_light_normalised:                   5020
% 15.87/2.48  sim_joinable_taut:                      791
% 15.87/2.48  sim_joinable_simp:                      0
% 15.87/2.48  sim_ac_normalised:                      0
% 15.87/2.48  sim_smt_subsumption:                    0
% 15.87/2.48  
%------------------------------------------------------------------------------
