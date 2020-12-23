%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:37 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 518 expanded)
%              Number of clauses        :   47 (  57 expanded)
%              Number of leaves         :   27 ( 161 expanded)
%              Depth                    :   16
%              Number of atoms          :  262 ( 709 expanded)
%              Number of equality atoms :  181 ( 583 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f68])).

fof(f70,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f60,f73,f74,f74,f74])).

fof(f89,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(definition_unfolding,[],[f51,f71,f58,f74])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f74])).

fof(f88,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f38,f71])).

fof(f19,axiom,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f61,f73,f74,f74,f74])).

fof(f21,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f21])).

fof(f26,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f22])).

fof(f36,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK2)) != sK2 ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    k1_setfam_1(k1_tarski(sK2)) != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f36])).

fof(f65,plain,(
    k1_setfam_1(k1_tarski(sK2)) != sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != sK2 ),
    inference(definition_unfolding,[],[f65,f74])).

cnf(c_161,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7492,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),X2))
    | X2 != X0
    | sK1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_7494,plain,
    ( r1_tarski(sK2,sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK2))
    | ~ r1_tarski(sK2,sK2)
    | sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK2) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7492])).

cnf(c_158,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_615,plain,
    ( X0 != X1
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_1315,plain,
    ( X0 != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_5748,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | k1_xboole_0 != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_5750,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | k1_xboole_0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5748])).

cnf(c_13,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_0,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_377,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_13,c_0,c_7])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_442,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_1041,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_442])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1065,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1041,c_5])).

cnf(c_2746,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_377,c_7,c_1065])).

cnf(c_2748,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2746])).

cnf(c_16,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_316,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_319,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_865,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X0
    | r1_tarski(X1,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_319])).

cnf(c_867,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK2) = sK2
    | r1_tarski(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_14,plain,
    ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_318,plain,
    ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_737,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_318])).

cnf(c_745,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_737])).

cnf(c_747,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_746,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,sK1(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_665,plain,
    ( ~ r1_tarski(X0,sK1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0))
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
    | k1_xboole_0 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_667,plain,
    ( ~ r1_tarski(sK2,sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK2))
    | r1_tarski(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_412,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2)
    | ~ r1_tarski(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_413,plain,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK2
    | r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_159,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_165,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_45,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_28,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_27,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_17,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7494,c_5750,c_2748,c_867,c_747,c_746,c_667,c_413,c_412,c_165,c_45,c_28,c_27,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:47:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.72/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.98  
% 3.72/0.98  ------  iProver source info
% 3.72/0.98  
% 3.72/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.98  git: non_committed_changes: false
% 3.72/0.98  git: last_make_outside_of_git: false
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options
% 3.72/0.98  
% 3.72/0.98  --out_options                           all
% 3.72/0.98  --tptp_safe_out                         true
% 3.72/0.98  --problem_path                          ""
% 3.72/0.98  --include_path                          ""
% 3.72/0.98  --clausifier                            res/vclausify_rel
% 3.72/0.98  --clausifier_options                    --mode clausify
% 3.72/0.98  --stdin                                 false
% 3.72/0.98  --stats_out                             sel
% 3.72/0.98  
% 3.72/0.98  ------ General Options
% 3.72/0.98  
% 3.72/0.98  --fof                                   false
% 3.72/0.98  --time_out_real                         604.99
% 3.72/0.98  --time_out_virtual                      -1.
% 3.72/0.98  --symbol_type_check                     false
% 3.72/0.98  --clausify_out                          false
% 3.72/0.98  --sig_cnt_out                           false
% 3.72/0.98  --trig_cnt_out                          false
% 3.72/0.98  --trig_cnt_out_tolerance                1.
% 3.72/0.98  --trig_cnt_out_sk_spl                   false
% 3.72/0.98  --abstr_cl_out                          false
% 3.72/0.98  
% 3.72/0.98  ------ Global Options
% 3.72/0.98  
% 3.72/0.98  --schedule                              none
% 3.72/0.98  --add_important_lit                     false
% 3.72/0.98  --prop_solver_per_cl                    1000
% 3.72/0.98  --min_unsat_core                        false
% 3.72/0.98  --soft_assumptions                      false
% 3.72/0.98  --soft_lemma_size                       3
% 3.72/0.98  --prop_impl_unit_size                   0
% 3.72/0.98  --prop_impl_unit                        []
% 3.72/0.98  --share_sel_clauses                     true
% 3.72/0.98  --reset_solvers                         false
% 3.72/0.98  --bc_imp_inh                            [conj_cone]
% 3.72/0.98  --conj_cone_tolerance                   3.
% 3.72/0.98  --extra_neg_conj                        none
% 3.72/0.98  --large_theory_mode                     true
% 3.72/0.98  --prolific_symb_bound                   200
% 3.72/0.98  --lt_threshold                          2000
% 3.72/0.98  --clause_weak_htbl                      true
% 3.72/0.98  --gc_record_bc_elim                     false
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing Options
% 3.72/0.98  
% 3.72/0.98  --preprocessing_flag                    true
% 3.72/0.98  --time_out_prep_mult                    0.1
% 3.72/0.98  --splitting_mode                        input
% 3.72/0.98  --splitting_grd                         true
% 3.72/0.98  --splitting_cvd                         false
% 3.72/0.98  --splitting_cvd_svl                     false
% 3.72/0.98  --splitting_nvd                         32
% 3.72/0.98  --sub_typing                            true
% 3.72/0.98  --prep_gs_sim                           false
% 3.72/0.98  --prep_unflatten                        true
% 3.72/0.98  --prep_res_sim                          true
% 3.72/0.98  --prep_upred                            true
% 3.72/0.98  --prep_sem_filter                       exhaustive
% 3.72/0.98  --prep_sem_filter_out                   false
% 3.72/0.98  --pred_elim                             false
% 3.72/0.98  --res_sim_input                         true
% 3.72/0.98  --eq_ax_congr_red                       true
% 3.72/0.98  --pure_diseq_elim                       true
% 3.72/0.98  --brand_transform                       false
% 3.72/0.98  --non_eq_to_eq                          false
% 3.72/0.98  --prep_def_merge                        true
% 3.72/0.98  --prep_def_merge_prop_impl              false
% 3.72/0.98  --prep_def_merge_mbd                    true
% 3.72/0.98  --prep_def_merge_tr_red                 false
% 3.72/0.98  --prep_def_merge_tr_cl                  false
% 3.72/0.98  --smt_preprocessing                     true
% 3.72/0.98  --smt_ac_axioms                         fast
% 3.72/0.98  --preprocessed_out                      false
% 3.72/0.98  --preprocessed_stats                    false
% 3.72/0.98  
% 3.72/0.98  ------ Abstraction refinement Options
% 3.72/0.98  
% 3.72/0.98  --abstr_ref                             []
% 3.72/0.98  --abstr_ref_prep                        false
% 3.72/0.98  --abstr_ref_until_sat                   false
% 3.72/0.98  --abstr_ref_sig_restrict                funpre
% 3.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.98  --abstr_ref_under                       []
% 3.72/0.98  
% 3.72/0.98  ------ SAT Options
% 3.72/0.98  
% 3.72/0.98  --sat_mode                              false
% 3.72/0.98  --sat_fm_restart_options                ""
% 3.72/0.98  --sat_gr_def                            false
% 3.72/0.98  --sat_epr_types                         true
% 3.72/0.98  --sat_non_cyclic_types                  false
% 3.72/0.98  --sat_finite_models                     false
% 3.72/0.98  --sat_fm_lemmas                         false
% 3.72/0.98  --sat_fm_prep                           false
% 3.72/0.98  --sat_fm_uc_incr                        true
% 3.72/0.98  --sat_out_model                         small
% 3.72/0.98  --sat_out_clauses                       false
% 3.72/0.98  
% 3.72/0.98  ------ QBF Options
% 3.72/0.98  
% 3.72/0.98  --qbf_mode                              false
% 3.72/0.98  --qbf_elim_univ                         false
% 3.72/0.98  --qbf_dom_inst                          none
% 3.72/0.98  --qbf_dom_pre_inst                      false
% 3.72/0.98  --qbf_sk_in                             false
% 3.72/0.98  --qbf_pred_elim                         true
% 3.72/0.98  --qbf_split                             512
% 3.72/0.98  
% 3.72/0.98  ------ BMC1 Options
% 3.72/0.98  
% 3.72/0.98  --bmc1_incremental                      false
% 3.72/0.98  --bmc1_axioms                           reachable_all
% 3.72/0.98  --bmc1_min_bound                        0
% 3.72/0.98  --bmc1_max_bound                        -1
% 3.72/0.98  --bmc1_max_bound_default                -1
% 3.72/0.98  --bmc1_symbol_reachability              true
% 3.72/0.98  --bmc1_property_lemmas                  false
% 3.72/0.98  --bmc1_k_induction                      false
% 3.72/0.98  --bmc1_non_equiv_states                 false
% 3.72/0.98  --bmc1_deadlock                         false
% 3.72/0.98  --bmc1_ucm                              false
% 3.72/0.98  --bmc1_add_unsat_core                   none
% 3.72/0.98  --bmc1_unsat_core_children              false
% 3.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.98  --bmc1_out_stat                         full
% 3.72/0.98  --bmc1_ground_init                      false
% 3.72/0.98  --bmc1_pre_inst_next_state              false
% 3.72/0.98  --bmc1_pre_inst_state                   false
% 3.72/0.98  --bmc1_pre_inst_reach_state             false
% 3.72/0.98  --bmc1_out_unsat_core                   false
% 3.72/0.98  --bmc1_aig_witness_out                  false
% 3.72/0.98  --bmc1_verbose                          false
% 3.72/0.98  --bmc1_dump_clauses_tptp                false
% 3.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.98  --bmc1_dump_file                        -
% 3.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.98  --bmc1_ucm_extend_mode                  1
% 3.72/0.98  --bmc1_ucm_init_mode                    2
% 3.72/0.98  --bmc1_ucm_cone_mode                    none
% 3.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.98  --bmc1_ucm_relax_model                  4
% 3.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.98  --bmc1_ucm_layered_model                none
% 3.72/0.98  --bmc1_ucm_max_lemma_size               10
% 3.72/0.98  
% 3.72/0.98  ------ AIG Options
% 3.72/0.98  
% 3.72/0.98  --aig_mode                              false
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation Options
% 3.72/0.98  
% 3.72/0.98  --instantiation_flag                    true
% 3.72/0.98  --inst_sos_flag                         false
% 3.72/0.98  --inst_sos_phase                        true
% 3.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel_side                     num_symb
% 3.72/0.98  --inst_solver_per_active                1400
% 3.72/0.98  --inst_solver_calls_frac                1.
% 3.72/0.98  --inst_passive_queue_type               priority_queues
% 3.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.98  --inst_passive_queues_freq              [25;2]
% 3.72/0.98  --inst_dismatching                      true
% 3.72/0.98  --inst_eager_unprocessed_to_passive     true
% 3.72/0.98  --inst_prop_sim_given                   true
% 3.72/0.98  --inst_prop_sim_new                     false
% 3.72/0.98  --inst_subs_new                         false
% 3.72/0.98  --inst_eq_res_simp                      false
% 3.72/0.98  --inst_subs_given                       false
% 3.72/0.98  --inst_orphan_elimination               true
% 3.72/0.98  --inst_learning_loop_flag               true
% 3.72/0.98  --inst_learning_start                   3000
% 3.72/0.98  --inst_learning_factor                  2
% 3.72/0.98  --inst_start_prop_sim_after_learn       3
% 3.72/0.98  --inst_sel_renew                        solver
% 3.72/0.98  --inst_lit_activity_flag                true
% 3.72/0.98  --inst_restr_to_given                   false
% 3.72/0.98  --inst_activity_threshold               500
% 3.72/0.98  --inst_out_proof                        true
% 3.72/0.98  
% 3.72/0.98  ------ Resolution Options
% 3.72/0.98  
% 3.72/0.98  --resolution_flag                       true
% 3.72/0.98  --res_lit_sel                           adaptive
% 3.72/0.98  --res_lit_sel_side                      none
% 3.72/0.98  --res_ordering                          kbo
% 3.72/0.98  --res_to_prop_solver                    active
% 3.72/0.98  --res_prop_simpl_new                    false
% 3.72/0.98  --res_prop_simpl_given                  true
% 3.72/0.98  --res_passive_queue_type                priority_queues
% 3.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.98  --res_passive_queues_freq               [15;5]
% 3.72/0.98  --res_forward_subs                      full
% 3.72/0.98  --res_backward_subs                     full
% 3.72/0.98  --res_forward_subs_resolution           true
% 3.72/0.98  --res_backward_subs_resolution          true
% 3.72/0.98  --res_orphan_elimination                true
% 3.72/0.98  --res_time_limit                        2.
% 3.72/0.98  --res_out_proof                         true
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Options
% 3.72/0.98  
% 3.72/0.98  --superposition_flag                    true
% 3.72/0.98  --sup_passive_queue_type                priority_queues
% 3.72/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.98  --sup_passive_queues_freq               [1;4]
% 3.72/0.98  --demod_completeness_check              fast
% 3.72/0.98  --demod_use_ground                      true
% 3.72/0.98  --sup_to_prop_solver                    passive
% 3.72/0.98  --sup_prop_simpl_new                    true
% 3.72/0.98  --sup_prop_simpl_given                  true
% 3.72/0.98  --sup_fun_splitting                     false
% 3.72/0.98  --sup_smt_interval                      50000
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Simplification Setup
% 3.72/0.98  
% 3.72/0.98  --sup_indices_passive                   []
% 3.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_full_bw                           [BwDemod]
% 3.72/0.98  --sup_immed_triv                        [TrivRules]
% 3.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_immed_bw_main                     []
% 3.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  
% 3.72/0.98  ------ Combination Options
% 3.72/0.98  
% 3.72/0.98  --comb_res_mult                         3
% 3.72/0.98  --comb_sup_mult                         2
% 3.72/0.98  --comb_inst_mult                        10
% 3.72/0.98  
% 3.72/0.98  ------ Debug Options
% 3.72/0.98  
% 3.72/0.98  --dbg_backtrace                         false
% 3.72/0.98  --dbg_dump_prop_clauses                 false
% 3.72/0.98  --dbg_dump_prop_clauses_file            -
% 3.72/0.98  --dbg_out_stat                          false
% 3.72/0.98  ------ Parsing...
% 3.72/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  ------ Proving...
% 3.72/0.98  ------ Problem Properties 
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  clauses                                 17
% 3.72/0.98  conjectures                             1
% 3.72/0.98  EPR                                     2
% 3.72/0.98  Horn                                    13
% 3.72/0.98  unary                                   10
% 3.72/0.98  binary                                  2
% 3.72/0.98  lits                                    29
% 3.72/0.98  lits eq                                 17
% 3.72/0.98  fd_pure                                 0
% 3.72/0.98  fd_pseudo                               0
% 3.72/0.98  fd_cond                                 2
% 3.72/0.98  fd_pseudo_cond                          4
% 3.72/0.98  AC symbols                              0
% 3.72/0.98  
% 3.72/0.98  ------ Input Options Time Limit: Unbounded
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  Current options:
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options
% 3.72/0.98  
% 3.72/0.98  --out_options                           all
% 3.72/0.98  --tptp_safe_out                         true
% 3.72/0.98  --problem_path                          ""
% 3.72/0.98  --include_path                          ""
% 3.72/0.98  --clausifier                            res/vclausify_rel
% 3.72/0.98  --clausifier_options                    --mode clausify
% 3.72/0.98  --stdin                                 false
% 3.72/0.98  --stats_out                             sel
% 3.72/0.98  
% 3.72/0.98  ------ General Options
% 3.72/0.98  
% 3.72/0.98  --fof                                   false
% 3.72/0.98  --time_out_real                         604.99
% 3.72/0.98  --time_out_virtual                      -1.
% 3.72/0.98  --symbol_type_check                     false
% 3.72/0.98  --clausify_out                          false
% 3.72/0.98  --sig_cnt_out                           false
% 3.72/0.98  --trig_cnt_out                          false
% 3.72/0.98  --trig_cnt_out_tolerance                1.
% 3.72/0.98  --trig_cnt_out_sk_spl                   false
% 3.72/0.98  --abstr_cl_out                          false
% 3.72/0.98  
% 3.72/0.98  ------ Global Options
% 3.72/0.98  
% 3.72/0.98  --schedule                              none
% 3.72/0.98  --add_important_lit                     false
% 3.72/0.98  --prop_solver_per_cl                    1000
% 3.72/0.98  --min_unsat_core                        false
% 3.72/0.98  --soft_assumptions                      false
% 3.72/0.98  --soft_lemma_size                       3
% 3.72/0.98  --prop_impl_unit_size                   0
% 3.72/0.98  --prop_impl_unit                        []
% 3.72/0.98  --share_sel_clauses                     true
% 3.72/0.98  --reset_solvers                         false
% 3.72/0.98  --bc_imp_inh                            [conj_cone]
% 3.72/0.98  --conj_cone_tolerance                   3.
% 3.72/0.98  --extra_neg_conj                        none
% 3.72/0.98  --large_theory_mode                     true
% 3.72/0.98  --prolific_symb_bound                   200
% 3.72/0.98  --lt_threshold                          2000
% 3.72/0.98  --clause_weak_htbl                      true
% 3.72/0.98  --gc_record_bc_elim                     false
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing Options
% 3.72/0.98  
% 3.72/0.98  --preprocessing_flag                    true
% 3.72/0.98  --time_out_prep_mult                    0.1
% 3.72/0.98  --splitting_mode                        input
% 3.72/0.98  --splitting_grd                         true
% 3.72/0.98  --splitting_cvd                         false
% 3.72/0.98  --splitting_cvd_svl                     false
% 3.72/0.98  --splitting_nvd                         32
% 3.72/0.98  --sub_typing                            true
% 3.72/0.98  --prep_gs_sim                           false
% 3.72/0.98  --prep_unflatten                        true
% 3.72/0.98  --prep_res_sim                          true
% 3.72/0.98  --prep_upred                            true
% 3.72/0.98  --prep_sem_filter                       exhaustive
% 3.72/0.98  --prep_sem_filter_out                   false
% 3.72/0.98  --pred_elim                             false
% 3.72/0.98  --res_sim_input                         true
% 3.72/0.98  --eq_ax_congr_red                       true
% 3.72/0.98  --pure_diseq_elim                       true
% 3.72/0.98  --brand_transform                       false
% 3.72/0.98  --non_eq_to_eq                          false
% 3.72/0.98  --prep_def_merge                        true
% 3.72/0.98  --prep_def_merge_prop_impl              false
% 3.72/0.98  --prep_def_merge_mbd                    true
% 3.72/0.98  --prep_def_merge_tr_red                 false
% 3.72/0.98  --prep_def_merge_tr_cl                  false
% 3.72/0.98  --smt_preprocessing                     true
% 3.72/0.98  --smt_ac_axioms                         fast
% 3.72/0.98  --preprocessed_out                      false
% 3.72/0.98  --preprocessed_stats                    false
% 3.72/0.98  
% 3.72/0.98  ------ Abstraction refinement Options
% 3.72/0.98  
% 3.72/0.98  --abstr_ref                             []
% 3.72/0.98  --abstr_ref_prep                        false
% 3.72/0.98  --abstr_ref_until_sat                   false
% 3.72/0.98  --abstr_ref_sig_restrict                funpre
% 3.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.98  --abstr_ref_under                       []
% 3.72/0.98  
% 3.72/0.98  ------ SAT Options
% 3.72/0.98  
% 3.72/0.98  --sat_mode                              false
% 3.72/0.98  --sat_fm_restart_options                ""
% 3.72/0.98  --sat_gr_def                            false
% 3.72/0.98  --sat_epr_types                         true
% 3.72/0.98  --sat_non_cyclic_types                  false
% 3.72/0.98  --sat_finite_models                     false
% 3.72/0.98  --sat_fm_lemmas                         false
% 3.72/0.98  --sat_fm_prep                           false
% 3.72/0.98  --sat_fm_uc_incr                        true
% 3.72/0.98  --sat_out_model                         small
% 3.72/0.98  --sat_out_clauses                       false
% 3.72/0.98  
% 3.72/0.98  ------ QBF Options
% 3.72/0.98  
% 3.72/0.98  --qbf_mode                              false
% 3.72/0.98  --qbf_elim_univ                         false
% 3.72/0.98  --qbf_dom_inst                          none
% 3.72/0.98  --qbf_dom_pre_inst                      false
% 3.72/0.98  --qbf_sk_in                             false
% 3.72/0.98  --qbf_pred_elim                         true
% 3.72/0.98  --qbf_split                             512
% 3.72/0.98  
% 3.72/0.98  ------ BMC1 Options
% 3.72/0.98  
% 3.72/0.98  --bmc1_incremental                      false
% 3.72/0.98  --bmc1_axioms                           reachable_all
% 3.72/0.98  --bmc1_min_bound                        0
% 3.72/0.98  --bmc1_max_bound                        -1
% 3.72/0.98  --bmc1_max_bound_default                -1
% 3.72/0.98  --bmc1_symbol_reachability              true
% 3.72/0.98  --bmc1_property_lemmas                  false
% 3.72/0.98  --bmc1_k_induction                      false
% 3.72/0.98  --bmc1_non_equiv_states                 false
% 3.72/0.98  --bmc1_deadlock                         false
% 3.72/0.98  --bmc1_ucm                              false
% 3.72/0.98  --bmc1_add_unsat_core                   none
% 3.72/0.98  --bmc1_unsat_core_children              false
% 3.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.98  --bmc1_out_stat                         full
% 3.72/0.98  --bmc1_ground_init                      false
% 3.72/0.98  --bmc1_pre_inst_next_state              false
% 3.72/0.98  --bmc1_pre_inst_state                   false
% 3.72/0.98  --bmc1_pre_inst_reach_state             false
% 3.72/0.98  --bmc1_out_unsat_core                   false
% 3.72/0.98  --bmc1_aig_witness_out                  false
% 3.72/0.98  --bmc1_verbose                          false
% 3.72/0.98  --bmc1_dump_clauses_tptp                false
% 3.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.98  --bmc1_dump_file                        -
% 3.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.98  --bmc1_ucm_extend_mode                  1
% 3.72/0.98  --bmc1_ucm_init_mode                    2
% 3.72/0.98  --bmc1_ucm_cone_mode                    none
% 3.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.98  --bmc1_ucm_relax_model                  4
% 3.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.98  --bmc1_ucm_layered_model                none
% 3.72/0.98  --bmc1_ucm_max_lemma_size               10
% 3.72/0.98  
% 3.72/0.98  ------ AIG Options
% 3.72/0.98  
% 3.72/0.98  --aig_mode                              false
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation Options
% 3.72/0.98  
% 3.72/0.98  --instantiation_flag                    true
% 3.72/0.98  --inst_sos_flag                         false
% 3.72/0.98  --inst_sos_phase                        true
% 3.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel_side                     num_symb
% 3.72/0.98  --inst_solver_per_active                1400
% 3.72/0.98  --inst_solver_calls_frac                1.
% 3.72/0.98  --inst_passive_queue_type               priority_queues
% 3.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.98  --inst_passive_queues_freq              [25;2]
% 3.72/0.98  --inst_dismatching                      true
% 3.72/0.98  --inst_eager_unprocessed_to_passive     true
% 3.72/0.98  --inst_prop_sim_given                   true
% 3.72/0.98  --inst_prop_sim_new                     false
% 3.72/0.98  --inst_subs_new                         false
% 3.72/0.98  --inst_eq_res_simp                      false
% 3.72/0.98  --inst_subs_given                       false
% 3.72/0.98  --inst_orphan_elimination               true
% 3.72/0.98  --inst_learning_loop_flag               true
% 3.72/0.98  --inst_learning_start                   3000
% 3.72/0.98  --inst_learning_factor                  2
% 3.72/0.98  --inst_start_prop_sim_after_learn       3
% 3.72/0.98  --inst_sel_renew                        solver
% 3.72/0.98  --inst_lit_activity_flag                true
% 3.72/0.98  --inst_restr_to_given                   false
% 3.72/0.98  --inst_activity_threshold               500
% 3.72/0.98  --inst_out_proof                        true
% 3.72/0.98  
% 3.72/0.98  ------ Resolution Options
% 3.72/0.98  
% 3.72/0.98  --resolution_flag                       true
% 3.72/0.98  --res_lit_sel                           adaptive
% 3.72/0.98  --res_lit_sel_side                      none
% 3.72/0.98  --res_ordering                          kbo
% 3.72/0.98  --res_to_prop_solver                    active
% 3.72/0.98  --res_prop_simpl_new                    false
% 3.72/0.98  --res_prop_simpl_given                  true
% 3.72/0.98  --res_passive_queue_type                priority_queues
% 3.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.98  --res_passive_queues_freq               [15;5]
% 3.72/0.98  --res_forward_subs                      full
% 3.72/0.98  --res_backward_subs                     full
% 3.72/0.98  --res_forward_subs_resolution           true
% 3.72/0.98  --res_backward_subs_resolution          true
% 3.72/0.98  --res_orphan_elimination                true
% 3.72/0.98  --res_time_limit                        2.
% 3.72/0.98  --res_out_proof                         true
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Options
% 3.72/0.98  
% 3.72/0.98  --superposition_flag                    true
% 3.72/0.98  --sup_passive_queue_type                priority_queues
% 3.72/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.98  --sup_passive_queues_freq               [1;4]
% 3.72/0.98  --demod_completeness_check              fast
% 3.72/0.98  --demod_use_ground                      true
% 3.72/0.98  --sup_to_prop_solver                    passive
% 3.72/0.98  --sup_prop_simpl_new                    true
% 3.72/0.98  --sup_prop_simpl_given                  true
% 3.72/0.98  --sup_fun_splitting                     false
% 3.72/0.98  --sup_smt_interval                      50000
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Simplification Setup
% 3.72/0.98  
% 3.72/0.98  --sup_indices_passive                   []
% 3.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_full_bw                           [BwDemod]
% 3.72/0.98  --sup_immed_triv                        [TrivRules]
% 3.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_immed_bw_main                     []
% 3.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  
% 3.72/0.98  ------ Combination Options
% 3.72/0.98  
% 3.72/0.98  --comb_res_mult                         3
% 3.72/0.98  --comb_sup_mult                         2
% 3.72/0.98  --comb_inst_mult                        10
% 3.72/0.98  
% 3.72/0.98  ------ Debug Options
% 3.72/0.98  
% 3.72/0.98  --dbg_backtrace                         false
% 3.72/0.98  --dbg_dump_prop_clauses                 false
% 3.72/0.98  --dbg_dump_prop_clauses_file            -
% 3.72/0.98  --dbg_out_stat                          false
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS status Theorem for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  fof(f18,axiom,(
% 3.72/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f33,plain,(
% 3.72/0.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.72/0.98    inference(nnf_transformation,[],[f18])).
% 3.72/0.98  
% 3.72/0.98  fof(f60,plain,(
% 3.72/0.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f33])).
% 3.72/0.98  
% 3.72/0.98  fof(f3,axiom,(
% 3.72/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f42,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f3])).
% 3.72/0.98  
% 3.72/0.98  fof(f7,axiom,(
% 3.72/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f46,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f7])).
% 3.72/0.98  
% 3.72/0.98  fof(f17,axiom,(
% 3.72/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f59,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f17])).
% 3.72/0.98  
% 3.72/0.98  fof(f71,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.72/0.98    inference(definition_unfolding,[],[f59,f70])).
% 3.72/0.98  
% 3.72/0.98  fof(f72,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.72/0.98    inference(definition_unfolding,[],[f46,f71])).
% 3.72/0.98  
% 3.72/0.98  fof(f73,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.72/0.98    inference(definition_unfolding,[],[f42,f72])).
% 3.72/0.98  
% 3.72/0.98  fof(f10,axiom,(
% 3.72/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f52,plain,(
% 3.72/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f10])).
% 3.72/0.98  
% 3.72/0.98  fof(f11,axiom,(
% 3.72/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f53,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f11])).
% 3.72/0.98  
% 3.72/0.98  fof(f12,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f54,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f12])).
% 3.72/0.98  
% 3.72/0.98  fof(f13,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f55,plain,(
% 3.72/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f13])).
% 3.72/0.98  
% 3.72/0.98  fof(f14,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f56,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f14])).
% 3.72/0.98  
% 3.72/0.98  fof(f15,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f57,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f15])).
% 3.72/0.98  
% 3.72/0.98  fof(f16,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f58,plain,(
% 3.72/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f16])).
% 3.72/0.98  
% 3.72/0.98  fof(f66,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f57,f58])).
% 3.72/0.98  
% 3.72/0.98  fof(f67,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f56,f66])).
% 3.72/0.98  
% 3.72/0.98  fof(f68,plain,(
% 3.72/0.98    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f55,f67])).
% 3.72/0.98  
% 3.72/0.98  fof(f69,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f54,f68])).
% 3.72/0.98  
% 3.72/0.98  fof(f70,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f53,f69])).
% 3.72/0.98  
% 3.72/0.98  fof(f74,plain,(
% 3.72/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f52,f70])).
% 3.72/0.98  
% 3.72/0.98  fof(f82,plain,(
% 3.72/0.98    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f60,f73,f74,f74,f74])).
% 3.72/0.98  
% 3.72/0.98  fof(f89,plain,(
% 3.72/0.98    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.72/0.98    inference(equality_resolution,[],[f82])).
% 3.72/0.98  
% 3.72/0.98  fof(f9,axiom,(
% 3.72/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f51,plain,(
% 3.72/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f9])).
% 3.72/0.98  
% 3.72/0.98  fof(f75,plain,(
% 3.72/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) )),
% 3.72/0.98    inference(definition_unfolding,[],[f51,f71,f58,f74])).
% 3.72/0.98  
% 3.72/0.98  fof(f6,axiom,(
% 3.72/0.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f45,plain,(
% 3.72/0.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.72/0.98    inference(cnf_transformation,[],[f6])).
% 3.72/0.98  
% 3.72/0.98  fof(f5,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f44,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f5])).
% 3.72/0.98  
% 3.72/0.98  fof(f4,axiom,(
% 3.72/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f43,plain,(
% 3.72/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.72/0.98    inference(cnf_transformation,[],[f4])).
% 3.72/0.98  
% 3.72/0.98  fof(f20,axiom,(
% 3.72/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f24,plain,(
% 3.72/0.98    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.72/0.98    inference(ennf_transformation,[],[f20])).
% 3.72/0.98  
% 3.72/0.98  fof(f25,plain,(
% 3.72/0.98    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.72/0.98    inference(flattening,[],[f24])).
% 3.72/0.98  
% 3.72/0.98  fof(f34,plain,(
% 3.72/0.98    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f35,plain,(
% 3.72/0.98    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f34])).
% 3.72/0.98  
% 3.72/0.98  fof(f63,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK1(X0,X1),X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f35])).
% 3.72/0.98  
% 3.72/0.98  fof(f8,axiom,(
% 3.72/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f29,plain,(
% 3.72/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.72/0.98    inference(nnf_transformation,[],[f8])).
% 3.72/0.98  
% 3.72/0.98  fof(f30,plain,(
% 3.72/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.72/0.98    inference(rectify,[],[f29])).
% 3.72/0.98  
% 3.72/0.98  fof(f31,plain,(
% 3.72/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f32,plain,(
% 3.72/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f47,plain,(
% 3.72/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.72/0.98    inference(cnf_transformation,[],[f32])).
% 3.72/0.98  
% 3.72/0.98  fof(f80,plain,(
% 3.72/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.72/0.98    inference(definition_unfolding,[],[f47,f74])).
% 3.72/0.98  
% 3.72/0.98  fof(f88,plain,(
% 3.72/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 3.72/0.98    inference(equality_resolution,[],[f80])).
% 3.72/0.98  
% 3.72/0.98  fof(f1,axiom,(
% 3.72/0.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f23,plain,(
% 3.72/0.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.72/0.98    inference(rectify,[],[f1])).
% 3.72/0.98  
% 3.72/0.98  fof(f38,plain,(
% 3.72/0.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.72/0.98    inference(cnf_transformation,[],[f23])).
% 3.72/0.98  
% 3.72/0.98  fof(f76,plain,(
% 3.72/0.98    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.72/0.98    inference(definition_unfolding,[],[f38,f71])).
% 3.72/0.98  
% 3.72/0.98  fof(f19,axiom,(
% 3.72/0.98    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f62,plain,(
% 3.72/0.98    ( ! [X0] : (r1_tarski(k1_setfam_1(X0),k3_tarski(X0))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f19])).
% 3.72/0.98  
% 3.72/0.98  fof(f64,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK1(X0,X1))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f35])).
% 3.72/0.98  
% 3.72/0.98  fof(f2,axiom,(
% 3.72/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f27,plain,(
% 3.72/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/0.98    inference(nnf_transformation,[],[f2])).
% 3.72/0.98  
% 3.72/0.98  fof(f28,plain,(
% 3.72/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/0.98    inference(flattening,[],[f27])).
% 3.72/0.98  
% 3.72/0.98  fof(f41,plain,(
% 3.72/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f28])).
% 3.72/0.98  
% 3.72/0.98  fof(f39,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.72/0.98    inference(cnf_transformation,[],[f28])).
% 3.72/0.98  
% 3.72/0.98  fof(f85,plain,(
% 3.72/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.72/0.98    inference(equality_resolution,[],[f39])).
% 3.72/0.98  
% 3.72/0.98  fof(f61,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.72/0.98    inference(cnf_transformation,[],[f33])).
% 3.72/0.98  
% 3.72/0.98  fof(f81,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 3.72/0.98    inference(definition_unfolding,[],[f61,f73,f74,f74,f74])).
% 3.72/0.98  
% 3.72/0.98  fof(f21,conjecture,(
% 3.72/0.98    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f22,negated_conjecture,(
% 3.72/0.98    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.72/0.98    inference(negated_conjecture,[],[f21])).
% 3.72/0.98  
% 3.72/0.98  fof(f26,plain,(
% 3.72/0.98    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 3.72/0.98    inference(ennf_transformation,[],[f22])).
% 3.72/0.98  
% 3.72/0.98  fof(f36,plain,(
% 3.72/0.98    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK2)) != sK2),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f37,plain,(
% 3.72/0.98    k1_setfam_1(k1_tarski(sK2)) != sK2),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f36])).
% 3.72/0.98  
% 3.72/0.98  fof(f65,plain,(
% 3.72/0.98    k1_setfam_1(k1_tarski(sK2)) != sK2),
% 3.72/0.98    inference(cnf_transformation,[],[f37])).
% 3.72/0.98  
% 3.72/0.98  fof(f83,plain,(
% 3.72/0.98    k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != sK2),
% 3.72/0.98    inference(definition_unfolding,[],[f65,f74])).
% 3.72/0.98  
% 3.72/0.98  cnf(c_161,plain,
% 3.72/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.72/0.98      theory(equality) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7492,plain,
% 3.72/0.98      ( ~ r1_tarski(X0,X1)
% 3.72/0.98      | r1_tarski(X2,sK1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),X2))
% 3.72/0.98      | X2 != X0
% 3.72/0.98      | sK1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),X2) != X1 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_161]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7494,plain,
% 3.72/0.98      ( r1_tarski(sK2,sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK2))
% 3.72/0.98      | ~ r1_tarski(sK2,sK2)
% 3.72/0.98      | sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK2) != sK2
% 3.72/0.98      | sK2 != sK2 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_7492]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_158,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_615,plain,
% 3.72/0.98      ( X0 != X1
% 3.72/0.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1
% 3.72/0.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_158]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1315,plain,
% 3.72/0.98      ( X0 != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
% 3.72/0.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
% 3.72/0.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_615]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_5748,plain,
% 3.72/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
% 3.72/0.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 3.72/0.98      | k1_xboole_0 != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_1315]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_5750,plain,
% 3.72/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.72/0.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 3.72/0.98      | k1_xboole_0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_5748]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_13,plain,
% 3.72/0.98      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_0,plain,
% 3.72/0.98      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.72/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7,plain,
% 3.72/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_377,plain,
% 3.72/0.98      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_13,c_0,c_7]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6,plain,
% 3.72/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.72/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_442,plain,
% 3.72/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1041,plain,
% 3.72/0.98      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_7,c_442]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_5,plain,
% 3.72/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1065,plain,
% 3.72/0.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.72/0.98      inference(light_normalisation,[status(thm)],[c_1041,c_5]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2746,plain,
% 3.72/0.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_377,c_7,c_1065]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2748,plain,
% 3.72/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_2746]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_16,plain,
% 3.72/0.98      ( r2_hidden(sK1(X0,X1),X0)
% 3.72/0.98      | r1_tarski(X1,k1_setfam_1(X0))
% 3.72/0.98      | k1_xboole_0 = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_316,plain,
% 3.72/0.98      ( k1_xboole_0 = X0
% 3.72/0.98      | r2_hidden(sK1(X0,X1),X0) = iProver_top
% 3.72/0.98      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_11,plain,
% 3.72/0.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.72/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_319,plain,
% 3.72/0.98      ( X0 = X1
% 3.72/0.98      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_865,plain,
% 3.72/0.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 3.72/0.98      | sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X0
% 3.72/0.98      | r1_tarski(X1,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_316,c_319]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_867,plain,
% 3.72/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 3.72/0.98      | sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK2) = sK2
% 3.72/0.98      | r1_tarski(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = iProver_top ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_865]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1,plain,
% 3.72/0.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_14,plain,
% 3.72/0.98      ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
% 3.72/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_318,plain,
% 3.72/0.98      ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_737,plain,
% 3.72/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),X0) = iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1,c_318]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_745,plain,
% 3.72/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),X0) ),
% 3.72/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_737]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_747,plain,
% 3.72/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_745]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_746,plain,
% 3.72/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2) = iProver_top ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_737]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_15,plain,
% 3.72/0.98      ( ~ r1_tarski(X0,sK1(X1,X0))
% 3.72/0.98      | r1_tarski(X0,k1_setfam_1(X1))
% 3.72/0.98      | k1_xboole_0 = X1 ),
% 3.72/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_665,plain,
% 3.72/0.98      ( ~ r1_tarski(X0,sK1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0))
% 3.72/0.98      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
% 3.72/0.98      | k1_xboole_0 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_667,plain,
% 3.72/0.98      ( ~ r1_tarski(sK2,sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK2))
% 3.72/0.98      | r1_tarski(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
% 3.72/0.98      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_665]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2,plain,
% 3.72/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.72/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_412,plain,
% 3.72/0.98      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2)
% 3.72/0.98      | ~ r1_tarski(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
% 3.72/0.98      | k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK2 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_413,plain,
% 3.72/0.98      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK2
% 3.72/0.98      | r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2) != iProver_top
% 3.72/0.98      | r1_tarski(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_159,plain,
% 3.72/0.98      ( X0 != X1
% 3.72/0.98      | X2 != X3
% 3.72/0.98      | X4 != X5
% 3.72/0.98      | X6 != X7
% 3.72/0.98      | X8 != X9
% 3.72/0.98      | X10 != X11
% 3.72/0.98      | X12 != X13
% 3.72/0.98      | X14 != X15
% 3.72/0.98      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 3.72/0.98      theory(equality) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_165,plain,
% 3.72/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.72/0.98      | sK2 != sK2 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_159]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4,plain,
% 3.72/0.98      ( r1_tarski(X0,X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_45,plain,
% 3.72/0.98      ( r1_tarski(sK2,sK2) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_12,plain,
% 3.72/0.98      ( X0 = X1
% 3.72/0.98      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.72/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_28,plain,
% 3.72/0.98      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.72/0.98      | sK2 = sK2 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_27,plain,
% 3.72/0.98      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_17,negated_conjecture,
% 3.72/0.98      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != sK2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(contradiction,plain,
% 3.72/0.98      ( $false ),
% 3.72/0.98      inference(minisat,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_7494,c_5750,c_2748,c_867,c_747,c_746,c_667,c_413,
% 3.72/0.98                 c_412,c_165,c_45,c_28,c_27,c_17]) ).
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  ------                               Statistics
% 3.72/0.98  
% 3.72/0.98  ------ Selected
% 3.72/0.98  
% 3.72/0.98  total_time:                             0.308
% 3.72/0.98  
%------------------------------------------------------------------------------
