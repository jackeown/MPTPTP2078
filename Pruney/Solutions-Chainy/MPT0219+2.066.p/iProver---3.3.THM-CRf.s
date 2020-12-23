%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:19 EST 2020

% Result     : Theorem 31.37s
% Output     : CNFRefutation 31.37s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 527 expanded)
%              Number of clauses        :   47 (  86 expanded)
%              Number of leaves         :   26 ( 164 expanded)
%              Depth                    :   15
%              Number of atoms          :  313 ( 803 expanded)
%              Number of equality atoms :  241 ( 693 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f23,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f33])).

fof(f64,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f71,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f71])).

fof(f90,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f64,f66,f72,f72,f72])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f38,f36,f66])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f37,f66])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f55,f66,f68,f69])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(definition_unfolding,[],[f56,f66,f72,f73])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f54,f66,f69,f69])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f91,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f92,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f91])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f9])).

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
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f50,f72])).

fof(f100,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f98,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f87])).

fof(f99,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f98])).

fof(f65,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_48959,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_1,c_20])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_48797,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_2])).

cnf(c_49042,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_48797,c_5])).

cnf(c_49779,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_5,c_49042])).

cnf(c_49783,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_48797,c_49042])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_49818,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_49783,c_4])).

cnf(c_56149,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(demodulation,[status(thm)],[c_49779,c_49818])).

cnf(c_56199,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_48959,c_56149])).

cnf(c_56231,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
    inference(superposition,[status(thm)],[c_48797,c_56149])).

cnf(c_56423,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_56231,c_4])).

cnf(c_56513,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_56199,c_56423])).

cnf(c_18,plain,
    ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_49534,plain,
    ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) ),
    inference(superposition,[status(thm)],[c_1,c_18])).

cnf(c_104931,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_56513,c_49534])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_105728,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_104931,c_0,c_4,c_48797])).

cnf(c_122,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_49485,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X2,X2,X2,X2,X2,X2,X3,sK3)
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X3,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_59908,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X9,X9,X9,X9,X9,X9,X10,sK3)
    | k6_enumset1(X9,X9,X9,X9,X9,X9,X10,sK3) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(instantiation,[status(thm)],[c_49485])).

cnf(c_59909,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_59908])).

cnf(c_10,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_49265,plain,
    ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_49267,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_49265])).

cnf(c_126,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5428,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_6073,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5428])).

cnf(c_6074,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6073])).

cnf(c_17064,plain,
    ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3) ),
    inference(instantiation,[status(thm)],[c_6074])).

cnf(c_17066,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_17064])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2012,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2014,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_689,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_690,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_123,plain,
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

cnf(c_127,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_16,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_26,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_105728,c_59909,c_49267,c_17066,c_2014,c_690,c_127,c_26,c_23,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 21:00:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.37/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.37/4.49  
% 31.37/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.37/4.49  
% 31.37/4.49  ------  iProver source info
% 31.37/4.49  
% 31.37/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.37/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.37/4.49  git: non_committed_changes: false
% 31.37/4.49  git: last_make_outside_of_git: false
% 31.37/4.49  
% 31.37/4.49  ------ 
% 31.37/4.49  ------ Parsing...
% 31.37/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  ------ Proving...
% 31.37/4.49  ------ Problem Properties 
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  clauses                                 21
% 31.37/4.49  conjectures                             2
% 31.37/4.49  EPR                                     1
% 31.37/4.49  Horn                                    18
% 31.37/4.49  unary                                   13
% 31.37/4.49  binary                                  1
% 31.37/4.49  lits                                    39
% 31.37/4.49  lits eq                                 27
% 31.37/4.49  fd_pure                                 0
% 31.37/4.49  fd_pseudo                               0
% 31.37/4.49  fd_cond                                 0
% 31.37/4.49  fd_pseudo_cond                          6
% 31.37/4.49  AC symbols                              0
% 31.37/4.49  
% 31.37/4.49  ------ Input Options Time Limit: Unbounded
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 31.37/4.49  Current options:
% 31.37/4.49  ------ 
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.37/4.49  
% 31.37/4.49  ------ Proving...
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  % SZS status Theorem for theBenchmark.p
% 31.37/4.49  
% 31.37/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.37/4.49  
% 31.37/4.49  fof(f1,axiom,(
% 31.37/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f35,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f1])).
% 31.37/4.49  
% 31.37/4.49  fof(f20,conjecture,(
% 31.37/4.49    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f21,negated_conjecture,(
% 31.37/4.49    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 31.37/4.49    inference(negated_conjecture,[],[f20])).
% 31.37/4.49  
% 31.37/4.49  fof(f23,plain,(
% 31.37/4.49    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 31.37/4.49    inference(ennf_transformation,[],[f21])).
% 31.37/4.49  
% 31.37/4.49  fof(f33,plain,(
% 31.37/4.49    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 31.37/4.49    introduced(choice_axiom,[])).
% 31.37/4.49  
% 31.37/4.49  fof(f34,plain,(
% 31.37/4.49    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 31.37/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f33])).
% 31.37/4.49  
% 31.37/4.49  fof(f64,plain,(
% 31.37/4.49    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 31.37/4.49    inference(cnf_transformation,[],[f34])).
% 31.37/4.49  
% 31.37/4.49  fof(f7,axiom,(
% 31.37/4.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f41,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f7])).
% 31.37/4.49  
% 31.37/4.49  fof(f2,axiom,(
% 31.37/4.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f36,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.37/4.49    inference(cnf_transformation,[],[f2])).
% 31.37/4.49  
% 31.37/4.49  fof(f66,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 31.37/4.49    inference(definition_unfolding,[],[f41,f36])).
% 31.37/4.49  
% 31.37/4.49  fof(f13,axiom,(
% 31.37/4.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f57,plain,(
% 31.37/4.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f13])).
% 31.37/4.49  
% 31.37/4.49  fof(f14,axiom,(
% 31.37/4.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f58,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f14])).
% 31.37/4.49  
% 31.37/4.49  fof(f15,axiom,(
% 31.37/4.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f59,plain,(
% 31.37/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f15])).
% 31.37/4.49  
% 31.37/4.49  fof(f16,axiom,(
% 31.37/4.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f60,plain,(
% 31.37/4.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f16])).
% 31.37/4.49  
% 31.37/4.49  fof(f17,axiom,(
% 31.37/4.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f61,plain,(
% 31.37/4.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f17])).
% 31.37/4.49  
% 31.37/4.49  fof(f18,axiom,(
% 31.37/4.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f62,plain,(
% 31.37/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f18])).
% 31.37/4.49  
% 31.37/4.49  fof(f19,axiom,(
% 31.37/4.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f63,plain,(
% 31.37/4.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f19])).
% 31.37/4.49  
% 31.37/4.49  fof(f67,plain,(
% 31.37/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 31.37/4.49    inference(definition_unfolding,[],[f62,f63])).
% 31.37/4.49  
% 31.37/4.49  fof(f68,plain,(
% 31.37/4.49    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 31.37/4.49    inference(definition_unfolding,[],[f61,f67])).
% 31.37/4.49  
% 31.37/4.49  fof(f69,plain,(
% 31.37/4.49    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 31.37/4.49    inference(definition_unfolding,[],[f60,f68])).
% 31.37/4.49  
% 31.37/4.49  fof(f70,plain,(
% 31.37/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 31.37/4.49    inference(definition_unfolding,[],[f59,f69])).
% 31.37/4.49  
% 31.37/4.49  fof(f71,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 31.37/4.49    inference(definition_unfolding,[],[f58,f70])).
% 31.37/4.49  
% 31.37/4.49  fof(f72,plain,(
% 31.37/4.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 31.37/4.49    inference(definition_unfolding,[],[f57,f71])).
% 31.37/4.49  
% 31.37/4.49  fof(f90,plain,(
% 31.37/4.49    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 31.37/4.49    inference(definition_unfolding,[],[f64,f66,f72,f72,f72])).
% 31.37/4.49  
% 31.37/4.49  fof(f6,axiom,(
% 31.37/4.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f40,plain,(
% 31.37/4.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f6])).
% 31.37/4.49  
% 31.37/4.49  fof(f4,axiom,(
% 31.37/4.49    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f38,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 31.37/4.49    inference(cnf_transformation,[],[f4])).
% 31.37/4.49  
% 31.37/4.49  fof(f76,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 31.37/4.49    inference(definition_unfolding,[],[f38,f36,f66])).
% 31.37/4.49  
% 31.37/4.49  fof(f3,axiom,(
% 31.37/4.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f37,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 31.37/4.49    inference(cnf_transformation,[],[f3])).
% 31.37/4.49  
% 31.37/4.49  fof(f75,plain,(
% 31.37/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 31.37/4.49    inference(definition_unfolding,[],[f37,f66])).
% 31.37/4.49  
% 31.37/4.49  fof(f5,axiom,(
% 31.37/4.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f39,plain,(
% 31.37/4.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.37/4.49    inference(cnf_transformation,[],[f5])).
% 31.37/4.49  
% 31.37/4.49  fof(f12,axiom,(
% 31.37/4.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f56,plain,(
% 31.37/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f12])).
% 31.37/4.49  
% 31.37/4.49  fof(f11,axiom,(
% 31.37/4.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f55,plain,(
% 31.37/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f11])).
% 31.37/4.49  
% 31.37/4.49  fof(f73,plain,(
% 31.37/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 31.37/4.49    inference(definition_unfolding,[],[f55,f66,f68,f69])).
% 31.37/4.49  
% 31.37/4.49  fof(f89,plain,(
% 31.37/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) )),
% 31.37/4.49    inference(definition_unfolding,[],[f56,f66,f72,f73])).
% 31.37/4.49  
% 31.37/4.49  fof(f10,axiom,(
% 31.37/4.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f54,plain,(
% 31.37/4.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 31.37/4.49    inference(cnf_transformation,[],[f10])).
% 31.37/4.49  
% 31.37/4.49  fof(f74,plain,(
% 31.37/4.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 31.37/4.49    inference(definition_unfolding,[],[f54,f66,f69,f69])).
% 31.37/4.49  
% 31.37/4.49  fof(f8,axiom,(
% 31.37/4.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f22,plain,(
% 31.37/4.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 31.37/4.49    inference(ennf_transformation,[],[f8])).
% 31.37/4.49  
% 31.37/4.49  fof(f24,plain,(
% 31.37/4.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 31.37/4.49    inference(nnf_transformation,[],[f22])).
% 31.37/4.49  
% 31.37/4.49  fof(f25,plain,(
% 31.37/4.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 31.37/4.49    inference(flattening,[],[f24])).
% 31.37/4.49  
% 31.37/4.49  fof(f26,plain,(
% 31.37/4.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 31.37/4.49    inference(rectify,[],[f25])).
% 31.37/4.49  
% 31.37/4.49  fof(f27,plain,(
% 31.37/4.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 31.37/4.49    introduced(choice_axiom,[])).
% 31.37/4.49  
% 31.37/4.49  fof(f28,plain,(
% 31.37/4.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 31.37/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 31.37/4.49  
% 31.37/4.49  fof(f45,plain,(
% 31.37/4.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 31.37/4.49    inference(cnf_transformation,[],[f28])).
% 31.37/4.49  
% 31.37/4.49  fof(f81,plain,(
% 31.37/4.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 31.37/4.49    inference(definition_unfolding,[],[f45,f70])).
% 31.37/4.49  
% 31.37/4.49  fof(f91,plain,(
% 31.37/4.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 31.37/4.49    inference(equality_resolution,[],[f81])).
% 31.37/4.49  
% 31.37/4.49  fof(f92,plain,(
% 31.37/4.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 31.37/4.49    inference(equality_resolution,[],[f91])).
% 31.37/4.49  
% 31.37/4.49  fof(f9,axiom,(
% 31.37/4.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 31.37/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.37/4.49  
% 31.37/4.49  fof(f29,plain,(
% 31.37/4.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 31.37/4.49    inference(nnf_transformation,[],[f9])).
% 31.37/4.49  
% 31.37/4.49  fof(f30,plain,(
% 31.37/4.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 31.37/4.49    inference(rectify,[],[f29])).
% 31.37/4.49  
% 31.37/4.49  fof(f31,plain,(
% 31.37/4.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 31.37/4.49    introduced(choice_axiom,[])).
% 31.37/4.49  
% 31.37/4.49  fof(f32,plain,(
% 31.37/4.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 31.37/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 31.37/4.49  
% 31.37/4.49  fof(f50,plain,(
% 31.37/4.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 31.37/4.49    inference(cnf_transformation,[],[f32])).
% 31.37/4.49  
% 31.37/4.49  fof(f88,plain,(
% 31.37/4.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 31.37/4.49    inference(definition_unfolding,[],[f50,f72])).
% 31.37/4.49  
% 31.37/4.49  fof(f100,plain,(
% 31.37/4.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 31.37/4.49    inference(equality_resolution,[],[f88])).
% 31.37/4.49  
% 31.37/4.49  fof(f51,plain,(
% 31.37/4.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 31.37/4.49    inference(cnf_transformation,[],[f32])).
% 31.37/4.49  
% 31.37/4.49  fof(f87,plain,(
% 31.37/4.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 31.37/4.49    inference(definition_unfolding,[],[f51,f72])).
% 31.37/4.49  
% 31.37/4.49  fof(f98,plain,(
% 31.37/4.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 31.37/4.49    inference(equality_resolution,[],[f87])).
% 31.37/4.49  
% 31.37/4.49  fof(f99,plain,(
% 31.37/4.49    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 31.37/4.49    inference(equality_resolution,[],[f98])).
% 31.37/4.49  
% 31.37/4.49  fof(f65,plain,(
% 31.37/4.49    sK2 != sK3),
% 31.37/4.49    inference(cnf_transformation,[],[f34])).
% 31.37/4.49  
% 31.37/4.49  cnf(c_1,plain,
% 31.37/4.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 31.37/4.49      inference(cnf_transformation,[],[f35]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_20,negated_conjecture,
% 31.37/4.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 31.37/4.49      inference(cnf_transformation,[],[f90]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_48959,plain,
% 31.37/4.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 31.37/4.49      inference(demodulation,[status(thm)],[c_1,c_20]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_5,plain,
% 31.37/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 31.37/4.49      inference(cnf_transformation,[],[f40]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_3,plain,
% 31.37/4.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 31.37/4.49      inference(cnf_transformation,[],[f76]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_2,plain,
% 31.37/4.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 31.37/4.49      inference(cnf_transformation,[],[f75]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_48797,plain,
% 31.37/4.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.37/4.49      inference(light_normalisation,[status(thm)],[c_3,c_2]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_49042,plain,
% 31.37/4.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 31.37/4.49      inference(superposition,[status(thm)],[c_48797,c_5]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_49779,plain,
% 31.37/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 31.37/4.49      inference(superposition,[status(thm)],[c_5,c_49042]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_49783,plain,
% 31.37/4.49      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 31.37/4.49      inference(superposition,[status(thm)],[c_48797,c_49042]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_4,plain,
% 31.37/4.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.37/4.49      inference(cnf_transformation,[],[f39]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_49818,plain,
% 31.37/4.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 31.37/4.49      inference(light_normalisation,[status(thm)],[c_49783,c_4]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_56149,plain,
% 31.37/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 31.37/4.49      inference(demodulation,[status(thm)],[c_49779,c_49818]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_56199,plain,
% 31.37/4.49      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 31.37/4.49      inference(superposition,[status(thm)],[c_48959,c_56149]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_56231,plain,
% 31.37/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
% 31.37/4.49      inference(superposition,[status(thm)],[c_48797,c_56149]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_56423,plain,
% 31.37/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 31.37/4.49      inference(light_normalisation,[status(thm)],[c_56231,c_4]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_56513,plain,
% 31.37/4.49      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 31.37/4.49      inference(demodulation,[status(thm)],[c_56199,c_56423]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_18,plain,
% 31.37/4.49      ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) ),
% 31.37/4.49      inference(cnf_transformation,[],[f89]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_49534,plain,
% 31.37/4.49      ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) ),
% 31.37/4.49      inference(superposition,[status(thm)],[c_1,c_18]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_104931,plain,
% 31.37/4.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
% 31.37/4.49      inference(superposition,[status(thm)],[c_56513,c_49534]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_0,plain,
% 31.37/4.49      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 31.37/4.49      inference(cnf_transformation,[],[f74]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_105728,plain,
% 31.37/4.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 31.37/4.49      inference(demodulation,[status(thm)],[c_104931,c_0,c_4,c_48797]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_122,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_49485,plain,
% 31.37/4.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1
% 31.37/4.49      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X2,X2,X2,X2,X2,X2,X3,sK3)
% 31.37/4.49      | k6_enumset1(X2,X2,X2,X2,X2,X2,X3,sK3) != X1 ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_122]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_59908,plain,
% 31.37/4.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
% 31.37/4.49      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X9,X9,X9,X9,X9,X9,X10,sK3)
% 31.37/4.49      | k6_enumset1(X9,X9,X9,X9,X9,X9,X10,sK3) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_49485]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_59909,plain,
% 31.37/4.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 31.37/4.49      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 31.37/4.49      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_59908]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_10,plain,
% 31.37/4.49      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 31.37/4.49      inference(cnf_transformation,[],[f92]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_49265,plain,
% 31.37/4.49      ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_10]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_49267,plain,
% 31.37/4.49      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_49265]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_126,plain,
% 31.37/4.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.37/4.49      theory(equality) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_5428,plain,
% 31.37/4.49      ( ~ r2_hidden(X0,X1)
% 31.37/4.49      | r2_hidden(sK3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 31.37/4.49      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
% 31.37/4.49      | sK3 != X0 ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_126]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_6073,plain,
% 31.37/4.49      ( ~ r2_hidden(sK3,X0)
% 31.37/4.49      | r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 31.37/4.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
% 31.37/4.49      | sK3 != sK3 ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_5428]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_6074,plain,
% 31.37/4.49      ( ~ r2_hidden(sK3,X0)
% 31.37/4.49      | r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 31.37/4.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ),
% 31.37/4.49      inference(equality_resolution_simp,[status(thm)],[c_6073]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_17064,plain,
% 31.37/4.49      ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 31.37/4.49      | ~ r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3))
% 31.37/4.49      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3) ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_6074]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_17066,plain,
% 31.37/4.49      ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 31.37/4.49      | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 31.37/4.49      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_17064]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_17,plain,
% 31.37/4.49      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 31.37/4.49      inference(cnf_transformation,[],[f100]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_2012,plain,
% 31.37/4.49      ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 31.37/4.49      | sK3 = X0 ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_17]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_2014,plain,
% 31.37/4.49      ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 31.37/4.49      | sK3 = sK2 ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_2012]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_689,plain,
% 31.37/4.49      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_122]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_690,plain,
% 31.37/4.49      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_689]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_123,plain,
% 31.37/4.49      ( X0 != X1
% 31.37/4.49      | X2 != X3
% 31.37/4.49      | X4 != X5
% 31.37/4.49      | X6 != X7
% 31.37/4.49      | X8 != X9
% 31.37/4.49      | X10 != X11
% 31.37/4.49      | X12 != X13
% 31.37/4.49      | X14 != X15
% 31.37/4.49      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 31.37/4.49      theory(equality) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_127,plain,
% 31.37/4.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 31.37/4.49      | sK2 != sK2 ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_123]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_16,plain,
% 31.37/4.49      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 31.37/4.49      inference(cnf_transformation,[],[f99]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_26,plain,
% 31.37/4.49      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_16]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_23,plain,
% 31.37/4.49      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 31.37/4.49      | sK2 = sK2 ),
% 31.37/4.49      inference(instantiation,[status(thm)],[c_17]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(c_19,negated_conjecture,
% 31.37/4.49      ( sK2 != sK3 ),
% 31.37/4.49      inference(cnf_transformation,[],[f65]) ).
% 31.37/4.49  
% 31.37/4.49  cnf(contradiction,plain,
% 31.37/4.49      ( $false ),
% 31.37/4.49      inference(minisat,
% 31.37/4.49                [status(thm)],
% 31.37/4.49                [c_105728,c_59909,c_49267,c_17066,c_2014,c_690,c_127,
% 31.37/4.49                 c_26,c_23,c_19]) ).
% 31.37/4.49  
% 31.37/4.49  
% 31.37/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.37/4.49  
% 31.37/4.49  ------                               Statistics
% 31.37/4.49  
% 31.37/4.49  ------ Selected
% 31.37/4.49  
% 31.37/4.49  total_time:                             3.521
% 31.37/4.49  
%------------------------------------------------------------------------------
