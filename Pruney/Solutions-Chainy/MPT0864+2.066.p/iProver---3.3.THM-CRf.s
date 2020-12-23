%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:58 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 425 expanded)
%              Number of clauses        :   61 (  72 expanded)
%              Number of leaves         :   21 ( 131 expanded)
%              Depth                    :   14
%              Number of atoms          :  273 ( 703 expanded)
%              Number of equality atoms :  194 ( 571 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f33])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f72])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f73])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f56,f75,f75,f75])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f19,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f23,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK3,sK4) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK2) = sK2
        | k1_mcart_1(sK2) = sK2 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK2 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( k2_mcart_1(sK2) = sK2
      | k1_mcart_1(sK2) = sK2 )
    & k4_tarski(sK3,sK4) = sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f36,f35])).

fof(f69,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f74,f74])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f55,f75,f75,f75])).

fof(f95,plain,(
    ! [X1] : k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f85])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_639,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X0 != X2
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_701,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | X1 != X0
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_5323,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_5325,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK3 != sK2 ),
    inference(instantiation,[status(thm)],[c_5323])).

cnf(c_5291,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_5293,plain,
    ( r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK4 != sK2 ),
    inference(instantiation,[status(thm)],[c_5291])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X0,X2) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_723,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k4_tarski(X0,X2) != sK1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k1_xboole_0 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2504,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k4_tarski(sK3,sK4) != sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_2506,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_tarski(sK3,sK4) != sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X2,X0) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_722,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k4_tarski(X2,X0) != sK1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k1_xboole_0 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2499,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k4_tarski(sK3,sK4) != sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_2501,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_tarski(sK3,sK4) != sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2499])).

cnf(c_21,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_559,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( X0 = X1
    | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_565,plain,
    ( k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1718,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_565])).

cnf(c_1840,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_559,c_1718])).

cnf(c_1841,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_222,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_1650,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0
    | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | k4_xboole_0(k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_1651,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
    | k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_221,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_979,plain,
    ( k4_tarski(X0,X1) != X2
    | k4_tarski(X0,X1) = sK1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
    | sK1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) != X2 ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_1528,plain,
    ( k4_tarski(sK3,sK4) = sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k4_tarski(sK3,sK4) != sK2
    | sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != sK2 ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_1529,plain,
    ( k4_tarski(sK3,sK4) = sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_tarski(sK3,sK4) != sK2
    | sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_220,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1245,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_1246,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_751,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
    | k4_xboole_0(k4_xboole_0(X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1075,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0))
    | k4_xboole_0(k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_1077,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0))
    | k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1075])).

cnf(c_22,negated_conjecture,
    ( k1_mcart_1(sK2) = sK2
    | k2_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_760,plain,
    ( k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_23,c_18])).

cnf(c_820,plain,
    ( k2_mcart_1(sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_22,c_760])).

cnf(c_17,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_706,plain,
    ( k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_23,c_17])).

cnf(c_822,plain,
    ( sK4 = sK2
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_820,c_706])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_816,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_817,plain,
    ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_774,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_776,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_695,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_697,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_670,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(X1,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0))
    | X1 != X0
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_672,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0))
    | k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_617,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_619,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_48,plain,
    ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_47,plain,
    ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5325,c_5293,c_2506,c_2501,c_1841,c_1651,c_1529,c_1246,c_1077,c_822,c_817,c_776,c_697,c_672,c_619,c_48,c_47,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:30:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.71/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.04  
% 3.71/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.04  
% 3.71/1.04  ------  iProver source info
% 3.71/1.04  
% 3.71/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.04  git: non_committed_changes: false
% 3.71/1.04  git: last_make_outside_of_git: false
% 3.71/1.04  
% 3.71/1.04  ------ 
% 3.71/1.04  
% 3.71/1.04  ------ Input Options
% 3.71/1.04  
% 3.71/1.04  --out_options                           all
% 3.71/1.04  --tptp_safe_out                         true
% 3.71/1.04  --problem_path                          ""
% 3.71/1.04  --include_path                          ""
% 3.71/1.04  --clausifier                            res/vclausify_rel
% 3.71/1.04  --clausifier_options                    ""
% 3.71/1.04  --stdin                                 false
% 3.71/1.04  --stats_out                             all
% 3.71/1.04  
% 3.71/1.04  ------ General Options
% 3.71/1.04  
% 3.71/1.04  --fof                                   false
% 3.71/1.04  --time_out_real                         305.
% 3.71/1.04  --time_out_virtual                      -1.
% 3.71/1.04  --symbol_type_check                     false
% 3.71/1.04  --clausify_out                          false
% 3.71/1.04  --sig_cnt_out                           false
% 3.71/1.04  --trig_cnt_out                          false
% 3.71/1.04  --trig_cnt_out_tolerance                1.
% 3.71/1.04  --trig_cnt_out_sk_spl                   false
% 3.71/1.04  --abstr_cl_out                          false
% 3.71/1.04  
% 3.71/1.04  ------ Global Options
% 3.71/1.04  
% 3.71/1.04  --schedule                              default
% 3.71/1.04  --add_important_lit                     false
% 3.71/1.04  --prop_solver_per_cl                    1000
% 3.71/1.04  --min_unsat_core                        false
% 3.71/1.04  --soft_assumptions                      false
% 3.71/1.04  --soft_lemma_size                       3
% 3.71/1.04  --prop_impl_unit_size                   0
% 3.71/1.04  --prop_impl_unit                        []
% 3.71/1.04  --share_sel_clauses                     true
% 3.71/1.04  --reset_solvers                         false
% 3.71/1.04  --bc_imp_inh                            [conj_cone]
% 3.71/1.04  --conj_cone_tolerance                   3.
% 3.71/1.04  --extra_neg_conj                        none
% 3.71/1.04  --large_theory_mode                     true
% 3.71/1.04  --prolific_symb_bound                   200
% 3.71/1.04  --lt_threshold                          2000
% 3.71/1.04  --clause_weak_htbl                      true
% 3.71/1.04  --gc_record_bc_elim                     false
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing Options
% 3.71/1.04  
% 3.71/1.04  --preprocessing_flag                    true
% 3.71/1.04  --time_out_prep_mult                    0.1
% 3.71/1.04  --splitting_mode                        input
% 3.71/1.04  --splitting_grd                         true
% 3.71/1.04  --splitting_cvd                         false
% 3.71/1.04  --splitting_cvd_svl                     false
% 3.71/1.04  --splitting_nvd                         32
% 3.71/1.04  --sub_typing                            true
% 3.71/1.04  --prep_gs_sim                           true
% 3.71/1.04  --prep_unflatten                        true
% 3.71/1.04  --prep_res_sim                          true
% 3.71/1.04  --prep_upred                            true
% 3.71/1.04  --prep_sem_filter                       exhaustive
% 3.71/1.04  --prep_sem_filter_out                   false
% 3.71/1.04  --pred_elim                             true
% 3.71/1.04  --res_sim_input                         true
% 3.71/1.04  --eq_ax_congr_red                       true
% 3.71/1.04  --pure_diseq_elim                       true
% 3.71/1.04  --brand_transform                       false
% 3.71/1.04  --non_eq_to_eq                          false
% 3.71/1.04  --prep_def_merge                        true
% 3.71/1.04  --prep_def_merge_prop_impl              false
% 3.71/1.04  --prep_def_merge_mbd                    true
% 3.71/1.04  --prep_def_merge_tr_red                 false
% 3.71/1.04  --prep_def_merge_tr_cl                  false
% 3.71/1.04  --smt_preprocessing                     true
% 3.71/1.04  --smt_ac_axioms                         fast
% 3.71/1.04  --preprocessed_out                      false
% 3.71/1.04  --preprocessed_stats                    false
% 3.71/1.04  
% 3.71/1.04  ------ Abstraction refinement Options
% 3.71/1.04  
% 3.71/1.04  --abstr_ref                             []
% 3.71/1.04  --abstr_ref_prep                        false
% 3.71/1.04  --abstr_ref_until_sat                   false
% 3.71/1.04  --abstr_ref_sig_restrict                funpre
% 3.71/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.04  --abstr_ref_under                       []
% 3.71/1.04  
% 3.71/1.04  ------ SAT Options
% 3.71/1.04  
% 3.71/1.04  --sat_mode                              false
% 3.71/1.04  --sat_fm_restart_options                ""
% 3.71/1.04  --sat_gr_def                            false
% 3.71/1.04  --sat_epr_types                         true
% 3.71/1.04  --sat_non_cyclic_types                  false
% 3.71/1.04  --sat_finite_models                     false
% 3.71/1.04  --sat_fm_lemmas                         false
% 3.71/1.04  --sat_fm_prep                           false
% 3.71/1.04  --sat_fm_uc_incr                        true
% 3.71/1.04  --sat_out_model                         small
% 3.71/1.04  --sat_out_clauses                       false
% 3.71/1.04  
% 3.71/1.04  ------ QBF Options
% 3.71/1.04  
% 3.71/1.04  --qbf_mode                              false
% 3.71/1.04  --qbf_elim_univ                         false
% 3.71/1.04  --qbf_dom_inst                          none
% 3.71/1.04  --qbf_dom_pre_inst                      false
% 3.71/1.04  --qbf_sk_in                             false
% 3.71/1.04  --qbf_pred_elim                         true
% 3.71/1.04  --qbf_split                             512
% 3.71/1.04  
% 3.71/1.04  ------ BMC1 Options
% 3.71/1.04  
% 3.71/1.04  --bmc1_incremental                      false
% 3.71/1.04  --bmc1_axioms                           reachable_all
% 3.71/1.04  --bmc1_min_bound                        0
% 3.71/1.04  --bmc1_max_bound                        -1
% 3.71/1.04  --bmc1_max_bound_default                -1
% 3.71/1.04  --bmc1_symbol_reachability              true
% 3.71/1.04  --bmc1_property_lemmas                  false
% 3.71/1.04  --bmc1_k_induction                      false
% 3.71/1.04  --bmc1_non_equiv_states                 false
% 3.71/1.04  --bmc1_deadlock                         false
% 3.71/1.04  --bmc1_ucm                              false
% 3.71/1.04  --bmc1_add_unsat_core                   none
% 3.71/1.04  --bmc1_unsat_core_children              false
% 3.71/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.04  --bmc1_out_stat                         full
% 3.71/1.04  --bmc1_ground_init                      false
% 3.71/1.04  --bmc1_pre_inst_next_state              false
% 3.71/1.04  --bmc1_pre_inst_state                   false
% 3.71/1.04  --bmc1_pre_inst_reach_state             false
% 3.71/1.04  --bmc1_out_unsat_core                   false
% 3.71/1.04  --bmc1_aig_witness_out                  false
% 3.71/1.04  --bmc1_verbose                          false
% 3.71/1.04  --bmc1_dump_clauses_tptp                false
% 3.71/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.04  --bmc1_dump_file                        -
% 3.71/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.04  --bmc1_ucm_extend_mode                  1
% 3.71/1.04  --bmc1_ucm_init_mode                    2
% 3.71/1.04  --bmc1_ucm_cone_mode                    none
% 3.71/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.04  --bmc1_ucm_relax_model                  4
% 3.71/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.04  --bmc1_ucm_layered_model                none
% 3.71/1.04  --bmc1_ucm_max_lemma_size               10
% 3.71/1.04  
% 3.71/1.04  ------ AIG Options
% 3.71/1.04  
% 3.71/1.04  --aig_mode                              false
% 3.71/1.04  
% 3.71/1.04  ------ Instantiation Options
% 3.71/1.04  
% 3.71/1.04  --instantiation_flag                    true
% 3.71/1.04  --inst_sos_flag                         true
% 3.71/1.04  --inst_sos_phase                        true
% 3.71/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.04  --inst_lit_sel_side                     num_symb
% 3.71/1.04  --inst_solver_per_active                1400
% 3.71/1.04  --inst_solver_calls_frac                1.
% 3.71/1.04  --inst_passive_queue_type               priority_queues
% 3.71/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.04  --inst_passive_queues_freq              [25;2]
% 3.71/1.04  --inst_dismatching                      true
% 3.71/1.04  --inst_eager_unprocessed_to_passive     true
% 3.71/1.04  --inst_prop_sim_given                   true
% 3.71/1.04  --inst_prop_sim_new                     false
% 3.71/1.04  --inst_subs_new                         false
% 3.71/1.04  --inst_eq_res_simp                      false
% 3.71/1.04  --inst_subs_given                       false
% 3.71/1.04  --inst_orphan_elimination               true
% 3.71/1.04  --inst_learning_loop_flag               true
% 3.71/1.04  --inst_learning_start                   3000
% 3.71/1.04  --inst_learning_factor                  2
% 3.71/1.04  --inst_start_prop_sim_after_learn       3
% 3.71/1.04  --inst_sel_renew                        solver
% 3.71/1.04  --inst_lit_activity_flag                true
% 3.71/1.04  --inst_restr_to_given                   false
% 3.71/1.04  --inst_activity_threshold               500
% 3.71/1.04  --inst_out_proof                        true
% 3.71/1.04  
% 3.71/1.04  ------ Resolution Options
% 3.71/1.04  
% 3.71/1.04  --resolution_flag                       true
% 3.71/1.04  --res_lit_sel                           adaptive
% 3.71/1.04  --res_lit_sel_side                      none
% 3.71/1.04  --res_ordering                          kbo
% 3.71/1.04  --res_to_prop_solver                    active
% 3.71/1.04  --res_prop_simpl_new                    false
% 3.71/1.04  --res_prop_simpl_given                  true
% 3.71/1.04  --res_passive_queue_type                priority_queues
% 3.71/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.04  --res_passive_queues_freq               [15;5]
% 3.71/1.04  --res_forward_subs                      full
% 3.71/1.04  --res_backward_subs                     full
% 3.71/1.04  --res_forward_subs_resolution           true
% 3.71/1.04  --res_backward_subs_resolution          true
% 3.71/1.04  --res_orphan_elimination                true
% 3.71/1.04  --res_time_limit                        2.
% 3.71/1.04  --res_out_proof                         true
% 3.71/1.04  
% 3.71/1.04  ------ Superposition Options
% 3.71/1.04  
% 3.71/1.04  --superposition_flag                    true
% 3.71/1.04  --sup_passive_queue_type                priority_queues
% 3.71/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.04  --demod_completeness_check              fast
% 3.71/1.04  --demod_use_ground                      true
% 3.71/1.04  --sup_to_prop_solver                    passive
% 3.71/1.04  --sup_prop_simpl_new                    true
% 3.71/1.04  --sup_prop_simpl_given                  true
% 3.71/1.04  --sup_fun_splitting                     true
% 3.71/1.04  --sup_smt_interval                      50000
% 3.71/1.04  
% 3.71/1.04  ------ Superposition Simplification Setup
% 3.71/1.04  
% 3.71/1.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/1.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/1.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/1.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/1.04  --sup_immed_triv                        [TrivRules]
% 3.71/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.04  --sup_immed_bw_main                     []
% 3.71/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.04  --sup_input_bw                          []
% 3.71/1.04  
% 3.71/1.04  ------ Combination Options
% 3.71/1.04  
% 3.71/1.04  --comb_res_mult                         3
% 3.71/1.04  --comb_sup_mult                         2
% 3.71/1.04  --comb_inst_mult                        10
% 3.71/1.04  
% 3.71/1.04  ------ Debug Options
% 3.71/1.04  
% 3.71/1.04  --dbg_backtrace                         false
% 3.71/1.04  --dbg_dump_prop_clauses                 false
% 3.71/1.04  --dbg_dump_prop_clauses_file            -
% 3.71/1.04  --dbg_out_stat                          false
% 3.71/1.04  ------ Parsing...
% 3.71/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.04  ------ Proving...
% 3.71/1.04  ------ Problem Properties 
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  clauses                                 24
% 3.71/1.04  conjectures                             2
% 3.71/1.04  EPR                                     0
% 3.71/1.04  Horn                                    17
% 3.71/1.04  unary                                   8
% 3.71/1.04  binary                                  9
% 3.71/1.04  lits                                    48
% 3.71/1.04  lits eq                                 25
% 3.71/1.04  fd_pure                                 0
% 3.71/1.04  fd_pseudo                               0
% 3.71/1.04  fd_cond                                 3
% 3.71/1.04  fd_pseudo_cond                          4
% 3.71/1.04  AC symbols                              0
% 3.71/1.04  
% 3.71/1.04  ------ Schedule dynamic 5 is on 
% 3.71/1.04  
% 3.71/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  ------ 
% 3.71/1.04  Current options:
% 3.71/1.04  ------ 
% 3.71/1.04  
% 3.71/1.04  ------ Input Options
% 3.71/1.04  
% 3.71/1.04  --out_options                           all
% 3.71/1.04  --tptp_safe_out                         true
% 3.71/1.04  --problem_path                          ""
% 3.71/1.04  --include_path                          ""
% 3.71/1.04  --clausifier                            res/vclausify_rel
% 3.71/1.04  --clausifier_options                    ""
% 3.71/1.04  --stdin                                 false
% 3.71/1.04  --stats_out                             all
% 3.71/1.04  
% 3.71/1.04  ------ General Options
% 3.71/1.04  
% 3.71/1.04  --fof                                   false
% 3.71/1.04  --time_out_real                         305.
% 3.71/1.04  --time_out_virtual                      -1.
% 3.71/1.04  --symbol_type_check                     false
% 3.71/1.04  --clausify_out                          false
% 3.71/1.04  --sig_cnt_out                           false
% 3.71/1.04  --trig_cnt_out                          false
% 3.71/1.04  --trig_cnt_out_tolerance                1.
% 3.71/1.04  --trig_cnt_out_sk_spl                   false
% 3.71/1.04  --abstr_cl_out                          false
% 3.71/1.04  
% 3.71/1.04  ------ Global Options
% 3.71/1.04  
% 3.71/1.04  --schedule                              default
% 3.71/1.04  --add_important_lit                     false
% 3.71/1.04  --prop_solver_per_cl                    1000
% 3.71/1.04  --min_unsat_core                        false
% 3.71/1.04  --soft_assumptions                      false
% 3.71/1.04  --soft_lemma_size                       3
% 3.71/1.04  --prop_impl_unit_size                   0
% 3.71/1.04  --prop_impl_unit                        []
% 3.71/1.04  --share_sel_clauses                     true
% 3.71/1.04  --reset_solvers                         false
% 3.71/1.04  --bc_imp_inh                            [conj_cone]
% 3.71/1.04  --conj_cone_tolerance                   3.
% 3.71/1.04  --extra_neg_conj                        none
% 3.71/1.04  --large_theory_mode                     true
% 3.71/1.04  --prolific_symb_bound                   200
% 3.71/1.04  --lt_threshold                          2000
% 3.71/1.04  --clause_weak_htbl                      true
% 3.71/1.04  --gc_record_bc_elim                     false
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing Options
% 3.71/1.04  
% 3.71/1.04  --preprocessing_flag                    true
% 3.71/1.04  --time_out_prep_mult                    0.1
% 3.71/1.04  --splitting_mode                        input
% 3.71/1.04  --splitting_grd                         true
% 3.71/1.04  --splitting_cvd                         false
% 3.71/1.04  --splitting_cvd_svl                     false
% 3.71/1.04  --splitting_nvd                         32
% 3.71/1.04  --sub_typing                            true
% 3.71/1.04  --prep_gs_sim                           true
% 3.71/1.04  --prep_unflatten                        true
% 3.71/1.04  --prep_res_sim                          true
% 3.71/1.04  --prep_upred                            true
% 3.71/1.04  --prep_sem_filter                       exhaustive
% 3.71/1.04  --prep_sem_filter_out                   false
% 3.71/1.04  --pred_elim                             true
% 3.71/1.04  --res_sim_input                         true
% 3.71/1.04  --eq_ax_congr_red                       true
% 3.71/1.04  --pure_diseq_elim                       true
% 3.71/1.04  --brand_transform                       false
% 3.71/1.04  --non_eq_to_eq                          false
% 3.71/1.04  --prep_def_merge                        true
% 3.71/1.04  --prep_def_merge_prop_impl              false
% 3.71/1.04  --prep_def_merge_mbd                    true
% 3.71/1.04  --prep_def_merge_tr_red                 false
% 3.71/1.04  --prep_def_merge_tr_cl                  false
% 3.71/1.04  --smt_preprocessing                     true
% 3.71/1.04  --smt_ac_axioms                         fast
% 3.71/1.04  --preprocessed_out                      false
% 3.71/1.04  --preprocessed_stats                    false
% 3.71/1.04  
% 3.71/1.04  ------ Abstraction refinement Options
% 3.71/1.04  
% 3.71/1.04  --abstr_ref                             []
% 3.71/1.04  --abstr_ref_prep                        false
% 3.71/1.04  --abstr_ref_until_sat                   false
% 3.71/1.04  --abstr_ref_sig_restrict                funpre
% 3.71/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.04  --abstr_ref_under                       []
% 3.71/1.04  
% 3.71/1.04  ------ SAT Options
% 3.71/1.04  
% 3.71/1.04  --sat_mode                              false
% 3.71/1.04  --sat_fm_restart_options                ""
% 3.71/1.04  --sat_gr_def                            false
% 3.71/1.04  --sat_epr_types                         true
% 3.71/1.04  --sat_non_cyclic_types                  false
% 3.71/1.04  --sat_finite_models                     false
% 3.71/1.04  --sat_fm_lemmas                         false
% 3.71/1.04  --sat_fm_prep                           false
% 3.71/1.04  --sat_fm_uc_incr                        true
% 3.71/1.04  --sat_out_model                         small
% 3.71/1.04  --sat_out_clauses                       false
% 3.71/1.04  
% 3.71/1.04  ------ QBF Options
% 3.71/1.04  
% 3.71/1.04  --qbf_mode                              false
% 3.71/1.04  --qbf_elim_univ                         false
% 3.71/1.04  --qbf_dom_inst                          none
% 3.71/1.04  --qbf_dom_pre_inst                      false
% 3.71/1.04  --qbf_sk_in                             false
% 3.71/1.04  --qbf_pred_elim                         true
% 3.71/1.04  --qbf_split                             512
% 3.71/1.04  
% 3.71/1.04  ------ BMC1 Options
% 3.71/1.04  
% 3.71/1.04  --bmc1_incremental                      false
% 3.71/1.04  --bmc1_axioms                           reachable_all
% 3.71/1.04  --bmc1_min_bound                        0
% 3.71/1.04  --bmc1_max_bound                        -1
% 3.71/1.04  --bmc1_max_bound_default                -1
% 3.71/1.04  --bmc1_symbol_reachability              true
% 3.71/1.04  --bmc1_property_lemmas                  false
% 3.71/1.04  --bmc1_k_induction                      false
% 3.71/1.04  --bmc1_non_equiv_states                 false
% 3.71/1.04  --bmc1_deadlock                         false
% 3.71/1.04  --bmc1_ucm                              false
% 3.71/1.04  --bmc1_add_unsat_core                   none
% 3.71/1.04  --bmc1_unsat_core_children              false
% 3.71/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.04  --bmc1_out_stat                         full
% 3.71/1.04  --bmc1_ground_init                      false
% 3.71/1.04  --bmc1_pre_inst_next_state              false
% 3.71/1.04  --bmc1_pre_inst_state                   false
% 3.71/1.04  --bmc1_pre_inst_reach_state             false
% 3.71/1.04  --bmc1_out_unsat_core                   false
% 3.71/1.04  --bmc1_aig_witness_out                  false
% 3.71/1.04  --bmc1_verbose                          false
% 3.71/1.04  --bmc1_dump_clauses_tptp                false
% 3.71/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.04  --bmc1_dump_file                        -
% 3.71/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.04  --bmc1_ucm_extend_mode                  1
% 3.71/1.04  --bmc1_ucm_init_mode                    2
% 3.71/1.04  --bmc1_ucm_cone_mode                    none
% 3.71/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.04  --bmc1_ucm_relax_model                  4
% 3.71/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.04  --bmc1_ucm_layered_model                none
% 3.71/1.04  --bmc1_ucm_max_lemma_size               10
% 3.71/1.04  
% 3.71/1.04  ------ AIG Options
% 3.71/1.04  
% 3.71/1.04  --aig_mode                              false
% 3.71/1.04  
% 3.71/1.04  ------ Instantiation Options
% 3.71/1.04  
% 3.71/1.04  --instantiation_flag                    true
% 3.71/1.04  --inst_sos_flag                         true
% 3.71/1.04  --inst_sos_phase                        true
% 3.71/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.04  --inst_lit_sel_side                     none
% 3.71/1.04  --inst_solver_per_active                1400
% 3.71/1.04  --inst_solver_calls_frac                1.
% 3.71/1.04  --inst_passive_queue_type               priority_queues
% 3.71/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.04  --inst_passive_queues_freq              [25;2]
% 3.71/1.04  --inst_dismatching                      true
% 3.71/1.04  --inst_eager_unprocessed_to_passive     true
% 3.71/1.04  --inst_prop_sim_given                   true
% 3.71/1.04  --inst_prop_sim_new                     false
% 3.71/1.04  --inst_subs_new                         false
% 3.71/1.04  --inst_eq_res_simp                      false
% 3.71/1.04  --inst_subs_given                       false
% 3.71/1.04  --inst_orphan_elimination               true
% 3.71/1.04  --inst_learning_loop_flag               true
% 3.71/1.04  --inst_learning_start                   3000
% 3.71/1.04  --inst_learning_factor                  2
% 3.71/1.04  --inst_start_prop_sim_after_learn       3
% 3.71/1.04  --inst_sel_renew                        solver
% 3.71/1.04  --inst_lit_activity_flag                true
% 3.71/1.04  --inst_restr_to_given                   false
% 3.71/1.04  --inst_activity_threshold               500
% 3.71/1.04  --inst_out_proof                        true
% 3.71/1.04  
% 3.71/1.04  ------ Resolution Options
% 3.71/1.04  
% 3.71/1.04  --resolution_flag                       false
% 3.71/1.04  --res_lit_sel                           adaptive
% 3.71/1.04  --res_lit_sel_side                      none
% 3.71/1.04  --res_ordering                          kbo
% 3.71/1.04  --res_to_prop_solver                    active
% 3.71/1.04  --res_prop_simpl_new                    false
% 3.71/1.04  --res_prop_simpl_given                  true
% 3.71/1.04  --res_passive_queue_type                priority_queues
% 3.71/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.04  --res_passive_queues_freq               [15;5]
% 3.71/1.04  --res_forward_subs                      full
% 3.71/1.04  --res_backward_subs                     full
% 3.71/1.04  --res_forward_subs_resolution           true
% 3.71/1.04  --res_backward_subs_resolution          true
% 3.71/1.04  --res_orphan_elimination                true
% 3.71/1.04  --res_time_limit                        2.
% 3.71/1.04  --res_out_proof                         true
% 3.71/1.04  
% 3.71/1.04  ------ Superposition Options
% 3.71/1.04  
% 3.71/1.04  --superposition_flag                    true
% 3.71/1.04  --sup_passive_queue_type                priority_queues
% 3.71/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.04  --demod_completeness_check              fast
% 3.71/1.04  --demod_use_ground                      true
% 3.71/1.04  --sup_to_prop_solver                    passive
% 3.71/1.04  --sup_prop_simpl_new                    true
% 3.71/1.04  --sup_prop_simpl_given                  true
% 3.71/1.04  --sup_fun_splitting                     true
% 3.71/1.04  --sup_smt_interval                      50000
% 3.71/1.04  
% 3.71/1.04  ------ Superposition Simplification Setup
% 3.71/1.04  
% 3.71/1.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/1.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/1.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/1.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/1.04  --sup_immed_triv                        [TrivRules]
% 3.71/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.04  --sup_immed_bw_main                     []
% 3.71/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.04  --sup_input_bw                          []
% 3.71/1.04  
% 3.71/1.04  ------ Combination Options
% 3.71/1.04  
% 3.71/1.04  --comb_res_mult                         3
% 3.71/1.04  --comb_sup_mult                         2
% 3.71/1.04  --comb_inst_mult                        10
% 3.71/1.04  
% 3.71/1.04  ------ Debug Options
% 3.71/1.04  
% 3.71/1.04  --dbg_backtrace                         false
% 3.71/1.04  --dbg_dump_prop_clauses                 false
% 3.71/1.04  --dbg_dump_prop_clauses_file            -
% 3.71/1.04  --dbg_out_stat                          false
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  ------ Proving...
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  % SZS status Theorem for theBenchmark.p
% 3.71/1.04  
% 3.71/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.04  
% 3.71/1.04  fof(f18,axiom,(
% 3.71/1.04    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f22,plain,(
% 3.71/1.04    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.71/1.04    inference(ennf_transformation,[],[f18])).
% 3.71/1.04  
% 3.71/1.04  fof(f33,plain,(
% 3.71/1.04    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 3.71/1.04    introduced(choice_axiom,[])).
% 3.71/1.04  
% 3.71/1.04  fof(f34,plain,(
% 3.71/1.04    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 3.71/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f33])).
% 3.71/1.04  
% 3.71/1.04  fof(f66,plain,(
% 3.71/1.04    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.71/1.04    inference(cnf_transformation,[],[f34])).
% 3.71/1.04  
% 3.71/1.04  fof(f67,plain,(
% 3.71/1.04    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.71/1.04    inference(cnf_transformation,[],[f34])).
% 3.71/1.04  
% 3.71/1.04  fof(f65,plain,(
% 3.71/1.04    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.71/1.04    inference(cnf_transformation,[],[f34])).
% 3.71/1.04  
% 3.71/1.04  fof(f13,axiom,(
% 3.71/1.04    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f29,plain,(
% 3.71/1.04    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.71/1.04    inference(nnf_transformation,[],[f13])).
% 3.71/1.04  
% 3.71/1.04  fof(f56,plain,(
% 3.71/1.04    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.71/1.04    inference(cnf_transformation,[],[f29])).
% 3.71/1.04  
% 3.71/1.04  fof(f6,axiom,(
% 3.71/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f48,plain,(
% 3.71/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f6])).
% 3.71/1.04  
% 3.71/1.04  fof(f7,axiom,(
% 3.71/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f49,plain,(
% 3.71/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f7])).
% 3.71/1.04  
% 3.71/1.04  fof(f8,axiom,(
% 3.71/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f50,plain,(
% 3.71/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f8])).
% 3.71/1.04  
% 3.71/1.04  fof(f9,axiom,(
% 3.71/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f51,plain,(
% 3.71/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f9])).
% 3.71/1.04  
% 3.71/1.04  fof(f10,axiom,(
% 3.71/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f52,plain,(
% 3.71/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f10])).
% 3.71/1.04  
% 3.71/1.04  fof(f11,axiom,(
% 3.71/1.04    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f53,plain,(
% 3.71/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f11])).
% 3.71/1.04  
% 3.71/1.04  fof(f12,axiom,(
% 3.71/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f54,plain,(
% 3.71/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f12])).
% 3.71/1.04  
% 3.71/1.04  fof(f70,plain,(
% 3.71/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.71/1.04    inference(definition_unfolding,[],[f53,f54])).
% 3.71/1.04  
% 3.71/1.04  fof(f71,plain,(
% 3.71/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.71/1.04    inference(definition_unfolding,[],[f52,f70])).
% 3.71/1.04  
% 3.71/1.04  fof(f72,plain,(
% 3.71/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.71/1.04    inference(definition_unfolding,[],[f51,f71])).
% 3.71/1.04  
% 3.71/1.04  fof(f73,plain,(
% 3.71/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.71/1.04    inference(definition_unfolding,[],[f50,f72])).
% 3.71/1.04  
% 3.71/1.04  fof(f74,plain,(
% 3.71/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.71/1.04    inference(definition_unfolding,[],[f49,f73])).
% 3.71/1.04  
% 3.71/1.04  fof(f75,plain,(
% 3.71/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.71/1.04    inference(definition_unfolding,[],[f48,f74])).
% 3.71/1.04  
% 3.71/1.04  fof(f84,plain,(
% 3.71/1.04    ( ! [X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 3.71/1.04    inference(definition_unfolding,[],[f56,f75,f75,f75])).
% 3.71/1.04  
% 3.71/1.04  fof(f14,axiom,(
% 3.71/1.04    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f30,plain,(
% 3.71/1.04    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.71/1.04    inference(nnf_transformation,[],[f14])).
% 3.71/1.04  
% 3.71/1.04  fof(f57,plain,(
% 3.71/1.04    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.71/1.04    inference(cnf_transformation,[],[f30])).
% 3.71/1.04  
% 3.71/1.04  fof(f87,plain,(
% 3.71/1.04    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0) )),
% 3.71/1.04    inference(definition_unfolding,[],[f57,f75])).
% 3.71/1.04  
% 3.71/1.04  fof(f19,conjecture,(
% 3.71/1.04    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f20,negated_conjecture,(
% 3.71/1.04    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.71/1.04    inference(negated_conjecture,[],[f19])).
% 3.71/1.04  
% 3.71/1.04  fof(f23,plain,(
% 3.71/1.04    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 3.71/1.04    inference(ennf_transformation,[],[f20])).
% 3.71/1.04  
% 3.71/1.04  fof(f36,plain,(
% 3.71/1.04    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK3,sK4) = X0) )),
% 3.71/1.04    introduced(choice_axiom,[])).
% 3.71/1.04  
% 3.71/1.04  fof(f35,plain,(
% 3.71/1.04    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 3.71/1.04    introduced(choice_axiom,[])).
% 3.71/1.04  
% 3.71/1.04  fof(f37,plain,(
% 3.71/1.04    (k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & k4_tarski(sK3,sK4) = sK2),
% 3.71/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f36,f35])).
% 3.71/1.04  
% 3.71/1.04  fof(f69,plain,(
% 3.71/1.04    k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2),
% 3.71/1.04    inference(cnf_transformation,[],[f37])).
% 3.71/1.04  
% 3.71/1.04  fof(f68,plain,(
% 3.71/1.04    k4_tarski(sK3,sK4) = sK2),
% 3.71/1.04    inference(cnf_transformation,[],[f37])).
% 3.71/1.04  
% 3.71/1.04  fof(f17,axiom,(
% 3.71/1.04    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f63,plain,(
% 3.71/1.04    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.71/1.04    inference(cnf_transformation,[],[f17])).
% 3.71/1.04  
% 3.71/1.04  fof(f64,plain,(
% 3.71/1.04    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.71/1.04    inference(cnf_transformation,[],[f17])).
% 3.71/1.04  
% 3.71/1.04  fof(f4,axiom,(
% 3.71/1.04    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f46,plain,(
% 3.71/1.04    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.71/1.04    inference(cnf_transformation,[],[f4])).
% 3.71/1.04  
% 3.71/1.04  fof(f15,axiom,(
% 3.71/1.04    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.71/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f31,plain,(
% 3.71/1.04    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.71/1.04    inference(nnf_transformation,[],[f15])).
% 3.71/1.04  
% 3.71/1.04  fof(f32,plain,(
% 3.71/1.04    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.71/1.04    inference(flattening,[],[f31])).
% 3.71/1.04  
% 3.71/1.04  fof(f60,plain,(
% 3.71/1.04    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f32])).
% 3.71/1.04  
% 3.71/1.04  fof(f89,plain,(
% 3.71/1.04    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.71/1.04    inference(definition_unfolding,[],[f60,f74,f74])).
% 3.71/1.04  
% 3.71/1.04  fof(f58,plain,(
% 3.71/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f30])).
% 3.71/1.04  
% 3.71/1.04  fof(f86,plain,(
% 3.71/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.71/1.04    inference(definition_unfolding,[],[f58,f75])).
% 3.71/1.04  
% 3.71/1.04  fof(f55,plain,(
% 3.71/1.04    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f29])).
% 3.71/1.04  
% 3.71/1.04  fof(f85,plain,(
% 3.71/1.04    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.71/1.04    inference(definition_unfolding,[],[f55,f75,f75,f75])).
% 3.71/1.04  
% 3.71/1.04  fof(f95,plain,(
% 3.71/1.04    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.71/1.04    inference(equality_resolution,[],[f85])).
% 3.71/1.04  
% 3.71/1.04  cnf(c_224,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.71/1.04      theory(equality) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_639,plain,
% 3.71/1.04      ( r2_hidden(X0,X1)
% 3.71/1.04      | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 3.71/1.04      | X0 != X2
% 3.71/1.04      | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_224]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_701,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | X1 != X0
% 3.71/1.04      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_639]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_5323,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.71/1.04      | sK3 != X0 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_701]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_5325,plain,
% 3.71/1.04      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.71/1.04      | sK3 != sK2 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_5323]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_5291,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | r2_hidden(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.71/1.04      | sK4 != X0 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_701]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_5293,plain,
% 3.71/1.04      ( r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.71/1.04      | sK4 != sK2 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_5291]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_20,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,X1)
% 3.71/1.04      | k4_tarski(X0,X2) != sK1(X1)
% 3.71/1.04      | k1_xboole_0 = X1 ),
% 3.71/1.04      inference(cnf_transformation,[],[f66]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_723,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.71/1.04      | k4_tarski(X0,X2) != sK1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.71/1.04      | k1_xboole_0 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_20]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2504,plain,
% 3.71/1.04      ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | k4_tarski(sK3,sK4) != sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_723]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2506,plain,
% 3.71/1.04      ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | k4_tarski(sK3,sK4) != sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_2504]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_19,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,X1)
% 3.71/1.04      | k4_tarski(X2,X0) != sK1(X1)
% 3.71/1.04      | k1_xboole_0 = X1 ),
% 3.71/1.04      inference(cnf_transformation,[],[f67]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_722,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.71/1.04      | k4_tarski(X2,X0) != sK1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.71/1.04      | k1_xboole_0 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_19]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2499,plain,
% 3.71/1.04      ( ~ r2_hidden(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | k4_tarski(sK3,sK4) != sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_722]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2501,plain,
% 3.71/1.04      ( ~ r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | k4_tarski(sK3,sK4) != sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_2499]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_21,plain,
% 3.71/1.04      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.71/1.04      inference(cnf_transformation,[],[f65]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_559,plain,
% 3.71/1.04      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_9,plain,
% 3.71/1.04      ( X0 = X1
% 3.71/1.04      | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.71/1.04      inference(cnf_transformation,[],[f84]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_12,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,X1)
% 3.71/1.04      | k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != X1 ),
% 3.71/1.04      inference(cnf_transformation,[],[f87]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_565,plain,
% 3.71/1.04      ( k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0
% 3.71/1.04      | r2_hidden(X1,X0) != iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1718,plain,
% 3.71/1.04      ( X0 = X1
% 3.71/1.04      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_9,c_565]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1840,plain,
% 3.71/1.04      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 3.71/1.04      | sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_559,c_1718]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1841,plain,
% 3.71/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 3.71/1.04      | sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK2 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_1840]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_222,plain,
% 3.71/1.04      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 3.71/1.04      theory(equality) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1650,plain,
% 3.71/1.04      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0
% 3.71/1.04      | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 3.71/1.04      | k4_xboole_0(k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_222]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1651,plain,
% 3.71/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
% 3.71/1.04      | k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.71/1.04      | k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_1650]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_221,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_979,plain,
% 3.71/1.04      ( k4_tarski(X0,X1) != X2
% 3.71/1.04      | k4_tarski(X0,X1) = sK1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
% 3.71/1.04      | sK1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) != X2 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_221]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1528,plain,
% 3.71/1.04      ( k4_tarski(sK3,sK4) = sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | k4_tarski(sK3,sK4) != sK2
% 3.71/1.04      | sK1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != sK2 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_979]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1529,plain,
% 3.71/1.04      ( k4_tarski(sK3,sK4) = sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | k4_tarski(sK3,sK4) != sK2
% 3.71/1.04      | sK1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != sK2 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_1528]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_220,plain,( X0 = X0 ),theory(equality) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1245,plain,
% 3.71/1.04      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_220]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1246,plain,
% 3.71/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_1245]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_751,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
% 3.71/1.04      | k4_xboole_0(k4_xboole_0(X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k4_xboole_0(X1,X2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1075,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0))
% 3.71/1.04      | k4_xboole_0(k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_751]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_1077,plain,
% 3.71/1.04      ( ~ r2_hidden(sK2,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0))
% 3.71/1.04      | k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_1075]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_22,negated_conjecture,
% 3.71/1.04      ( k1_mcart_1(sK2) = sK2 | k2_mcart_1(sK2) = sK2 ),
% 3.71/1.04      inference(cnf_transformation,[],[f69]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_23,negated_conjecture,
% 3.71/1.04      ( k4_tarski(sK3,sK4) = sK2 ),
% 3.71/1.04      inference(cnf_transformation,[],[f68]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_18,plain,
% 3.71/1.04      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.71/1.04      inference(cnf_transformation,[],[f63]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_760,plain,
% 3.71/1.04      ( k1_mcart_1(sK2) = sK3 ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_23,c_18]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_820,plain,
% 3.71/1.04      ( k2_mcart_1(sK2) = sK2 | sK3 = sK2 ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_22,c_760]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_17,plain,
% 3.71/1.04      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.71/1.04      inference(cnf_transformation,[],[f64]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_706,plain,
% 3.71/1.04      ( k2_mcart_1(sK2) = sK4 ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_23,c_17]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_822,plain,
% 3.71/1.04      ( sK4 = sK2 | sK3 = sK2 ),
% 3.71/1.04      inference(demodulation,[status(thm)],[c_820,c_706]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_8,plain,
% 3.71/1.04      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.71/1.04      inference(cnf_transformation,[],[f46]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_816,plain,
% 3.71/1.04      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_8]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_817,plain,
% 3.71/1.04      ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_816]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_14,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,X1)
% 3.71/1.04      | k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0) ),
% 3.71/1.04      inference(cnf_transformation,[],[f89]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_774,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k1_xboole_0)
% 3.71/1.04      | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_14]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_776,plain,
% 3.71/1.04      ( ~ r2_hidden(sK2,k1_xboole_0)
% 3.71/1.04      | k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_774]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_695,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | r2_hidden(X1,k1_xboole_0)
% 3.71/1.04      | X1 != X0
% 3.71/1.04      | k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_639]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_697,plain,
% 3.71/1.04      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | r2_hidden(sK2,k1_xboole_0)
% 3.71/1.04      | sK2 != sK2
% 3.71/1.04      | k1_xboole_0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_695]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_670,plain,
% 3.71/1.04      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | r2_hidden(X1,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0))
% 3.71/1.04      | X1 != X0
% 3.71/1.04      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_639]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_672,plain,
% 3.71/1.04      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | r2_hidden(sK2,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0))
% 3.71/1.04      | k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.71/1.04      | sK2 != sK2 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_670]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_11,plain,
% 3.71/1.04      ( r2_hidden(X0,X1)
% 3.71/1.04      | k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X1 ),
% 3.71/1.04      inference(cnf_transformation,[],[f86]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_617,plain,
% 3.71/1.04      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.71/1.04      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_11]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_619,plain,
% 3.71/1.04      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 3.71/1.04      | k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_617]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_48,plain,
% 3.71/1.04      ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.71/1.04      | sK2 = sK2 ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_9]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_10,plain,
% 3.71/1.04      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.71/1.04      inference(cnf_transformation,[],[f95]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_47,plain,
% 3.71/1.04      ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(contradiction,plain,
% 3.71/1.04      ( $false ),
% 3.71/1.04      inference(minisat,
% 3.71/1.04                [status(thm)],
% 3.71/1.04                [c_5325,c_5293,c_2506,c_2501,c_1841,c_1651,c_1529,c_1246,
% 3.71/1.04                 c_1077,c_822,c_817,c_776,c_697,c_672,c_619,c_48,c_47,
% 3.71/1.04                 c_23]) ).
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.04  
% 3.71/1.04  ------                               Statistics
% 3.71/1.04  
% 3.71/1.04  ------ General
% 3.71/1.04  
% 3.71/1.04  abstr_ref_over_cycles:                  0
% 3.71/1.04  abstr_ref_under_cycles:                 0
% 3.71/1.04  gc_basic_clause_elim:                   0
% 3.71/1.04  forced_gc_time:                         0
% 3.71/1.04  parsing_time:                           0.01
% 3.71/1.04  unif_index_cands_time:                  0.
% 3.71/1.04  unif_index_add_time:                    0.
% 3.71/1.04  orderings_time:                         0.
% 3.71/1.04  out_proof_time:                         0.01
% 3.71/1.04  total_time:                             0.285
% 3.71/1.04  num_of_symbols:                         45
% 3.71/1.04  num_of_terms:                           8897
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing
% 3.71/1.04  
% 3.71/1.04  num_of_splits:                          0
% 3.71/1.04  num_of_split_atoms:                     0
% 3.71/1.04  num_of_reused_defs:                     0
% 3.71/1.04  num_eq_ax_congr_red:                    26
% 3.71/1.04  num_of_sem_filtered_clauses:            1
% 3.71/1.04  num_of_subtypes:                        0
% 3.71/1.04  monotx_restored_types:                  0
% 3.71/1.04  sat_num_of_epr_types:                   0
% 3.71/1.04  sat_num_of_non_cyclic_types:            0
% 3.71/1.04  sat_guarded_non_collapsed_types:        0
% 3.71/1.04  num_pure_diseq_elim:                    0
% 3.71/1.04  simp_replaced_by:                       0
% 3.71/1.04  res_preprocessed:                       91
% 3.71/1.04  prep_upred:                             0
% 3.71/1.04  prep_unflattend:                        0
% 3.71/1.04  smt_new_axioms:                         0
% 3.71/1.04  pred_elim_cands:                        1
% 3.71/1.04  pred_elim:                              0
% 3.71/1.04  pred_elim_cl:                           0
% 3.71/1.04  pred_elim_cycles:                       1
% 3.71/1.04  merged_defs:                            6
% 3.71/1.04  merged_defs_ncl:                        0
% 3.71/1.04  bin_hyper_res:                          6
% 3.71/1.04  prep_cycles:                            3
% 3.71/1.04  pred_elim_time:                         0.
% 3.71/1.04  splitting_time:                         0.
% 3.71/1.04  sem_filter_time:                        0.
% 3.71/1.04  monotx_time:                            0.
% 3.71/1.04  subtype_inf_time:                       0.
% 3.71/1.04  
% 3.71/1.04  ------ Problem properties
% 3.71/1.04  
% 3.71/1.04  clauses:                                24
% 3.71/1.04  conjectures:                            2
% 3.71/1.04  epr:                                    0
% 3.71/1.04  horn:                                   17
% 3.71/1.04  ground:                                 2
% 3.71/1.04  unary:                                  8
% 3.71/1.04  binary:                                 9
% 3.71/1.04  lits:                                   48
% 3.71/1.04  lits_eq:                                25
% 3.71/1.04  fd_pure:                                0
% 3.71/1.04  fd_pseudo:                              0
% 3.71/1.04  fd_cond:                                3
% 3.71/1.04  fd_pseudo_cond:                         4
% 3.71/1.04  ac_symbols:                             0
% 3.71/1.04  
% 3.71/1.04  ------ Propositional Solver
% 3.71/1.04  
% 3.71/1.04  prop_solver_calls:                      26
% 3.71/1.04  prop_fast_solver_calls:                 526
% 3.71/1.04  smt_solver_calls:                       0
% 3.71/1.04  smt_fast_solver_calls:                  0
% 3.71/1.04  prop_num_of_clauses:                    2008
% 3.71/1.04  prop_preprocess_simplified:             6381
% 3.71/1.04  prop_fo_subsumed:                       1
% 3.71/1.04  prop_solver_time:                       0.
% 3.71/1.04  smt_solver_time:                        0.
% 3.71/1.04  smt_fast_solver_time:                   0.
% 3.71/1.04  prop_fast_solver_time:                  0.
% 3.71/1.04  prop_unsat_core_time:                   0.
% 3.71/1.04  
% 3.71/1.04  ------ QBF
% 3.71/1.04  
% 3.71/1.04  qbf_q_res:                              0
% 3.71/1.04  qbf_num_tautologies:                    0
% 3.71/1.04  qbf_prep_cycles:                        0
% 3.71/1.04  
% 3.71/1.04  ------ BMC1
% 3.71/1.04  
% 3.71/1.04  bmc1_current_bound:                     -1
% 3.71/1.04  bmc1_last_solved_bound:                 -1
% 3.71/1.04  bmc1_unsat_core_size:                   -1
% 3.71/1.04  bmc1_unsat_core_parents_size:           -1
% 3.71/1.04  bmc1_merge_next_fun:                    0
% 3.71/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.71/1.04  
% 3.71/1.04  ------ Instantiation
% 3.71/1.04  
% 3.71/1.04  inst_num_of_clauses:                    618
% 3.71/1.04  inst_num_in_passive:                    400
% 3.71/1.04  inst_num_in_active:                     193
% 3.71/1.04  inst_num_in_unprocessed:                24
% 3.71/1.04  inst_num_of_loops:                      310
% 3.71/1.04  inst_num_of_learning_restarts:          0
% 3.71/1.04  inst_num_moves_active_passive:          114
% 3.71/1.04  inst_lit_activity:                      0
% 3.71/1.04  inst_lit_activity_moves:                0
% 3.71/1.04  inst_num_tautologies:                   0
% 3.71/1.04  inst_num_prop_implied:                  0
% 3.71/1.04  inst_num_existing_simplified:           0
% 3.71/1.04  inst_num_eq_res_simplified:             0
% 3.71/1.04  inst_num_child_elim:                    0
% 3.71/1.04  inst_num_of_dismatching_blockings:      603
% 3.71/1.04  inst_num_of_non_proper_insts:           847
% 3.71/1.04  inst_num_of_duplicates:                 0
% 3.71/1.04  inst_inst_num_from_inst_to_res:         0
% 3.71/1.04  inst_dismatching_checking_time:         0.
% 3.71/1.04  
% 3.71/1.04  ------ Resolution
% 3.71/1.04  
% 3.71/1.04  res_num_of_clauses:                     0
% 3.71/1.04  res_num_in_passive:                     0
% 3.71/1.04  res_num_in_active:                      0
% 3.71/1.04  res_num_of_loops:                       94
% 3.71/1.04  res_forward_subset_subsumed:            33
% 3.71/1.04  res_backward_subset_subsumed:           0
% 3.71/1.04  res_forward_subsumed:                   0
% 3.71/1.04  res_backward_subsumed:                  0
% 3.71/1.04  res_forward_subsumption_resolution:     0
% 3.71/1.04  res_backward_subsumption_resolution:    0
% 3.71/1.04  res_clause_to_clause_subsumption:       965
% 3.71/1.04  res_orphan_elimination:                 0
% 3.71/1.04  res_tautology_del:                      74
% 3.71/1.04  res_num_eq_res_simplified:              0
% 3.71/1.04  res_num_sel_changes:                    0
% 3.71/1.04  res_moves_from_active_to_pass:          0
% 3.71/1.04  
% 3.71/1.04  ------ Superposition
% 3.71/1.04  
% 3.71/1.04  sup_time_total:                         0.
% 3.71/1.04  sup_time_generating:                    0.
% 3.71/1.04  sup_time_sim_full:                      0.
% 3.71/1.04  sup_time_sim_immed:                     0.
% 3.71/1.04  
% 3.71/1.04  sup_num_of_clauses:                     147
% 3.71/1.04  sup_num_in_active:                      44
% 3.71/1.04  sup_num_in_passive:                     103
% 3.71/1.04  sup_num_of_loops:                       60
% 3.71/1.04  sup_fw_superposition:                   111
% 3.71/1.04  sup_bw_superposition:                   147
% 3.71/1.04  sup_immediate_simplified:               63
% 3.71/1.04  sup_given_eliminated:                   1
% 3.71/1.04  comparisons_done:                       0
% 3.71/1.04  comparisons_avoided:                    4
% 3.71/1.04  
% 3.71/1.04  ------ Simplifications
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  sim_fw_subset_subsumed:                 4
% 3.71/1.04  sim_bw_subset_subsumed:                 4
% 3.71/1.04  sim_fw_subsumed:                        28
% 3.71/1.04  sim_bw_subsumed:                        3
% 3.71/1.04  sim_fw_subsumption_res:                 0
% 3.71/1.04  sim_bw_subsumption_res:                 0
% 3.71/1.04  sim_tautology_del:                      28
% 3.71/1.04  sim_eq_tautology_del:                   22
% 3.71/1.04  sim_eq_res_simp:                        3
% 3.71/1.04  sim_fw_demodulated:                     48
% 3.71/1.04  sim_bw_demodulated:                     18
% 3.71/1.04  sim_light_normalised:                   14
% 3.71/1.04  sim_joinable_taut:                      0
% 3.71/1.04  sim_joinable_simp:                      0
% 3.71/1.04  sim_ac_normalised:                      0
% 3.71/1.04  sim_smt_subsumption:                    0
% 3.71/1.04  
%------------------------------------------------------------------------------
