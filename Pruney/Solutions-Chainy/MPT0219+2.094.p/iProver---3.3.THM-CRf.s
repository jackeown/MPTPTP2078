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
% DateTime   : Thu Dec  3 11:29:24 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 234 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :   11 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  195 ( 663 expanded)
%              Number of equality atoms :  156 ( 554 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f32])).

fof(f57,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f72,plain,(
    k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3))) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f57,f42,f59,f59,f59])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f51,f42,f59,f59])).

fof(f61,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f42,f59,f60])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) != X3 ) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f73,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5))))) != X3 ) ),
    inference(equality_resolution,[],[f67])).

fof(f74,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)))))) ),
    inference(equality_resolution,[],[f73])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))))) ),
    inference(definition_unfolding,[],[f54,f61,f60])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) != X3 ) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f79,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) != X3 ) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f77,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) != X3 ) ),
    inference(equality_resolution,[],[f69])).

fof(f78,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_xboole_0(k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))))) ),
    inference(equality_resolution,[],[f77])).

fof(f58,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3))) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_13,plain,
    ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_570,plain,
    ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2223,plain,
    ( r2_hidden(sK3,k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_570])).

cnf(c_17,plain,
    ( k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))))) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)))),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3))))))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_567,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)))),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1146,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X1,k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_567])).

cnf(c_2475,plain,
    ( sK3 = X0
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_2223,c_1146])).

cnf(c_2477,plain,
    ( sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_2475])).

cnf(c_306,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_625,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_626,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_15,plain,
    ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,plain,
    ( r2_hidden(sK2,k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)))),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_22,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)))),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))))))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2477,c_626,c_25,c_22,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.33/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/0.99  
% 3.33/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/0.99  
% 3.33/0.99  ------  iProver source info
% 3.33/0.99  
% 3.33/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.33/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/0.99  git: non_committed_changes: false
% 3.33/0.99  git: last_make_outside_of_git: false
% 3.33/0.99  
% 3.33/0.99  ------ 
% 3.33/0.99  ------ Parsing...
% 3.33/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/0.99  ------ Proving...
% 3.33/0.99  ------ Problem Properties 
% 3.33/0.99  
% 3.33/0.99  
% 3.33/0.99  clauses                                 19
% 3.33/0.99  conjectures                             2
% 3.33/0.99  EPR                                     2
% 3.33/0.99  Horn                                    17
% 3.33/0.99  unary                                   10
% 3.33/0.99  binary                                  4
% 3.33/0.99  lits                                    36
% 3.33/0.99  lits eq                                 19
% 3.33/1.00  fd_pure                                 0
% 3.33/1.00  fd_pseudo                               0
% 3.33/1.00  fd_cond                                 1
% 3.33/1.00  fd_pseudo_cond                          4
% 3.33/1.00  AC symbols                              0
% 3.33/1.00  
% 3.33/1.00  ------ Input Options Time Limit: Unbounded
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ 
% 3.33/1.00  Current options:
% 3.33/1.00  ------ 
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ Proving...
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS status Theorem for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  fof(f16,conjecture,(
% 3.33/1.00    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f17,negated_conjecture,(
% 3.33/1.00    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.33/1.00    inference(negated_conjecture,[],[f16])).
% 3.33/1.00  
% 3.33/1.00  fof(f24,plain,(
% 3.33/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f17])).
% 3.33/1.00  
% 3.33/1.00  fof(f32,plain,(
% 3.33/1.00    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f33,plain,(
% 3.33/1.00    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f32])).
% 3.33/1.00  
% 3.33/1.00  fof(f57,plain,(
% 3.33/1.00    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.33/1.00    inference(cnf_transformation,[],[f33])).
% 3.33/1.00  
% 3.33/1.00  fof(f8,axiom,(
% 3.33/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f42,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f8])).
% 3.33/1.00  
% 3.33/1.00  fof(f15,axiom,(
% 3.33/1.00    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f56,plain,(
% 3.33/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f15])).
% 3.33/1.00  
% 3.33/1.00  fof(f14,axiom,(
% 3.33/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f55,plain,(
% 3.33/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f14])).
% 3.33/1.00  
% 3.33/1.00  fof(f59,plain,(
% 3.33/1.00    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 3.33/1.00    inference(definition_unfolding,[],[f56,f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f72,plain,(
% 3.33/1.00    k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3))) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),
% 3.33/1.00    inference(definition_unfolding,[],[f57,f42,f59,f59,f59])).
% 3.33/1.00  
% 3.33/1.00  fof(f9,axiom,(
% 3.33/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f23,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.33/1.00    inference(ennf_transformation,[],[f9])).
% 3.33/1.00  
% 3.33/1.00  fof(f27,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.33/1.00    inference(nnf_transformation,[],[f23])).
% 3.33/1.00  
% 3.33/1.00  fof(f28,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.33/1.00    inference(flattening,[],[f27])).
% 3.33/1.00  
% 3.33/1.00  fof(f29,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.33/1.00    inference(rectify,[],[f28])).
% 3.33/1.00  
% 3.33/1.00  fof(f30,plain,(
% 3.33/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f31,plain,(
% 3.33/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.33/1.00  
% 3.33/1.00  fof(f46,plain,(
% 3.33/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.33/1.00    inference(cnf_transformation,[],[f31])).
% 3.33/1.00  
% 3.33/1.00  fof(f11,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f52,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f11])).
% 3.33/1.00  
% 3.33/1.00  fof(f10,axiom,(
% 3.33/1.00    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f51,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f10])).
% 3.33/1.00  
% 3.33/1.00  fof(f60,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))) = k2_tarski(X0,X1)) )),
% 3.33/1.00    inference(definition_unfolding,[],[f51,f42,f59,f59])).
% 3.33/1.00  
% 3.33/1.00  fof(f61,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) = k1_enumset1(X0,X1,X2)) )),
% 3.33/1.00    inference(definition_unfolding,[],[f52,f42,f59,f60])).
% 3.33/1.00  
% 3.33/1.00  fof(f67,plain,(
% 3.33/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) != X3) )),
% 3.33/1.00    inference(definition_unfolding,[],[f46,f61])).
% 3.33/1.00  
% 3.33/1.00  fof(f73,plain,(
% 3.33/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5))))) != X3) )),
% 3.33/1.00    inference(equality_resolution,[],[f67])).
% 3.33/1.00  
% 3.33/1.00  fof(f74,plain,(
% 3.33/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X5,X5,X5,X5,X5,X5))))))) )),
% 3.33/1.00    inference(equality_resolution,[],[f73])).
% 3.33/1.00  
% 3.33/1.00  fof(f13,axiom,(
% 3.33/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f54,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f13])).
% 3.33/1.00  
% 3.33/1.00  fof(f71,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))))) )),
% 3.33/1.00    inference(definition_unfolding,[],[f54,f61,f60])).
% 3.33/1.00  
% 3.33/1.00  fof(f43,plain,(
% 3.33/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.33/1.00    inference(cnf_transformation,[],[f31])).
% 3.33/1.00  
% 3.33/1.00  fof(f70,plain,(
% 3.33/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) != X3) )),
% 3.33/1.00    inference(definition_unfolding,[],[f43,f61])).
% 3.33/1.00  
% 3.33/1.00  fof(f79,plain,(
% 3.33/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))))) )),
% 3.33/1.00    inference(equality_resolution,[],[f70])).
% 3.33/1.00  
% 3.33/1.00  fof(f44,plain,(
% 3.33/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.33/1.00    inference(cnf_transformation,[],[f31])).
% 3.33/1.00  
% 3.33/1.00  fof(f69,plain,(
% 3.33/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) != X3) )),
% 3.33/1.00    inference(definition_unfolding,[],[f44,f61])).
% 3.33/1.00  
% 3.33/1.00  fof(f77,plain,(
% 3.33/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))) != X3) )),
% 3.33/1.00    inference(equality_resolution,[],[f69])).
% 3.33/1.00  
% 3.33/1.00  fof(f78,plain,(
% 3.33/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_xboole_0(k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))))))) )),
% 3.33/1.00    inference(equality_resolution,[],[f77])).
% 3.33/1.00  
% 3.33/1.00  fof(f58,plain,(
% 3.33/1.00    sK2 != sK3),
% 3.33/1.00    inference(cnf_transformation,[],[f33])).
% 3.33/1.00  
% 3.33/1.00  cnf(c_19,negated_conjecture,
% 3.33/1.00      ( k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3))) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.33/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_13,plain,
% 3.33/1.00      ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_570,plain,
% 3.33/1.00      ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))))) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2223,plain,
% 3.33/1.00      ( r2_hidden(sK3,k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_19,c_570]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_17,plain,
% 3.33/1.00      ( k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))))) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_16,plain,
% 3.33/1.00      ( ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)))),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3))))))
% 3.33/1.00      | X0 = X1
% 3.33/1.00      | X0 = X2
% 3.33/1.00      | X0 = X3 ),
% 3.33/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_567,plain,
% 3.33/1.00      ( X0 = X1
% 3.33/1.00      | X0 = X2
% 3.33/1.00      | X0 = X3
% 3.33/1.00      | r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)))),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)))))) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1146,plain,
% 3.33/1.00      ( X0 = X1
% 3.33/1.00      | X2 = X1
% 3.33/1.00      | r2_hidden(X1,k5_xboole_0(k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X0,X0,X0,X0,X0,X0)))) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_17,c_567]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2475,plain,
% 3.33/1.00      ( sK3 = X0 | sK3 = sK2 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_2223,c_1146]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2477,plain,
% 3.33/1.00      ( sK3 = sK2 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_2475]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_306,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_625,plain,
% 3.33/1.00      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_306]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_626,plain,
% 3.33/1.00      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_625]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_15,plain,
% 3.33/1.00      ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)),k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))))) ),
% 3.33/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_25,plain,
% 3.33/1.00      ( r2_hidden(sK2,k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)))),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_22,plain,
% 3.33/1.00      ( ~ r2_hidden(sK2,k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)))),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))))))
% 3.33/1.00      | sK2 = sK2 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_18,negated_conjecture,
% 3.33/1.00      ( sK2 != sK3 ),
% 3.33/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(contradiction,plain,
% 3.33/1.00      ( $false ),
% 3.33/1.00      inference(minisat,[status(thm)],[c_2477,c_626,c_25,c_22,c_18]) ).
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  ------                               Statistics
% 3.33/1.00  
% 3.33/1.00  ------ Selected
% 3.33/1.00  
% 3.33/1.00  total_time:                             0.28
% 3.33/1.00  
%------------------------------------------------------------------------------
