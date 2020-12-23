%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:50 EST 2020

% Result     : Theorem 27.54s
% Output     : CNFRefutation 27.54s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 290 expanded)
%              Number of clauses        :   65 (  85 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  342 (1028 expanded)
%              Number of equality atoms :  123 ( 218 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f34])).

fof(f61,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f60,f46,f66])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f62,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f63,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(definition_unfolding,[],[f63,f65])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_110625,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_110630,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_110614,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_110618,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_110629,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_111091,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_enumset1(X2,X2,X2,X2)) = k4_xboole_0(X0,X1)
    | r2_hidden(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_110618,c_110629])).

cnf(c_111164,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k4_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_110614,c_111091])).

cnf(c_14,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_110621,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_110627,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_110846,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_110621,c_110627])).

cnf(c_111553,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k4_xboole_0(X0,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_111164,c_110846])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_291,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_292,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0)
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_110611,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_112130,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_111553,c_110611])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7,negated_conjecture,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_110626,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_110816,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X0,X1)) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_110626])).

cnf(c_112161,plain,
    ( r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_112130,c_110816])).

cnf(c_112224,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_110630,c_112161])).

cnf(c_132086,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_110625,c_112224])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_68997,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_69008,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_69194,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_68997,c_69008])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_69001,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_69239,plain,
    ( k4_xboole_0(sK3,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_69194,c_69001])).

cnf(c_69011,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_69006,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_69010,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_69418,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_69006,c_69010])).

cnf(c_69664,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_69011,c_69418])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_69009,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_69417,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_69006,c_69009])).

cnf(c_82973,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_69664,c_69417])).

cnf(c_82983,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_82973,c_69010])).

cnf(c_83573,plain,
    ( r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK1(X0,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_69239,c_82983])).

cnf(c_83696,plain,
    ( r1_xboole_0(X0,sK3) = iProver_top
    | r2_hidden(sK1(X0,sK3),sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_83573,c_69239])).

cnf(c_83774,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK3),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_83696])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29478,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_29482,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_29996,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_29478,c_29482])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29472,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_35491,plain,
    ( r1_xboole_0(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_29996,c_29472])).

cnf(c_32647,plain,
    ( ~ r1_xboole_0(X0,sK3)
    | r1_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_32648,plain,
    ( r1_xboole_0(X0,sK3) != iProver_top
    | r1_xboole_0(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32647])).

cnf(c_32650,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32648])).

cnf(c_1942,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1943,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1942])).

cnf(c_25,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_132086,c_83774,c_35491,c_32650,c_1943,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.54/3.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.54/3.99  
% 27.54/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.54/3.99  
% 27.54/3.99  ------  iProver source info
% 27.54/3.99  
% 27.54/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.54/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.54/3.99  git: non_committed_changes: false
% 27.54/3.99  git: last_make_outside_of_git: false
% 27.54/3.99  
% 27.54/3.99  ------ 
% 27.54/3.99  ------ Parsing...
% 27.54/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  ------ Proving...
% 27.54/3.99  ------ Problem Properties 
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  clauses                                 22
% 27.54/3.99  conjectures                             6
% 27.54/3.99  EPR                                     3
% 27.54/3.99  Horn                                    16
% 27.54/3.99  unary                                   5
% 27.54/3.99  binary                                  12
% 27.54/3.99  lits                                    45
% 27.54/3.99  lits eq                                 8
% 27.54/3.99  fd_pure                                 0
% 27.54/3.99  fd_pseudo                               0
% 27.54/3.99  fd_cond                                 0
% 27.54/3.99  fd_pseudo_cond                          3
% 27.54/3.99  AC symbols                              0
% 27.54/3.99  
% 27.54/3.99  ------ Input Options Time Limit: Unbounded
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing...
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 27.54/3.99  Current options:
% 27.54/3.99  ------ 
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.54/3.99  
% 27.54/3.99  ------ Proving...
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  % SZS status Theorem for theBenchmark.p
% 27.54/3.99  
% 27.54/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.54/3.99  
% 27.54/3.99  fof(f3,axiom,(
% 27.54/3.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f17,plain,(
% 27.54/3.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.54/3.99    inference(rectify,[],[f3])).
% 27.54/3.99  
% 27.54/3.99  fof(f19,plain,(
% 27.54/3.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.54/3.99    inference(ennf_transformation,[],[f17])).
% 27.54/3.99  
% 27.54/3.99  fof(f30,plain,(
% 27.54/3.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 27.54/3.99    introduced(choice_axiom,[])).
% 27.54/3.99  
% 27.54/3.99  fof(f31,plain,(
% 27.54/3.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.54/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f30])).
% 27.54/3.99  
% 27.54/3.99  fof(f43,plain,(
% 27.54/3.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f31])).
% 27.54/3.99  
% 27.54/3.99  fof(f5,axiom,(
% 27.54/3.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f46,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f5])).
% 27.54/3.99  
% 27.54/3.99  fof(f68,plain,(
% 27.54/3.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f43,f46])).
% 27.54/3.99  
% 27.54/3.99  fof(f1,axiom,(
% 27.54/3.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f25,plain,(
% 27.54/3.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.54/3.99    inference(nnf_transformation,[],[f1])).
% 27.54/3.99  
% 27.54/3.99  fof(f26,plain,(
% 27.54/3.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.54/3.99    inference(flattening,[],[f25])).
% 27.54/3.99  
% 27.54/3.99  fof(f27,plain,(
% 27.54/3.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.54/3.99    inference(rectify,[],[f26])).
% 27.54/3.99  
% 27.54/3.99  fof(f28,plain,(
% 27.54/3.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 27.54/3.99    introduced(choice_axiom,[])).
% 27.54/3.99  
% 27.54/3.99  fof(f29,plain,(
% 27.54/3.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 27.54/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 27.54/3.99  
% 27.54/3.99  fof(f38,plain,(
% 27.54/3.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 27.54/3.99    inference(cnf_transformation,[],[f29])).
% 27.54/3.99  
% 27.54/3.99  fof(f77,plain,(
% 27.54/3.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 27.54/3.99    inference(equality_resolution,[],[f38])).
% 27.54/3.99  
% 27.54/3.99  fof(f15,conjecture,(
% 27.54/3.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f16,negated_conjecture,(
% 27.54/3.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 27.54/3.99    inference(negated_conjecture,[],[f15])).
% 27.54/3.99  
% 27.54/3.99  fof(f23,plain,(
% 27.54/3.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 27.54/3.99    inference(ennf_transformation,[],[f16])).
% 27.54/3.99  
% 27.54/3.99  fof(f24,plain,(
% 27.54/3.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 27.54/3.99    inference(flattening,[],[f23])).
% 27.54/3.99  
% 27.54/3.99  fof(f34,plain,(
% 27.54/3.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 27.54/3.99    introduced(choice_axiom,[])).
% 27.54/3.99  
% 27.54/3.99  fof(f35,plain,(
% 27.54/3.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 27.54/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f34])).
% 27.54/3.99  
% 27.54/3.99  fof(f61,plain,(
% 27.54/3.99    r2_hidden(sK5,sK4)),
% 27.54/3.99    inference(cnf_transformation,[],[f35])).
% 27.54/3.99  
% 27.54/3.99  fof(f14,axiom,(
% 27.54/3.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f33,plain,(
% 27.54/3.99    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 27.54/3.99    inference(nnf_transformation,[],[f14])).
% 27.54/3.99  
% 27.54/3.99  fof(f59,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f33])).
% 27.54/3.99  
% 27.54/3.99  fof(f10,axiom,(
% 27.54/3.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f54,plain,(
% 27.54/3.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f10])).
% 27.54/3.99  
% 27.54/3.99  fof(f11,axiom,(
% 27.54/3.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f55,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f11])).
% 27.54/3.99  
% 27.54/3.99  fof(f12,axiom,(
% 27.54/3.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f56,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f12])).
% 27.54/3.99  
% 27.54/3.99  fof(f64,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f55,f56])).
% 27.54/3.99  
% 27.54/3.99  fof(f66,plain,(
% 27.54/3.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f54,f64])).
% 27.54/3.99  
% 27.54/3.99  fof(f73,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 27.54/3.99    inference(definition_unfolding,[],[f59,f66])).
% 27.54/3.99  
% 27.54/3.99  fof(f37,plain,(
% 27.54/3.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 27.54/3.99    inference(cnf_transformation,[],[f29])).
% 27.54/3.99  
% 27.54/3.99  fof(f78,plain,(
% 27.54/3.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 27.54/3.99    inference(equality_resolution,[],[f37])).
% 27.54/3.99  
% 27.54/3.99  fof(f8,axiom,(
% 27.54/3.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f51,plain,(
% 27.54/3.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f8])).
% 27.54/3.99  
% 27.54/3.99  fof(f2,axiom,(
% 27.54/3.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f18,plain,(
% 27.54/3.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 27.54/3.99    inference(ennf_transformation,[],[f2])).
% 27.54/3.99  
% 27.54/3.99  fof(f42,plain,(
% 27.54/3.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f18])).
% 27.54/3.99  
% 27.54/3.99  fof(f6,axiom,(
% 27.54/3.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f20,plain,(
% 27.54/3.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 27.54/3.99    inference(ennf_transformation,[],[f6])).
% 27.54/3.99  
% 27.54/3.99  fof(f21,plain,(
% 27.54/3.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 27.54/3.99    inference(flattening,[],[f20])).
% 27.54/3.99  
% 27.54/3.99  fof(f47,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f21])).
% 27.54/3.99  
% 27.54/3.99  fof(f60,plain,(
% 27.54/3.99    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 27.54/3.99    inference(cnf_transformation,[],[f35])).
% 27.54/3.99  
% 27.54/3.99  fof(f76,plain,(
% 27.54/3.99    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))),
% 27.54/3.99    inference(definition_unfolding,[],[f60,f46,f66])).
% 27.54/3.99  
% 27.54/3.99  fof(f4,axiom,(
% 27.54/3.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f45,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.54/3.99    inference(cnf_transformation,[],[f4])).
% 27.54/3.99  
% 27.54/3.99  fof(f69,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.54/3.99    inference(definition_unfolding,[],[f45,f46])).
% 27.54/3.99  
% 27.54/3.99  fof(f44,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 27.54/3.99    inference(cnf_transformation,[],[f31])).
% 27.54/3.99  
% 27.54/3.99  fof(f67,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.54/3.99    inference(definition_unfolding,[],[f44,f46])).
% 27.54/3.99  
% 27.54/3.99  fof(f62,plain,(
% 27.54/3.99    r1_xboole_0(sK4,sK3)),
% 27.54/3.99    inference(cnf_transformation,[],[f35])).
% 27.54/3.99  
% 27.54/3.99  fof(f9,axiom,(
% 27.54/3.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f32,plain,(
% 27.54/3.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 27.54/3.99    inference(nnf_transformation,[],[f9])).
% 27.54/3.99  
% 27.54/3.99  fof(f52,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 27.54/3.99    inference(cnf_transformation,[],[f32])).
% 27.54/3.99  
% 27.54/3.99  fof(f36,plain,(
% 27.54/3.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 27.54/3.99    inference(cnf_transformation,[],[f29])).
% 27.54/3.99  
% 27.54/3.99  fof(f79,plain,(
% 27.54/3.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 27.54/3.99    inference(equality_resolution,[],[f36])).
% 27.54/3.99  
% 27.54/3.99  fof(f7,axiom,(
% 27.54/3.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f22,plain,(
% 27.54/3.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 27.54/3.99    inference(ennf_transformation,[],[f7])).
% 27.54/3.99  
% 27.54/3.99  fof(f48,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 27.54/3.99    inference(cnf_transformation,[],[f22])).
% 27.54/3.99  
% 27.54/3.99  fof(f13,axiom,(
% 27.54/3.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 27.54/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.54/3.99  
% 27.54/3.99  fof(f57,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 27.54/3.99    inference(cnf_transformation,[],[f13])).
% 27.54/3.99  
% 27.54/3.99  fof(f65,plain,(
% 27.54/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 27.54/3.99    inference(definition_unfolding,[],[f57,f64])).
% 27.54/3.99  
% 27.54/3.99  fof(f72,plain,(
% 27.54/3.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 27.54/3.99    inference(definition_unfolding,[],[f48,f65])).
% 27.54/3.99  
% 27.54/3.99  fof(f63,plain,(
% 27.54/3.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 27.54/3.99    inference(cnf_transformation,[],[f35])).
% 27.54/3.99  
% 27.54/3.99  fof(f75,plain,(
% 27.54/3.99    ~r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)),
% 27.54/3.99    inference(definition_unfolding,[],[f63,f65])).
% 27.54/3.99  
% 27.54/3.99  cnf(c_8,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1)
% 27.54/3.99      | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 27.54/3.99      inference(cnf_transformation,[],[f68]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110625,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_3,plain,
% 27.54/3.99      ( ~ r2_hidden(X0,X1)
% 27.54/3.99      | r2_hidden(X0,X2)
% 27.54/3.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 27.54/3.99      inference(cnf_transformation,[],[f77]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110630,plain,
% 27.54/3.99      ( r2_hidden(X0,X1) != iProver_top
% 27.54/3.99      | r2_hidden(X0,X2) = iProver_top
% 27.54/3.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_21,negated_conjecture,
% 27.54/3.99      ( r2_hidden(sK5,sK4) ),
% 27.54/3.99      inference(cnf_transformation,[],[f61]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110614,plain,
% 27.54/3.99      ( r2_hidden(sK5,sK4) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_17,plain,
% 27.54/3.99      ( r2_hidden(X0,X1)
% 27.54/3.99      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 27.54/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110618,plain,
% 27.54/3.99      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 27.54/3.99      | r2_hidden(X1,X0) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_4,negated_conjecture,
% 27.54/3.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 27.54/3.99      inference(cnf_transformation,[],[f78]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110629,plain,
% 27.54/3.99      ( r2_hidden(X0,X1) != iProver_top
% 27.54/3.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_111091,plain,
% 27.54/3.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_enumset1(X2,X2,X2,X2)) = k4_xboole_0(X0,X1)
% 27.54/3.99      | r2_hidden(X2,X1) != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_110618,c_110629]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_111164,plain,
% 27.54/3.99      ( k4_xboole_0(k4_xboole_0(X0,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k4_xboole_0(X0,sK4) ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_110614,c_111091]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_14,plain,
% 27.54/3.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 27.54/3.99      inference(cnf_transformation,[],[f51]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110621,plain,
% 27.54/3.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_6,plain,
% 27.54/3.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 27.54/3.99      inference(cnf_transformation,[],[f42]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110627,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) != iProver_top
% 27.54/3.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110846,plain,
% 27.54/3.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_110621,c_110627]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_111553,plain,
% 27.54/3.99      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k4_xboole_0(X0,sK4)) = iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_111164,c_110846]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_10,plain,
% 27.54/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 27.54/3.99      inference(cnf_transformation,[],[f47]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_22,negated_conjecture,
% 27.54/3.99      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 27.54/3.99      inference(cnf_transformation,[],[f76]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_291,plain,
% 27.54/3.99      ( ~ r1_xboole_0(X0,X1)
% 27.54/3.99      | r1_xboole_0(X2,X1)
% 27.54/3.99      | k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 27.54/3.99      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X2 ),
% 27.54/3.99      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_292,plain,
% 27.54/3.99      ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0)
% 27.54/3.99      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) ),
% 27.54/3.99      inference(unflattening,[status(thm)],[c_291]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110611,plain,
% 27.54/3.99      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0) != iProver_top
% 27.54/3.99      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_112130,plain,
% 27.54/3.99      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,sK4)) = iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_111553,c_110611]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_9,plain,
% 27.54/3.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.54/3.99      inference(cnf_transformation,[],[f69]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_7,negated_conjecture,
% 27.54/3.99      ( ~ r1_xboole_0(X0,X1)
% 27.54/3.99      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 27.54/3.99      inference(cnf_transformation,[],[f67]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110626,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) != iProver_top
% 27.54/3.99      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_110816,plain,
% 27.54/3.99      ( r1_xboole_0(X0,k4_xboole_0(X0,X1)) != iProver_top
% 27.54/3.99      | r2_hidden(X2,k4_xboole_0(X0,X1)) != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_9,c_110626]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_112161,plain,
% 27.54/3.99      ( r2_hidden(X0,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK4)) != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_112130,c_110816]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_112224,plain,
% 27.54/3.99      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
% 27.54/3.99      | r2_hidden(X0,sK4) = iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_110630,c_112161]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_132086,plain,
% 27.54/3.99      ( r1_xboole_0(sK2,sK3) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(sK2,sK3),sK4) = iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_110625,c_112224]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_20,negated_conjecture,
% 27.54/3.99      ( r1_xboole_0(sK4,sK3) ),
% 27.54/3.99      inference(cnf_transformation,[],[f62]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_68997,plain,
% 27.54/3.99      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69008,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) != iProver_top
% 27.54/3.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69194,plain,
% 27.54/3.99      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_68997,c_69008]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_16,plain,
% 27.54/3.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 27.54/3.99      inference(cnf_transformation,[],[f52]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69001,plain,
% 27.54/3.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69239,plain,
% 27.54/3.99      ( k4_xboole_0(sK3,sK4) = sK3 ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_69194,c_69001]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69011,plain,
% 27.54/3.99      ( r2_hidden(X0,X1) != iProver_top
% 27.54/3.99      | r2_hidden(X0,X2) = iProver_top
% 27.54/3.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69006,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69010,plain,
% 27.54/3.99      ( r2_hidden(X0,X1) != iProver_top
% 27.54/3.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69418,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,X1)) != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_69006,c_69010]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69664,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,X1),X0) != iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_69011,c_69418]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_5,plain,
% 27.54/3.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 27.54/3.99      inference(cnf_transformation,[],[f79]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69009,plain,
% 27.54/3.99      ( r2_hidden(X0,X1) = iProver_top
% 27.54/3.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_69417,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_69006,c_69009]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_82973,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 27.54/3.99      inference(global_propositional_subsumption,
% 27.54/3.99                [status(thm)],
% 27.54/3.99                [c_69664,c_69417]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_82983,plain,
% 27.54/3.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_82973,c_69010]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_83573,plain,
% 27.54/3.99      ( r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,sK3),sK4) != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_69239,c_82983]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_83696,plain,
% 27.54/3.99      ( r1_xboole_0(X0,sK3) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(X0,sK3),sK4) != iProver_top ),
% 27.54/3.99      inference(light_normalisation,[status(thm)],[c_83573,c_69239]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_83774,plain,
% 27.54/3.99      ( r1_xboole_0(sK2,sK3) = iProver_top
% 27.54/3.99      | r2_hidden(sK1(sK2,sK3),sK4) != iProver_top ),
% 27.54/3.99      inference(instantiation,[status(thm)],[c_83696]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_13,plain,
% 27.54/3.99      ( ~ r1_xboole_0(X0,X1)
% 27.54/3.99      | ~ r1_xboole_0(X0,X2)
% 27.54/3.99      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
% 27.54/3.99      inference(cnf_transformation,[],[f72]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_29478,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) != iProver_top
% 27.54/3.99      | r1_xboole_0(X0,X2) != iProver_top
% 27.54/3.99      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_29482,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) != iProver_top
% 27.54/3.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_29996,plain,
% 27.54/3.99      ( r1_xboole_0(X0,X1) != iProver_top
% 27.54/3.99      | r1_xboole_0(X0,X2) != iProver_top
% 27.54/3.99      | r1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0) = iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_29478,c_29482]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_19,negated_conjecture,
% 27.54/3.99      ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
% 27.54/3.99      inference(cnf_transformation,[],[f75]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_29472,plain,
% 27.54/3.99      ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_35491,plain,
% 27.54/3.99      ( r1_xboole_0(sK3,sK4) != iProver_top
% 27.54/3.99      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 27.54/3.99      inference(superposition,[status(thm)],[c_29996,c_29472]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_32647,plain,
% 27.54/3.99      ( ~ r1_xboole_0(X0,sK3) | r1_xboole_0(sK3,X0) ),
% 27.54/3.99      inference(instantiation,[status(thm)],[c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_32648,plain,
% 27.54/3.99      ( r1_xboole_0(X0,sK3) != iProver_top
% 27.54/3.99      | r1_xboole_0(sK3,X0) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_32647]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_32650,plain,
% 27.54/3.99      ( r1_xboole_0(sK3,sK2) = iProver_top
% 27.54/3.99      | r1_xboole_0(sK2,sK3) != iProver_top ),
% 27.54/3.99      inference(instantiation,[status(thm)],[c_32648]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1942,plain,
% 27.54/3.99      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 27.54/3.99      inference(instantiation,[status(thm)],[c_6]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_1943,plain,
% 27.54/3.99      ( r1_xboole_0(sK3,sK4) = iProver_top
% 27.54/3.99      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_1942]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(c_25,plain,
% 27.54/3.99      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 27.54/3.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.54/3.99  
% 27.54/3.99  cnf(contradiction,plain,
% 27.54/3.99      ( $false ),
% 27.54/3.99      inference(minisat,
% 27.54/3.99                [status(thm)],
% 27.54/3.99                [c_132086,c_83774,c_35491,c_32650,c_1943,c_25]) ).
% 27.54/3.99  
% 27.54/3.99  
% 27.54/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.54/3.99  
% 27.54/3.99  ------                               Statistics
% 27.54/3.99  
% 27.54/3.99  ------ Selected
% 27.54/3.99  
% 27.54/3.99  total_time:                             3.148
% 27.54/3.99  
%------------------------------------------------------------------------------
