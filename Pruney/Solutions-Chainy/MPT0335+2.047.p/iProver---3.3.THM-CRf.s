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
% DateTime   : Thu Dec  3 11:38:32 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 11.92s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 314 expanded)
%              Number of clauses        :   51 (  62 expanded)
%              Number of leaves         :   17 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  445 (1263 expanded)
%              Number of equality atoms :  198 ( 588 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK3,sK5) != k1_tarski(sK6)
      & r2_hidden(sK6,sK3)
      & k3_xboole_0(sK4,sK5) = k1_tarski(sK6)
      & r1_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k3_xboole_0(sK3,sK5) != k1_tarski(sK6)
    & r2_hidden(sK6,sK3)
    & k3_xboole_0(sK4,sK5) = k1_tarski(sK6)
    & r1_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f14,f29])).

fof(f55,plain,(
    k3_xboole_0(sK3,sK5) != k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f74,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(definition_unfolding,[],[f55,f38,f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f81,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f53,plain,(
    k3_xboole_0(sK4,sK5) = k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(definition_unfolding,[],[f53,f38,f57])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f82,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f71])).

fof(f83,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f82])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f84,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f72])).

fof(f85,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f84])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f54,plain,(
    r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_168,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1512,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
    | k2_enumset1(sK6,sK6,sK6,sK6) != X1
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_8659,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
    | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
    | k2_enumset1(sK6,sK6,sK6,sK6) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_47050,plain,
    ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
    | k2_enumset1(sK6,sK6,sK6,sK6) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_8659])).

cnf(c_5170,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK3)
    | X0 != X2
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_17876,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X1,sK3)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5170])).

cnf(c_32759,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3)
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_17876])).

cnf(c_32761,plain,
    ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3)
    | ~ r2_hidden(sK6,sK3)
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != sK6
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_32759])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_764,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,X1)))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1421,plain,
    ( ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),X0)
    | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))
    | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK4) ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_12670,plain,
    ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
    | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK4)
    | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5) ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_3510,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
    | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
    | k2_enumset1(sK6,sK6,sK6,sK6) != k2_enumset1(X1,X2,X3,X4)
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_3512,plain,
    ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6))
    | k2_enumset1(sK6,sK6,sK6,sK6) != k2_enumset1(sK6,sK6,sK6,sK6)
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != sK6 ),
    inference(instantiation,[status(thm)],[c_3510])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2339,plain,
    ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
    | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5) ),
    inference(resolution,[status(thm)],[c_2,c_17])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3029,plain,
    ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5)
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_2339,c_10])).

cnf(c_19,negated_conjecture,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1659,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6))
    | r2_hidden(X1,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_168,c_19])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1824,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
    | X0 != sK6 ),
    inference(resolution,[status(thm)],[c_1659,c_14])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1837,plain,
    ( r2_hidden(X0,sK5)
    | X0 != sK6 ),
    inference(resolution,[status(thm)],[c_1824,c_5])).

cnf(c_3414,plain,
    ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3029,c_1837])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2979,plain,
    ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
    | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3) ),
    inference(resolution,[status(thm)],[c_3,c_17])).

cnf(c_3398,plain,
    ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3)
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
    inference(resolution,[status(thm)],[c_2979,c_10])).

cnf(c_1903,plain,
    ( ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(X0,X0,X0,X0))
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1905,plain,
    ( ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
    | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_167,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_166,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1081,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_167,c_166])).

cnf(c_1355,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_1081,c_19])).

cnf(c_987,plain,
    ( sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_618,plain,
    ( ~ r1_tarski(sK3,sK4)
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_952,plain,
    ( ~ r1_tarski(sK3,sK4)
    | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK4)
    | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_867,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_700,plain,
    ( ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5)
    | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3)
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_171,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_175,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK6,sK6,sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_27,plain,
    ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_24,plain,
    ( ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47050,c_32761,c_12670,c_3512,c_3414,c_3398,c_1905,c_1355,c_987,c_952,c_867,c_700,c_175,c_27,c_24,c_17,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.92/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.92/1.99  
% 11.92/1.99  ------  iProver source info
% 11.92/1.99  
% 11.92/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.92/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.92/1.99  git: non_committed_changes: false
% 11.92/1.99  git: last_make_outside_of_git: false
% 11.92/1.99  
% 11.92/1.99  ------ 
% 11.92/1.99  
% 11.92/1.99  ------ Input Options
% 11.92/1.99  
% 11.92/1.99  --out_options                           all
% 11.92/1.99  --tptp_safe_out                         true
% 11.92/1.99  --problem_path                          ""
% 11.92/1.99  --include_path                          ""
% 11.92/1.99  --clausifier                            res/vclausify_rel
% 11.92/1.99  --clausifier_options                    --mode clausify
% 11.92/1.99  --stdin                                 false
% 11.92/1.99  --stats_out                             sel
% 11.92/1.99  
% 11.92/1.99  ------ General Options
% 11.92/1.99  
% 11.92/1.99  --fof                                   false
% 11.92/1.99  --time_out_real                         604.99
% 11.92/1.99  --time_out_virtual                      -1.
% 11.92/1.99  --symbol_type_check                     false
% 11.92/1.99  --clausify_out                          false
% 11.92/1.99  --sig_cnt_out                           false
% 11.92/1.99  --trig_cnt_out                          false
% 11.92/1.99  --trig_cnt_out_tolerance                1.
% 11.92/1.99  --trig_cnt_out_sk_spl                   false
% 11.92/1.99  --abstr_cl_out                          false
% 11.92/1.99  
% 11.92/1.99  ------ Global Options
% 11.92/1.99  
% 11.92/1.99  --schedule                              none
% 11.92/1.99  --add_important_lit                     false
% 11.92/1.99  --prop_solver_per_cl                    1000
% 11.92/1.99  --min_unsat_core                        false
% 11.92/1.99  --soft_assumptions                      false
% 11.92/1.99  --soft_lemma_size                       3
% 11.92/1.99  --prop_impl_unit_size                   0
% 11.92/1.99  --prop_impl_unit                        []
% 11.92/1.99  --share_sel_clauses                     true
% 11.92/1.99  --reset_solvers                         false
% 11.92/1.99  --bc_imp_inh                            [conj_cone]
% 11.92/1.99  --conj_cone_tolerance                   3.
% 11.92/1.99  --extra_neg_conj                        none
% 11.92/1.99  --large_theory_mode                     true
% 11.92/1.99  --prolific_symb_bound                   200
% 11.92/1.99  --lt_threshold                          2000
% 11.92/1.99  --clause_weak_htbl                      true
% 11.92/1.99  --gc_record_bc_elim                     false
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing Options
% 11.92/1.99  
% 11.92/1.99  --preprocessing_flag                    true
% 11.92/1.99  --time_out_prep_mult                    0.1
% 11.92/1.99  --splitting_mode                        input
% 11.92/1.99  --splitting_grd                         true
% 11.92/1.99  --splitting_cvd                         false
% 11.92/1.99  --splitting_cvd_svl                     false
% 11.92/1.99  --splitting_nvd                         32
% 11.92/1.99  --sub_typing                            true
% 11.92/1.99  --prep_gs_sim                           false
% 11.92/1.99  --prep_unflatten                        true
% 11.92/1.99  --prep_res_sim                          true
% 11.92/1.99  --prep_upred                            true
% 11.92/1.99  --prep_sem_filter                       exhaustive
% 11.92/1.99  --prep_sem_filter_out                   false
% 11.92/1.99  --pred_elim                             false
% 11.92/1.99  --res_sim_input                         true
% 11.92/1.99  --eq_ax_congr_red                       true
% 11.92/1.99  --pure_diseq_elim                       true
% 11.92/1.99  --brand_transform                       false
% 11.92/1.99  --non_eq_to_eq                          false
% 11.92/1.99  --prep_def_merge                        true
% 11.92/1.99  --prep_def_merge_prop_impl              false
% 11.92/1.99  --prep_def_merge_mbd                    true
% 11.92/1.99  --prep_def_merge_tr_red                 false
% 11.92/1.99  --prep_def_merge_tr_cl                  false
% 11.92/1.99  --smt_preprocessing                     true
% 11.92/1.99  --smt_ac_axioms                         fast
% 11.92/1.99  --preprocessed_out                      false
% 11.92/1.99  --preprocessed_stats                    false
% 11.92/1.99  
% 11.92/1.99  ------ Abstraction refinement Options
% 11.92/1.99  
% 11.92/1.99  --abstr_ref                             []
% 11.92/1.99  --abstr_ref_prep                        false
% 11.92/1.99  --abstr_ref_until_sat                   false
% 11.92/1.99  --abstr_ref_sig_restrict                funpre
% 11.92/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.92/1.99  --abstr_ref_under                       []
% 11.92/1.99  
% 11.92/1.99  ------ SAT Options
% 11.92/1.99  
% 11.92/1.99  --sat_mode                              false
% 11.92/1.99  --sat_fm_restart_options                ""
% 11.92/1.99  --sat_gr_def                            false
% 11.92/1.99  --sat_epr_types                         true
% 11.92/1.99  --sat_non_cyclic_types                  false
% 11.92/1.99  --sat_finite_models                     false
% 11.92/1.99  --sat_fm_lemmas                         false
% 11.92/1.99  --sat_fm_prep                           false
% 11.92/1.99  --sat_fm_uc_incr                        true
% 11.92/1.99  --sat_out_model                         small
% 11.92/1.99  --sat_out_clauses                       false
% 11.92/1.99  
% 11.92/1.99  ------ QBF Options
% 11.92/1.99  
% 11.92/1.99  --qbf_mode                              false
% 11.92/1.99  --qbf_elim_univ                         false
% 11.92/1.99  --qbf_dom_inst                          none
% 11.92/1.99  --qbf_dom_pre_inst                      false
% 11.92/1.99  --qbf_sk_in                             false
% 11.92/1.99  --qbf_pred_elim                         true
% 11.92/1.99  --qbf_split                             512
% 11.92/1.99  
% 11.92/1.99  ------ BMC1 Options
% 11.92/1.99  
% 11.92/1.99  --bmc1_incremental                      false
% 11.92/1.99  --bmc1_axioms                           reachable_all
% 11.92/1.99  --bmc1_min_bound                        0
% 11.92/1.99  --bmc1_max_bound                        -1
% 11.92/1.99  --bmc1_max_bound_default                -1
% 11.92/1.99  --bmc1_symbol_reachability              true
% 11.92/1.99  --bmc1_property_lemmas                  false
% 11.92/1.99  --bmc1_k_induction                      false
% 11.92/1.99  --bmc1_non_equiv_states                 false
% 11.92/1.99  --bmc1_deadlock                         false
% 11.92/1.99  --bmc1_ucm                              false
% 11.92/1.99  --bmc1_add_unsat_core                   none
% 11.92/1.99  --bmc1_unsat_core_children              false
% 11.92/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.92/1.99  --bmc1_out_stat                         full
% 11.92/1.99  --bmc1_ground_init                      false
% 11.92/1.99  --bmc1_pre_inst_next_state              false
% 11.92/1.99  --bmc1_pre_inst_state                   false
% 11.92/1.99  --bmc1_pre_inst_reach_state             false
% 11.92/1.99  --bmc1_out_unsat_core                   false
% 11.92/1.99  --bmc1_aig_witness_out                  false
% 11.92/1.99  --bmc1_verbose                          false
% 11.92/1.99  --bmc1_dump_clauses_tptp                false
% 11.92/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.92/1.99  --bmc1_dump_file                        -
% 11.92/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.92/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.92/1.99  --bmc1_ucm_extend_mode                  1
% 11.92/1.99  --bmc1_ucm_init_mode                    2
% 11.92/1.99  --bmc1_ucm_cone_mode                    none
% 11.92/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.92/1.99  --bmc1_ucm_relax_model                  4
% 11.92/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.92/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.92/1.99  --bmc1_ucm_layered_model                none
% 11.92/1.99  --bmc1_ucm_max_lemma_size               10
% 11.92/1.99  
% 11.92/1.99  ------ AIG Options
% 11.92/1.99  
% 11.92/1.99  --aig_mode                              false
% 11.92/1.99  
% 11.92/1.99  ------ Instantiation Options
% 11.92/1.99  
% 11.92/1.99  --instantiation_flag                    true
% 11.92/1.99  --inst_sos_flag                         false
% 11.92/1.99  --inst_sos_phase                        true
% 11.92/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.92/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.92/1.99  --inst_lit_sel_side                     num_symb
% 11.92/1.99  --inst_solver_per_active                1400
% 11.92/1.99  --inst_solver_calls_frac                1.
% 11.92/1.99  --inst_passive_queue_type               priority_queues
% 11.92/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.92/1.99  --inst_passive_queues_freq              [25;2]
% 11.92/1.99  --inst_dismatching                      true
% 11.92/1.99  --inst_eager_unprocessed_to_passive     true
% 11.92/1.99  --inst_prop_sim_given                   true
% 11.92/1.99  --inst_prop_sim_new                     false
% 11.92/1.99  --inst_subs_new                         false
% 11.92/1.99  --inst_eq_res_simp                      false
% 11.92/1.99  --inst_subs_given                       false
% 11.92/1.99  --inst_orphan_elimination               true
% 11.92/1.99  --inst_learning_loop_flag               true
% 11.92/1.99  --inst_learning_start                   3000
% 11.92/1.99  --inst_learning_factor                  2
% 11.92/1.99  --inst_start_prop_sim_after_learn       3
% 11.92/1.99  --inst_sel_renew                        solver
% 11.92/1.99  --inst_lit_activity_flag                true
% 11.92/1.99  --inst_restr_to_given                   false
% 11.92/1.99  --inst_activity_threshold               500
% 11.92/1.99  --inst_out_proof                        true
% 11.92/1.99  
% 11.92/1.99  ------ Resolution Options
% 11.92/1.99  
% 11.92/1.99  --resolution_flag                       true
% 11.92/1.99  --res_lit_sel                           adaptive
% 11.92/1.99  --res_lit_sel_side                      none
% 11.92/1.99  --res_ordering                          kbo
% 11.92/1.99  --res_to_prop_solver                    active
% 11.92/1.99  --res_prop_simpl_new                    false
% 11.92/1.99  --res_prop_simpl_given                  true
% 11.92/1.99  --res_passive_queue_type                priority_queues
% 11.92/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.92/1.99  --res_passive_queues_freq               [15;5]
% 11.92/1.99  --res_forward_subs                      full
% 11.92/1.99  --res_backward_subs                     full
% 11.92/1.99  --res_forward_subs_resolution           true
% 11.92/1.99  --res_backward_subs_resolution          true
% 11.92/1.99  --res_orphan_elimination                true
% 11.92/1.99  --res_time_limit                        2.
% 11.92/1.99  --res_out_proof                         true
% 11.92/1.99  
% 11.92/1.99  ------ Superposition Options
% 11.92/1.99  
% 11.92/1.99  --superposition_flag                    true
% 11.92/1.99  --sup_passive_queue_type                priority_queues
% 11.92/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.92/1.99  --sup_passive_queues_freq               [1;4]
% 11.92/1.99  --demod_completeness_check              fast
% 11.92/1.99  --demod_use_ground                      true
% 11.92/1.99  --sup_to_prop_solver                    passive
% 11.92/1.99  --sup_prop_simpl_new                    true
% 11.92/1.99  --sup_prop_simpl_given                  true
% 11.92/1.99  --sup_fun_splitting                     false
% 11.92/1.99  --sup_smt_interval                      50000
% 11.92/1.99  
% 11.92/1.99  ------ Superposition Simplification Setup
% 11.92/1.99  
% 11.92/1.99  --sup_indices_passive                   []
% 11.92/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.92/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_full_bw                           [BwDemod]
% 11.92/1.99  --sup_immed_triv                        [TrivRules]
% 11.92/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_immed_bw_main                     []
% 11.92/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.92/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.92/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.92/1.99  
% 11.92/1.99  ------ Combination Options
% 11.92/1.99  
% 11.92/1.99  --comb_res_mult                         3
% 11.92/1.99  --comb_sup_mult                         2
% 11.92/1.99  --comb_inst_mult                        10
% 11.92/1.99  
% 11.92/1.99  ------ Debug Options
% 11.92/1.99  
% 11.92/1.99  --dbg_backtrace                         false
% 11.92/1.99  --dbg_dump_prop_clauses                 false
% 11.92/1.99  --dbg_dump_prop_clauses_file            -
% 11.92/1.99  --dbg_out_stat                          false
% 11.92/1.99  ------ Parsing...
% 11.92/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.92/1.99  ------ Proving...
% 11.92/1.99  ------ Problem Properties 
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  clauses                                 21
% 11.92/1.99  conjectures                             4
% 11.92/1.99  EPR                                     3
% 11.92/1.99  Horn                                    16
% 11.92/1.99  unary                                   7
% 11.92/1.99  binary                                  3
% 11.92/1.99  lits                                    48
% 11.92/1.99  lits eq                                 19
% 11.92/1.99  fd_pure                                 0
% 11.92/1.99  fd_pseudo                               0
% 11.92/1.99  fd_cond                                 0
% 11.92/1.99  fd_pseudo_cond                          8
% 11.92/1.99  AC symbols                              0
% 11.92/1.99  
% 11.92/1.99  ------ Input Options Time Limit: Unbounded
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  ------ 
% 11.92/1.99  Current options:
% 11.92/1.99  ------ 
% 11.92/1.99  
% 11.92/1.99  ------ Input Options
% 11.92/1.99  
% 11.92/1.99  --out_options                           all
% 11.92/1.99  --tptp_safe_out                         true
% 11.92/1.99  --problem_path                          ""
% 11.92/1.99  --include_path                          ""
% 11.92/1.99  --clausifier                            res/vclausify_rel
% 11.92/1.99  --clausifier_options                    --mode clausify
% 11.92/1.99  --stdin                                 false
% 11.92/1.99  --stats_out                             sel
% 11.92/1.99  
% 11.92/1.99  ------ General Options
% 11.92/1.99  
% 11.92/1.99  --fof                                   false
% 11.92/1.99  --time_out_real                         604.99
% 11.92/1.99  --time_out_virtual                      -1.
% 11.92/1.99  --symbol_type_check                     false
% 11.92/1.99  --clausify_out                          false
% 11.92/1.99  --sig_cnt_out                           false
% 11.92/1.99  --trig_cnt_out                          false
% 11.92/1.99  --trig_cnt_out_tolerance                1.
% 11.92/1.99  --trig_cnt_out_sk_spl                   false
% 11.92/1.99  --abstr_cl_out                          false
% 11.92/1.99  
% 11.92/1.99  ------ Global Options
% 11.92/1.99  
% 11.92/1.99  --schedule                              none
% 11.92/1.99  --add_important_lit                     false
% 11.92/1.99  --prop_solver_per_cl                    1000
% 11.92/1.99  --min_unsat_core                        false
% 11.92/1.99  --soft_assumptions                      false
% 11.92/1.99  --soft_lemma_size                       3
% 11.92/1.99  --prop_impl_unit_size                   0
% 11.92/1.99  --prop_impl_unit                        []
% 11.92/1.99  --share_sel_clauses                     true
% 11.92/1.99  --reset_solvers                         false
% 11.92/1.99  --bc_imp_inh                            [conj_cone]
% 11.92/1.99  --conj_cone_tolerance                   3.
% 11.92/1.99  --extra_neg_conj                        none
% 11.92/1.99  --large_theory_mode                     true
% 11.92/1.99  --prolific_symb_bound                   200
% 11.92/1.99  --lt_threshold                          2000
% 11.92/1.99  --clause_weak_htbl                      true
% 11.92/1.99  --gc_record_bc_elim                     false
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing Options
% 11.92/1.99  
% 11.92/1.99  --preprocessing_flag                    true
% 11.92/1.99  --time_out_prep_mult                    0.1
% 11.92/1.99  --splitting_mode                        input
% 11.92/1.99  --splitting_grd                         true
% 11.92/1.99  --splitting_cvd                         false
% 11.92/1.99  --splitting_cvd_svl                     false
% 11.92/1.99  --splitting_nvd                         32
% 11.92/1.99  --sub_typing                            true
% 11.92/1.99  --prep_gs_sim                           false
% 11.92/1.99  --prep_unflatten                        true
% 11.92/1.99  --prep_res_sim                          true
% 11.92/1.99  --prep_upred                            true
% 11.92/1.99  --prep_sem_filter                       exhaustive
% 11.92/1.99  --prep_sem_filter_out                   false
% 11.92/1.99  --pred_elim                             false
% 11.92/1.99  --res_sim_input                         true
% 11.92/1.99  --eq_ax_congr_red                       true
% 11.92/1.99  --pure_diseq_elim                       true
% 11.92/1.99  --brand_transform                       false
% 11.92/1.99  --non_eq_to_eq                          false
% 11.92/1.99  --prep_def_merge                        true
% 11.92/1.99  --prep_def_merge_prop_impl              false
% 11.92/1.99  --prep_def_merge_mbd                    true
% 11.92/1.99  --prep_def_merge_tr_red                 false
% 11.92/1.99  --prep_def_merge_tr_cl                  false
% 11.92/1.99  --smt_preprocessing                     true
% 11.92/1.99  --smt_ac_axioms                         fast
% 11.92/1.99  --preprocessed_out                      false
% 11.92/1.99  --preprocessed_stats                    false
% 11.92/1.99  
% 11.92/1.99  ------ Abstraction refinement Options
% 11.92/1.99  
% 11.92/1.99  --abstr_ref                             []
% 11.92/1.99  --abstr_ref_prep                        false
% 11.92/1.99  --abstr_ref_until_sat                   false
% 11.92/1.99  --abstr_ref_sig_restrict                funpre
% 11.92/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.92/1.99  --abstr_ref_under                       []
% 11.92/1.99  
% 11.92/1.99  ------ SAT Options
% 11.92/1.99  
% 11.92/1.99  --sat_mode                              false
% 11.92/1.99  --sat_fm_restart_options                ""
% 11.92/1.99  --sat_gr_def                            false
% 11.92/1.99  --sat_epr_types                         true
% 11.92/1.99  --sat_non_cyclic_types                  false
% 11.92/1.99  --sat_finite_models                     false
% 11.92/1.99  --sat_fm_lemmas                         false
% 11.92/1.99  --sat_fm_prep                           false
% 11.92/1.99  --sat_fm_uc_incr                        true
% 11.92/1.99  --sat_out_model                         small
% 11.92/1.99  --sat_out_clauses                       false
% 11.92/1.99  
% 11.92/1.99  ------ QBF Options
% 11.92/1.99  
% 11.92/1.99  --qbf_mode                              false
% 11.92/1.99  --qbf_elim_univ                         false
% 11.92/1.99  --qbf_dom_inst                          none
% 11.92/1.99  --qbf_dom_pre_inst                      false
% 11.92/1.99  --qbf_sk_in                             false
% 11.92/1.99  --qbf_pred_elim                         true
% 11.92/1.99  --qbf_split                             512
% 11.92/1.99  
% 11.92/1.99  ------ BMC1 Options
% 11.92/1.99  
% 11.92/1.99  --bmc1_incremental                      false
% 11.92/1.99  --bmc1_axioms                           reachable_all
% 11.92/1.99  --bmc1_min_bound                        0
% 11.92/1.99  --bmc1_max_bound                        -1
% 11.92/1.99  --bmc1_max_bound_default                -1
% 11.92/1.99  --bmc1_symbol_reachability              true
% 11.92/1.99  --bmc1_property_lemmas                  false
% 11.92/1.99  --bmc1_k_induction                      false
% 11.92/1.99  --bmc1_non_equiv_states                 false
% 11.92/1.99  --bmc1_deadlock                         false
% 11.92/1.99  --bmc1_ucm                              false
% 11.92/1.99  --bmc1_add_unsat_core                   none
% 11.92/1.99  --bmc1_unsat_core_children              false
% 11.92/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.92/1.99  --bmc1_out_stat                         full
% 11.92/1.99  --bmc1_ground_init                      false
% 11.92/1.99  --bmc1_pre_inst_next_state              false
% 11.92/1.99  --bmc1_pre_inst_state                   false
% 11.92/1.99  --bmc1_pre_inst_reach_state             false
% 11.92/1.99  --bmc1_out_unsat_core                   false
% 11.92/1.99  --bmc1_aig_witness_out                  false
% 11.92/1.99  --bmc1_verbose                          false
% 11.92/1.99  --bmc1_dump_clauses_tptp                false
% 11.92/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.92/1.99  --bmc1_dump_file                        -
% 11.92/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.92/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.92/1.99  --bmc1_ucm_extend_mode                  1
% 11.92/1.99  --bmc1_ucm_init_mode                    2
% 11.92/1.99  --bmc1_ucm_cone_mode                    none
% 11.92/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.92/1.99  --bmc1_ucm_relax_model                  4
% 11.92/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.92/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.92/1.99  --bmc1_ucm_layered_model                none
% 11.92/1.99  --bmc1_ucm_max_lemma_size               10
% 11.92/1.99  
% 11.92/1.99  ------ AIG Options
% 11.92/1.99  
% 11.92/1.99  --aig_mode                              false
% 11.92/1.99  
% 11.92/1.99  ------ Instantiation Options
% 11.92/1.99  
% 11.92/1.99  --instantiation_flag                    true
% 11.92/1.99  --inst_sos_flag                         false
% 11.92/1.99  --inst_sos_phase                        true
% 11.92/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.92/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.92/1.99  --inst_lit_sel_side                     num_symb
% 11.92/1.99  --inst_solver_per_active                1400
% 11.92/1.99  --inst_solver_calls_frac                1.
% 11.92/1.99  --inst_passive_queue_type               priority_queues
% 11.92/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.92/1.99  --inst_passive_queues_freq              [25;2]
% 11.92/1.99  --inst_dismatching                      true
% 11.92/1.99  --inst_eager_unprocessed_to_passive     true
% 11.92/1.99  --inst_prop_sim_given                   true
% 11.92/1.99  --inst_prop_sim_new                     false
% 11.92/1.99  --inst_subs_new                         false
% 11.92/1.99  --inst_eq_res_simp                      false
% 11.92/1.99  --inst_subs_given                       false
% 11.92/1.99  --inst_orphan_elimination               true
% 11.92/1.99  --inst_learning_loop_flag               true
% 11.92/1.99  --inst_learning_start                   3000
% 11.92/1.99  --inst_learning_factor                  2
% 11.92/1.99  --inst_start_prop_sim_after_learn       3
% 11.92/1.99  --inst_sel_renew                        solver
% 11.92/1.99  --inst_lit_activity_flag                true
% 11.92/1.99  --inst_restr_to_given                   false
% 11.92/1.99  --inst_activity_threshold               500
% 11.92/1.99  --inst_out_proof                        true
% 11.92/1.99  
% 11.92/1.99  ------ Resolution Options
% 11.92/1.99  
% 11.92/1.99  --resolution_flag                       true
% 11.92/1.99  --res_lit_sel                           adaptive
% 11.92/1.99  --res_lit_sel_side                      none
% 11.92/1.99  --res_ordering                          kbo
% 11.92/1.99  --res_to_prop_solver                    active
% 11.92/1.99  --res_prop_simpl_new                    false
% 11.92/1.99  --res_prop_simpl_given                  true
% 11.92/1.99  --res_passive_queue_type                priority_queues
% 11.92/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.92/1.99  --res_passive_queues_freq               [15;5]
% 11.92/1.99  --res_forward_subs                      full
% 11.92/1.99  --res_backward_subs                     full
% 11.92/1.99  --res_forward_subs_resolution           true
% 11.92/1.99  --res_backward_subs_resolution          true
% 11.92/1.99  --res_orphan_elimination                true
% 11.92/1.99  --res_time_limit                        2.
% 11.92/1.99  --res_out_proof                         true
% 11.92/1.99  
% 11.92/1.99  ------ Superposition Options
% 11.92/1.99  
% 11.92/1.99  --superposition_flag                    true
% 11.92/1.99  --sup_passive_queue_type                priority_queues
% 11.92/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.92/1.99  --sup_passive_queues_freq               [1;4]
% 11.92/1.99  --demod_completeness_check              fast
% 11.92/1.99  --demod_use_ground                      true
% 11.92/1.99  --sup_to_prop_solver                    passive
% 11.92/1.99  --sup_prop_simpl_new                    true
% 11.92/1.99  --sup_prop_simpl_given                  true
% 11.92/1.99  --sup_fun_splitting                     false
% 11.92/1.99  --sup_smt_interval                      50000
% 11.92/1.99  
% 11.92/1.99  ------ Superposition Simplification Setup
% 11.92/1.99  
% 11.92/1.99  --sup_indices_passive                   []
% 11.92/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.92/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.92/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_full_bw                           [BwDemod]
% 11.92/1.99  --sup_immed_triv                        [TrivRules]
% 11.92/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_immed_bw_main                     []
% 11.92/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.92/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.92/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.92/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.92/1.99  
% 11.92/1.99  ------ Combination Options
% 11.92/1.99  
% 11.92/1.99  --comb_res_mult                         3
% 11.92/1.99  --comb_sup_mult                         2
% 11.92/1.99  --comb_inst_mult                        10
% 11.92/1.99  
% 11.92/1.99  ------ Debug Options
% 11.92/1.99  
% 11.92/1.99  --dbg_backtrace                         false
% 11.92/1.99  --dbg_dump_prop_clauses                 false
% 11.92/1.99  --dbg_dump_prop_clauses_file            -
% 11.92/1.99  --dbg_out_stat                          false
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  ------ Proving...
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  % SZS status Theorem for theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  fof(f2,axiom,(
% 11.92/1.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.92/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f15,plain,(
% 11.92/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.92/1.99    inference(nnf_transformation,[],[f2])).
% 11.92/1.99  
% 11.92/1.99  fof(f16,plain,(
% 11.92/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.92/1.99    inference(flattening,[],[f15])).
% 11.92/1.99  
% 11.92/1.99  fof(f17,plain,(
% 11.92/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.92/1.99    inference(rectify,[],[f16])).
% 11.92/1.99  
% 11.92/1.99  fof(f18,plain,(
% 11.92/1.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f19,plain,(
% 11.92/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.92/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 11.92/1.99  
% 11.92/1.99  fof(f34,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 11.92/1.99    inference(cnf_transformation,[],[f19])).
% 11.92/1.99  
% 11.92/1.99  fof(f3,axiom,(
% 11.92/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.92/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f38,plain,(
% 11.92/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.92/1.99    inference(cnf_transformation,[],[f3])).
% 11.92/1.99  
% 11.92/1.99  fof(f61,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 11.92/1.99    inference(definition_unfolding,[],[f34,f38])).
% 11.92/1.99  
% 11.92/1.99  fof(f76,plain,(
% 11.92/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 11.92/1.99    inference(equality_resolution,[],[f61])).
% 11.92/1.99  
% 11.92/1.99  fof(f36,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f19])).
% 11.92/1.99  
% 11.92/1.99  fof(f59,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.92/1.99    inference(definition_unfolding,[],[f36,f38])).
% 11.92/1.99  
% 11.92/1.99  fof(f9,conjecture,(
% 11.92/1.99    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 11.92/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f10,negated_conjecture,(
% 11.92/1.99    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 11.92/1.99    inference(negated_conjecture,[],[f9])).
% 11.92/1.99  
% 11.92/1.99  fof(f13,plain,(
% 11.92/1.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 11.92/1.99    inference(ennf_transformation,[],[f10])).
% 11.92/1.99  
% 11.92/1.99  fof(f14,plain,(
% 11.92/1.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 11.92/1.99    inference(flattening,[],[f13])).
% 11.92/1.99  
% 11.92/1.99  fof(f29,plain,(
% 11.92/1.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK3,sK5) != k1_tarski(sK6) & r2_hidden(sK6,sK3) & k3_xboole_0(sK4,sK5) = k1_tarski(sK6) & r1_tarski(sK3,sK4))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f30,plain,(
% 11.92/1.99    k3_xboole_0(sK3,sK5) != k1_tarski(sK6) & r2_hidden(sK6,sK3) & k3_xboole_0(sK4,sK5) = k1_tarski(sK6) & r1_tarski(sK3,sK4)),
% 11.92/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f14,f29])).
% 11.92/1.99  
% 11.92/1.99  fof(f55,plain,(
% 11.92/1.99    k3_xboole_0(sK3,sK5) != k1_tarski(sK6)),
% 11.92/1.99    inference(cnf_transformation,[],[f30])).
% 11.92/1.99  
% 11.92/1.99  fof(f6,axiom,(
% 11.92/1.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.92/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f49,plain,(
% 11.92/1.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f6])).
% 11.92/1.99  
% 11.92/1.99  fof(f7,axiom,(
% 11.92/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.92/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f50,plain,(
% 11.92/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f7])).
% 11.92/1.99  
% 11.92/1.99  fof(f8,axiom,(
% 11.92/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.92/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f51,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f8])).
% 11.92/1.99  
% 11.92/1.99  fof(f56,plain,(
% 11.92/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.92/1.99    inference(definition_unfolding,[],[f50,f51])).
% 11.92/1.99  
% 11.92/1.99  fof(f57,plain,(
% 11.92/1.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.92/1.99    inference(definition_unfolding,[],[f49,f56])).
% 11.92/1.99  
% 11.92/1.99  fof(f74,plain,(
% 11.92/1.99    k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6)),
% 11.92/1.99    inference(definition_unfolding,[],[f55,f38,f57])).
% 11.92/1.99  
% 11.92/1.99  fof(f4,axiom,(
% 11.92/1.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.92/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f20,plain,(
% 11.92/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.92/1.99    inference(nnf_transformation,[],[f4])).
% 11.92/1.99  
% 11.92/1.99  fof(f21,plain,(
% 11.92/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.92/1.99    inference(rectify,[],[f20])).
% 11.92/1.99  
% 11.92/1.99  fof(f22,plain,(
% 11.92/1.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f23,plain,(
% 11.92/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.92/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 11.92/1.99  
% 11.92/1.99  fof(f39,plain,(
% 11.92/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.92/1.99    inference(cnf_transformation,[],[f23])).
% 11.92/1.99  
% 11.92/1.99  fof(f67,plain,(
% 11.92/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.92/1.99    inference(definition_unfolding,[],[f39,f57])).
% 11.92/1.99  
% 11.92/1.99  fof(f81,plain,(
% 11.92/1.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 11.92/1.99    inference(equality_resolution,[],[f67])).
% 11.92/1.99  
% 11.92/1.99  fof(f53,plain,(
% 11.92/1.99    k3_xboole_0(sK4,sK5) = k1_tarski(sK6)),
% 11.92/1.99    inference(cnf_transformation,[],[f30])).
% 11.92/1.99  
% 11.92/1.99  fof(f75,plain,(
% 11.92/1.99    k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6)),
% 11.92/1.99    inference(definition_unfolding,[],[f53,f38,f57])).
% 11.92/1.99  
% 11.92/1.99  fof(f5,axiom,(
% 11.92/1.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 11.92/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f24,plain,(
% 11.92/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.92/1.99    inference(nnf_transformation,[],[f5])).
% 11.92/1.99  
% 11.92/1.99  fof(f25,plain,(
% 11.92/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.92/1.99    inference(flattening,[],[f24])).
% 11.92/1.99  
% 11.92/1.99  fof(f26,plain,(
% 11.92/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.92/1.99    inference(rectify,[],[f25])).
% 11.92/1.99  
% 11.92/1.99  fof(f27,plain,(
% 11.92/1.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f28,plain,(
% 11.92/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.92/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 11.92/1.99  
% 11.92/1.99  fof(f45,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 11.92/1.99    inference(cnf_transformation,[],[f28])).
% 11.92/1.99  
% 11.92/1.99  fof(f71,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 11.92/1.99    inference(definition_unfolding,[],[f45,f56])).
% 11.92/1.99  
% 11.92/1.99  fof(f82,plain,(
% 11.92/1.99    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 11.92/1.99    inference(equality_resolution,[],[f71])).
% 11.92/1.99  
% 11.92/1.99  fof(f83,plain,(
% 11.92/1.99    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 11.92/1.99    inference(equality_resolution,[],[f82])).
% 11.92/1.99  
% 11.92/1.99  fof(f33,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.92/1.99    inference(cnf_transformation,[],[f19])).
% 11.92/1.99  
% 11.92/1.99  fof(f62,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 11.92/1.99    inference(definition_unfolding,[],[f33,f38])).
% 11.92/1.99  
% 11.92/1.99  fof(f77,plain,(
% 11.92/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.92/1.99    inference(equality_resolution,[],[f62])).
% 11.92/1.99  
% 11.92/1.99  fof(f35,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f19])).
% 11.92/1.99  
% 11.92/1.99  fof(f60,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.92/1.99    inference(definition_unfolding,[],[f35,f38])).
% 11.92/1.99  
% 11.92/1.99  fof(f1,axiom,(
% 11.92/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.92/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f11,plain,(
% 11.92/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.92/1.99    inference(unused_predicate_definition_removal,[],[f1])).
% 11.92/1.99  
% 11.92/1.99  fof(f12,plain,(
% 11.92/1.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 11.92/1.99    inference(ennf_transformation,[],[f11])).
% 11.92/1.99  
% 11.92/1.99  fof(f31,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f12])).
% 11.92/1.99  
% 11.92/1.99  fof(f37,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f19])).
% 11.92/1.99  
% 11.92/1.99  fof(f58,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.92/1.99    inference(definition_unfolding,[],[f37,f38])).
% 11.92/1.99  
% 11.92/1.99  fof(f44,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 11.92/1.99    inference(cnf_transformation,[],[f28])).
% 11.92/1.99  
% 11.92/1.99  fof(f72,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 11.92/1.99    inference(definition_unfolding,[],[f44,f56])).
% 11.92/1.99  
% 11.92/1.99  fof(f84,plain,(
% 11.92/1.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 11.92/1.99    inference(equality_resolution,[],[f72])).
% 11.92/1.99  
% 11.92/1.99  fof(f85,plain,(
% 11.92/1.99    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 11.92/1.99    inference(equality_resolution,[],[f84])).
% 11.92/1.99  
% 11.92/1.99  fof(f43,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 11.92/1.99    inference(cnf_transformation,[],[f28])).
% 11.92/1.99  
% 11.92/1.99  fof(f73,plain,(
% 11.92/1.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 11.92/1.99    inference(definition_unfolding,[],[f43,f56])).
% 11.92/1.99  
% 11.92/1.99  fof(f86,plain,(
% 11.92/1.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 11.92/1.99    inference(equality_resolution,[],[f73])).
% 11.92/1.99  
% 11.92/1.99  fof(f54,plain,(
% 11.92/1.99    r2_hidden(sK6,sK3)),
% 11.92/1.99    inference(cnf_transformation,[],[f30])).
% 11.92/1.99  
% 11.92/1.99  fof(f52,plain,(
% 11.92/1.99    r1_tarski(sK3,sK4)),
% 11.92/1.99    inference(cnf_transformation,[],[f30])).
% 11.92/1.99  
% 11.92/1.99  cnf(c_168,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.92/1.99      theory(equality) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1512,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,X1)
% 11.92/1.99      | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | k2_enumset1(sK6,sK6,sK6,sK6) != X1
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != X0 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_168]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_8659,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
% 11.92/1.99      | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | k2_enumset1(sK6,sK6,sK6,sK6) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != X0 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1512]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_47050,plain,
% 11.92/1.99      ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
% 11.92/1.99      | k2_enumset1(sK6,sK6,sK6,sK6) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_8659]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_5170,plain,
% 11.92/1.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X2,sK3) | X0 != X2 | X1 != sK3 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_168]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_17876,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,sK3) | r2_hidden(X1,sK3) | X1 != X0 | sK3 != sK3 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_5170]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_32759,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,sK3)
% 11.92/1.99      | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3)
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != X0
% 11.92/1.99      | sK3 != sK3 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_17876]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_32761,plain,
% 11.92/1.99      ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3)
% 11.92/1.99      | ~ r2_hidden(sK6,sK3)
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != sK6
% 11.92/1.99      | sK3 != sK3 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_32759]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_4,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,X1)
% 11.92/1.99      | ~ r2_hidden(X0,X2)
% 11.92/1.99      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 11.92/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_764,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,X1)
% 11.92/1.99      | r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,X1)))
% 11.92/1.99      | ~ r2_hidden(X0,sK4) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1421,plain,
% 11.92/1.99      ( ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),X0)
% 11.92/1.99      | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k4_xboole_0(sK4,k4_xboole_0(sK4,X0)))
% 11.92/1.99      | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK4) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_764]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_12670,plain,
% 11.92/1.99      ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
% 11.92/1.99      | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK4)
% 11.92/1.99      | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1421]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3510,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
% 11.92/1.99      | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | k2_enumset1(sK6,sK6,sK6,sK6) != k2_enumset1(X1,X2,X3,X4)
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != X0 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1512]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3512,plain,
% 11.92/1.99      ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | k2_enumset1(sK6,sK6,sK6,sK6) != k2_enumset1(sK6,sK6,sK6,sK6)
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != sK6 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_3510]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_2,plain,
% 11.92/1.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 11.92/1.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.92/1.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 11.92/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_17,negated_conjecture,
% 11.92/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) != k2_enumset1(sK6,sK6,sK6,sK6) ),
% 11.92/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_2339,plain,
% 11.92/1.99      ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5) ),
% 11.92/1.99      inference(resolution,[status(thm)],[c_2,c_17]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_10,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 11.92/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3029,plain,
% 11.92/1.99      ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5)
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
% 11.92/1.99      inference(resolution,[status(thm)],[c_2339,c_10]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_19,negated_conjecture,
% 11.92/1.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
% 11.92/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1659,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | r2_hidden(X1,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))
% 11.92/1.99      | X1 != X0 ),
% 11.92/1.99      inference(resolution,[status(thm)],[c_168,c_19]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_14,plain,
% 11.92/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1824,plain,
% 11.92/1.99      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) | X0 != sK6 ),
% 11.92/1.99      inference(resolution,[status(thm)],[c_1659,c_14]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_5,plain,
% 11.92/1.99      ( r2_hidden(X0,X1)
% 11.92/1.99      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 11.92/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1837,plain,
% 11.92/1.99      ( r2_hidden(X0,sK5) | X0 != sK6 ),
% 11.92/1.99      inference(resolution,[status(thm)],[c_1824,c_5]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3414,plain,
% 11.92/1.99      ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5) ),
% 11.92/1.99      inference(forward_subsumption_resolution,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_3029,c_1837]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3,plain,
% 11.92/1.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 11.92/1.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.92/1.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 11.92/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_2979,plain,
% 11.92/1.99      ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3) ),
% 11.92/1.99      inference(resolution,[status(thm)],[c_3,c_17]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3398,plain,
% 11.92/1.99      ( r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3)
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
% 11.92/1.99      inference(resolution,[status(thm)],[c_2979,c_10]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1903,plain,
% 11.92/1.99      ( ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(X0,X0,X0,X0))
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = X0 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1905,plain,
% 11.92/1.99      ( ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = sK6 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1903]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_167,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_166,plain,( X0 = X0 ),theory(equality) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1081,plain,
% 11.92/1.99      ( X0 != X1 | X1 = X0 ),
% 11.92/1.99      inference(resolution,[status(thm)],[c_167,c_166]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1355,plain,
% 11.92/1.99      ( k2_enumset1(sK6,sK6,sK6,sK6) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) ),
% 11.92/1.99      inference(resolution,[status(thm)],[c_1081,c_19]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_987,plain,
% 11.92/1.99      ( sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) = sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_166]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_0,plain,
% 11.92/1.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 11.92/1.99      inference(cnf_transformation,[],[f31]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_618,plain,
% 11.92/1.99      ( ~ r1_tarski(sK3,sK4) | r2_hidden(X0,sK4) | ~ r2_hidden(X0,sK3) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_952,plain,
% 11.92/1.99      ( ~ r1_tarski(sK3,sK4)
% 11.92/1.99      | r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK4)
% 11.92/1.99      | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_618]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_867,plain,
% 11.92/1.99      ( sK3 = sK3 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_166]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1,plain,
% 11.92/1.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 11.92/1.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 11.92/1.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 11.92/1.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 11.92/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_700,plain,
% 11.92/1.99      ( ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(sK6,sK6,sK6,sK6))
% 11.92/1.99      | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK5)
% 11.92/1.99      | ~ r2_hidden(sK0(sK3,sK5,k2_enumset1(sK6,sK6,sK6,sK6)),sK3)
% 11.92/1.99      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k2_enumset1(sK6,sK6,sK6,sK6) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_171,plain,
% 11.92/1.99      ( X0 != X1
% 11.92/1.99      | X2 != X3
% 11.92/1.99      | X4 != X5
% 11.92/1.99      | X6 != X7
% 11.92/1.99      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 11.92/1.99      theory(equality) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_175,plain,
% 11.92/1.99      ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK6,sK6,sK6,sK6)
% 11.92/1.99      | sK6 != sK6 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_171]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_15,plain,
% 11.92/1.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_27,plain,
% 11.92/1.99      ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_16,plain,
% 11.92/1.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 11.92/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_24,plain,
% 11.92/1.99      ( ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) | sK6 = sK6 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_16]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_18,negated_conjecture,
% 11.92/1.99      ( r2_hidden(sK6,sK3) ),
% 11.92/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_20,negated_conjecture,
% 11.92/1.99      ( r1_tarski(sK3,sK4) ),
% 11.92/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(contradiction,plain,
% 11.92/1.99      ( $false ),
% 11.92/1.99      inference(minisat,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_47050,c_32761,c_12670,c_3512,c_3414,c_3398,c_1905,
% 11.92/1.99                 c_1355,c_987,c_952,c_867,c_700,c_175,c_27,c_24,c_17,
% 11.92/1.99                 c_18,c_20]) ).
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  ------                               Statistics
% 11.92/1.99  
% 11.92/1.99  ------ Selected
% 11.92/1.99  
% 11.92/1.99  total_time:                             1.367
% 11.92/1.99  
%------------------------------------------------------------------------------
