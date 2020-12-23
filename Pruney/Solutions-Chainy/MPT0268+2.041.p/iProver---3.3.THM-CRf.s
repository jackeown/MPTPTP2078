%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:38 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 482 expanded)
%              Number of clauses        :   32 (  93 expanded)
%              Number of leaves         :   13 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  328 (2893 expanded)
%              Number of equality atoms :  168 (1113 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK4,sK3)
        | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3 )
      & ( ~ r2_hidden(sK4,sK3)
        | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3 ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( r2_hidden(sK4,sK3)
      | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3 )
    & ( ~ r2_hidden(sK4,sK3)
      | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f46])).

fof(f88,plain,
    ( r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f84,f85])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f83,f89])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f82,f90])).

fof(f109,plain,
    ( r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK3 ),
    inference(definition_unfolding,[],[f88,f91])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,
    ( ~ r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f110,plain,
    ( ~ r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(definition_unfolding,[],[f87,f91])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f74,f89])).

fof(f125,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f107])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f75,f89])).

fof(f123,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f106])).

fof(f124,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f123])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3086,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | r2_hidden(sK4,sK3) ),
    inference(resolution,[status(thm)],[c_9,c_34])).

cnf(c_6312,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_7,c_3086])).

cnf(c_1785,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1793,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6879,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6312,c_1785,c_1793])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6895,plain,
    ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_6879,c_8])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(sK4,sK3)
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_42,plain,
    ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_31,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_45,plain,
    ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_751,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2119,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_755,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1755,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4,sK3)
    | sK3 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_2118,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK4,sK3)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_5300,plain,
    ( ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
    | r2_hidden(sK4,sK3)
    | sK3 != sK3
    | sK4 != sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_752,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5670,plain,
    ( X0 != X1
    | X0 = sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3)
    | sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_5671,plain,
    ( sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) != sK4
    | sK4 = sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_5670])).

cnf(c_6897,plain,
    ( sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) = sK4
    | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(resolution,[status(thm)],[c_6879,c_32])).

cnf(c_7055,plain,
    ( k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6895,c_35,c_42,c_45,c_1785,c_2119,c_5300,c_5671,c_6897])).

cnf(c_7070,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
    | ~ r2_hidden(X1,sK3)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_7055,c_755])).

cnf(c_8027,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_7070,c_751])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_8383,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_8027,c_11])).

cnf(c_8385,plain,
    ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_8383])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8385,c_7055,c_45,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:14:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.68/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.98  
% 3.68/0.98  ------  iProver source info
% 3.68/0.98  
% 3.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.98  git: non_committed_changes: false
% 3.68/0.98  git: last_make_outside_of_git: false
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  ------ Parsing...
% 3.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  ------ Proving...
% 3.68/0.98  ------ Problem Properties 
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  clauses                                 35
% 3.68/0.98  conjectures                             2
% 3.68/0.98  EPR                                     2
% 3.68/0.98  Horn                                    23
% 3.68/0.98  unary                                   6
% 3.68/0.98  binary                                  11
% 3.68/0.98  lits                                    87
% 3.68/0.98  lits eq                                 28
% 3.68/0.98  fd_pure                                 0
% 3.68/0.98  fd_pseudo                               0
% 3.68/0.98  fd_cond                                 0
% 3.68/0.98  fd_pseudo_cond                          11
% 3.68/0.98  AC symbols                              0
% 3.68/0.98  
% 3.68/0.98  ------ Input Options Time Limit: Unbounded
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  Current options:
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS status Theorem for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  fof(f2,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f31,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.68/0.98    inference(nnf_transformation,[],[f2])).
% 3.68/0.98  
% 3.68/0.98  fof(f32,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.68/0.98    inference(flattening,[],[f31])).
% 3.68/0.98  
% 3.68/0.98  fof(f33,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.68/0.98    inference(rectify,[],[f32])).
% 3.68/0.98  
% 3.68/0.98  fof(f34,plain,(
% 3.68/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f35,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.68/0.98  
% 3.68/0.98  fof(f59,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f35])).
% 3.68/0.98  
% 3.68/0.98  fof(f57,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f35])).
% 3.68/0.98  
% 3.68/0.98  fof(f17,conjecture,(
% 3.68/0.98    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f18,negated_conjecture,(
% 3.68/0.98    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.68/0.98    inference(negated_conjecture,[],[f17])).
% 3.68/0.98  
% 3.68/0.98  fof(f25,plain,(
% 3.68/0.98    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f18])).
% 3.68/0.98  
% 3.68/0.98  fof(f45,plain,(
% 3.68/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.68/0.98    inference(nnf_transformation,[],[f25])).
% 3.68/0.98  
% 3.68/0.98  fof(f46,plain,(
% 3.68/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3) & (~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f47,plain,(
% 3.68/0.98    (r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3) & (~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3)),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f46])).
% 3.68/0.98  
% 3.68/0.98  fof(f88,plain,(
% 3.68/0.98    r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) != sK3),
% 3.68/0.98    inference(cnf_transformation,[],[f47])).
% 3.68/0.98  
% 3.68/0.98  fof(f12,axiom,(
% 3.68/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f82,plain,(
% 3.68/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f12])).
% 3.68/0.98  
% 3.68/0.98  fof(f13,axiom,(
% 3.68/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f83,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f13])).
% 3.68/0.98  
% 3.68/0.98  fof(f14,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f84,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f14])).
% 3.68/0.98  
% 3.68/0.98  fof(f15,axiom,(
% 3.68/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f85,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f15])).
% 3.68/0.98  
% 3.68/0.98  fof(f89,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.68/0.98    inference(definition_unfolding,[],[f84,f85])).
% 3.68/0.98  
% 3.68/0.98  fof(f90,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.68/0.98    inference(definition_unfolding,[],[f83,f89])).
% 3.68/0.98  
% 3.68/0.98  fof(f91,plain,(
% 3.68/0.98    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.68/0.98    inference(definition_unfolding,[],[f82,f90])).
% 3.68/0.98  
% 3.68/0.98  fof(f109,plain,(
% 3.68/0.98    r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK3),
% 3.68/0.98    inference(definition_unfolding,[],[f88,f91])).
% 3.68/0.98  
% 3.68/0.98  fof(f58,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f35])).
% 3.68/0.98  
% 3.68/0.98  fof(f87,plain,(
% 3.68/0.98    ~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k1_tarski(sK4)) = sK3),
% 3.68/0.98    inference(cnf_transformation,[],[f47])).
% 3.68/0.98  
% 3.68/0.98  fof(f110,plain,(
% 3.68/0.98    ~r2_hidden(sK4,sK3) | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3),
% 3.68/0.98    inference(definition_unfolding,[],[f87,f91])).
% 3.68/0.98  
% 3.68/0.98  fof(f11,axiom,(
% 3.68/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f23,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.68/0.98    inference(ennf_transformation,[],[f11])).
% 3.68/0.98  
% 3.68/0.98  fof(f40,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.68/0.98    inference(nnf_transformation,[],[f23])).
% 3.68/0.98  
% 3.68/0.98  fof(f41,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.68/0.98    inference(flattening,[],[f40])).
% 3.68/0.98  
% 3.68/0.98  fof(f42,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.68/0.98    inference(rectify,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f43,plain,(
% 3.68/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f44,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 3.68/0.98  
% 3.68/0.98  fof(f74,plain,(
% 3.68/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.68/0.98    inference(cnf_transformation,[],[f44])).
% 3.68/0.98  
% 3.68/0.98  fof(f107,plain,(
% 3.68/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.68/0.98    inference(definition_unfolding,[],[f74,f89])).
% 3.68/0.98  
% 3.68/0.98  fof(f125,plain,(
% 3.68/0.98    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 3.68/0.98    inference(equality_resolution,[],[f107])).
% 3.68/0.98  
% 3.68/0.98  fof(f75,plain,(
% 3.68/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.68/0.98    inference(cnf_transformation,[],[f44])).
% 3.68/0.98  
% 3.68/0.98  fof(f106,plain,(
% 3.68/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.68/0.98    inference(definition_unfolding,[],[f75,f89])).
% 3.68/0.98  
% 3.68/0.98  fof(f123,plain,(
% 3.68/0.98    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 3.68/0.98    inference(equality_resolution,[],[f106])).
% 3.68/0.98  
% 3.68/0.98  fof(f124,plain,(
% 3.68/0.98    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 3.68/0.98    inference(equality_resolution,[],[f123])).
% 3.68/0.98  
% 3.68/0.98  fof(f55,plain,(
% 3.68/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.68/0.98    inference(cnf_transformation,[],[f35])).
% 3.68/0.98  
% 3.68/0.98  fof(f115,plain,(
% 3.68/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.68/0.98    inference(equality_resolution,[],[f55])).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7,plain,
% 3.68/0.98      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 3.68/0.98      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.68/0.98      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.68/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.68/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9,plain,
% 3.68/0.98      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.68/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.68/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.68/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_34,negated_conjecture,
% 3.68/0.98      ( r2_hidden(sK4,sK3)
% 3.68/0.98      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK3 ),
% 3.68/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3086,plain,
% 3.68/0.98      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.68/0.98      | r2_hidden(sK4,sK3) ),
% 3.68/0.98      inference(resolution,[status(thm)],[c_9,c_34]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6312,plain,
% 3.68/0.98      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.68/0.98      | ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.68/0.98      | r2_hidden(sK4,sK3)
% 3.68/0.98      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.68/0.98      inference(resolution,[status(thm)],[c_7,c_3086]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1785,plain,
% 3.68/0.98      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.68/0.98      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1793,plain,
% 3.68/0.98      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.68/0.98      | ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.68/0.98      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6879,plain,
% 3.68/0.98      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.68/0.98      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_6312,c_1785,c_1793]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8,plain,
% 3.68/0.98      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 3.68/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.68/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.68/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6895,plain,
% 3.68/0.98      ( r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.68/0.98      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.68/0.98      inference(resolution,[status(thm)],[c_6879,c_8]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_35,negated_conjecture,
% 3.68/0.98      ( ~ r2_hidden(sK4,sK3)
% 3.68/0.98      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.68/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_32,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 3.68/0.98      | X0 = X1
% 3.68/0.98      | X0 = X2
% 3.68/0.98      | X0 = X3 ),
% 3.68/0.98      inference(cnf_transformation,[],[f125]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_42,plain,
% 3.68/0.98      ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_32]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_31,plain,
% 3.68/0.98      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f124]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_45,plain,
% 3.68/0.98      ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_31]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_751,plain,( X0 = X0 ),theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2119,plain,
% 3.68/0.98      ( sK3 = sK3 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_751]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_755,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.68/0.98      theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1755,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(sK4,sK3) | sK3 != X1 | sK4 != X0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_755]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2118,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,sK3)
% 3.68/0.98      | r2_hidden(sK4,sK3)
% 3.68/0.98      | sK3 != sK3
% 3.68/0.98      | sK4 != X0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1755]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5300,plain,
% 3.68/0.98      ( ~ r2_hidden(sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3),sK3)
% 3.68/0.98      | r2_hidden(sK4,sK3)
% 3.68/0.98      | sK3 != sK3
% 3.68/0.98      | sK4 != sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_2118]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_752,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5670,plain,
% 3.68/0.98      ( X0 != X1
% 3.68/0.98      | X0 = sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3)
% 3.68/0.98      | sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) != X1 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_752]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5671,plain,
% 3.68/0.98      ( sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) != sK4
% 3.68/0.98      | sK4 = sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3)
% 3.68/0.98      | sK4 != sK4 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_5670]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6897,plain,
% 3.68/0.98      ( sK1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK3) = sK4
% 3.68/0.98      | k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.68/0.98      inference(resolution,[status(thm)],[c_6879,c_32]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7055,plain,
% 3.68/0.98      ( k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK3 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_6895,c_35,c_42,c_45,c_1785,c_2119,c_5300,c_5671,
% 3.68/0.98                 c_6897]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7070,plain,
% 3.68/0.98      ( r2_hidden(X0,k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
% 3.68/0.98      | ~ r2_hidden(X1,sK3)
% 3.68/0.98      | X0 != X1 ),
% 3.68/0.98      inference(resolution,[status(thm)],[c_7055,c_755]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8027,plain,
% 3.68/0.98      ( r2_hidden(X0,k4_xboole_0(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
% 3.68/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.68/0.98      inference(resolution,[status(thm)],[c_7070,c_751]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_11,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8383,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.68/0.98      | ~ r2_hidden(X0,sK3) ),
% 3.68/0.98      inference(resolution,[status(thm)],[c_8027,c_11]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8385,plain,
% 3.68/0.98      ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 3.68/0.98      | ~ r2_hidden(sK4,sK3) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_8383]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(contradiction,plain,
% 3.68/0.98      ( $false ),
% 3.68/0.98      inference(minisat,[status(thm)],[c_8385,c_7055,c_45,c_34]) ).
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  ------                               Statistics
% 3.68/0.98  
% 3.68/0.98  ------ Selected
% 3.68/0.98  
% 3.68/0.98  total_time:                             0.237
% 3.68/0.98  
%------------------------------------------------------------------------------
