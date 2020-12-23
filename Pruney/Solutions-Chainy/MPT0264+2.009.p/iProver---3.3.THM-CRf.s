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
% DateTime   : Thu Dec  3 11:35:15 EST 2020

% Result     : Theorem 35.47s
% Output     : CNFRefutation 35.47s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 319 expanded)
%              Number of clauses        :   53 (  72 expanded)
%              Number of leaves         :   17 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  327 ( 868 expanded)
%              Number of equality atoms :  185 ( 580 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) )
   => ( sK1 != sK2
      & r2_hidden(sK2,sK3)
      & k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( sK1 != sK2
    & r2_hidden(sK2,sK3)
    & k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f40])).

fof(f79,plain,(
    k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f82])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f83])).

fof(f109,plain,(
    k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f79,f57,f83,f84])).

fof(f81,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f82])).

fof(f118,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f82])).

fof(f116,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f100])).

fof(f117,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f116])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f77,f83])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f78,f83])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f57,f57])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f80,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_442,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_438,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2913,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_442,c_438])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9938,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(resolution,[status(thm)],[c_2913,c_14])).

cnf(c_33,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2909,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(X1,k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_442,c_33])).

cnf(c_113603,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(X2,k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)))
    | X2 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_9938,c_2909])).

cnf(c_439,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2242,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_439,c_438])).

cnf(c_9899,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(resolution,[status(thm)],[c_2242,c_33])).

cnf(c_118534,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)
    | ~ r2_hidden(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3))) ),
    inference(resolution,[status(thm)],[c_113603,c_9899])).

cnf(c_31,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_53,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_56,plain,
    ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1081,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_1082,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_1242,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,X2))
    | sK2 = X0
    | sK2 = X1
    | sK2 = X2 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1244,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | sK2 = sK1 ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1237,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1427,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1428,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_29,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1596,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),k3_enumset1(X1,X1,X1,X2,X3))
    | r2_hidden(sK2,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3465,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),k3_enumset1(X0,X0,X0,X0,sK2))
    | r2_hidden(sK2,k3_enumset1(X0,X0,X0,X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1596])).

cnf(c_3468,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3465])).

cnf(c_1285,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3466,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),k3_enumset1(X0,X0,X0,X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_3472,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3466])).

cnf(c_1343,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k3_enumset1(X3,X3,X3,X4,X2))
    | X0 != X2
    | X1 != k3_enumset1(X3,X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_1998,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0))
    | r2_hidden(sK2,k3_enumset1(X3,X3,X3,X4,X5))
    | k3_enumset1(X3,X3,X3,X4,X5) != k3_enumset1(X1,X1,X1,X2,X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1343])).

cnf(c_6401,plain,
    ( r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,X2))
    | ~ r2_hidden(sK2,k3_enumset1(X3,X3,X3,X4,sK2))
    | k3_enumset1(X0,X0,X0,X1,X2) != k3_enumset1(X3,X3,X3,X4,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1998])).

cnf(c_6403,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6401])).

cnf(c_9881,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_2242,c_14])).

cnf(c_10332,plain,
    ( X0 != k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3))
    | k3_enumset1(sK1,sK1,sK1,sK1,sK1) = X0 ),
    inference(resolution,[status(thm)],[c_9899,c_439])).

cnf(c_96648,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK2) ),
    inference(resolution,[status(thm)],[c_9881,c_10332])).

cnf(c_119891,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_118534,c_31,c_53,c_56,c_1082,c_1244,c_1427,c_1428,c_3468,c_3472,c_6403,c_96648])).

cnf(c_28,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_119903,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_119891,c_28])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1455,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k3_enumset1(sK1,sK1,sK1,sK1,sK2))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1,c_33])).

cnf(c_12,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_867,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1713,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_867])).

cnf(c_852,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4273,plain,
    ( r2_hidden(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1713,c_852])).

cnf(c_4275,plain,
    ( r2_hidden(sK1,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4273])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_119903,c_4275,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:11:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 35.47/5.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.47/5.01  
% 35.47/5.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.47/5.01  
% 35.47/5.01  ------  iProver source info
% 35.47/5.01  
% 35.47/5.01  git: date: 2020-06-30 10:37:57 +0100
% 35.47/5.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.47/5.01  git: non_committed_changes: false
% 35.47/5.01  git: last_make_outside_of_git: false
% 35.47/5.01  
% 35.47/5.01  ------ 
% 35.47/5.01  ------ Parsing...
% 35.47/5.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.47/5.01  
% 35.47/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.47/5.01  
% 35.47/5.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.47/5.01  
% 35.47/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.47/5.01  ------ Proving...
% 35.47/5.01  ------ Problem Properties 
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  clauses                                 33
% 35.47/5.01  conjectures                             3
% 35.47/5.01  EPR                                     4
% 35.47/5.01  Horn                                    25
% 35.47/5.01  unary                                   15
% 35.47/5.01  binary                                  5
% 35.47/5.01  lits                                    67
% 35.47/5.01  lits eq                                 29
% 35.47/5.01  fd_pure                                 0
% 35.47/5.01  fd_pseudo                               0
% 35.47/5.01  fd_cond                                 0
% 35.47/5.01  fd_pseudo_cond                          6
% 35.47/5.01  AC symbols                              0
% 35.47/5.01  
% 35.47/5.01  ------ Input Options Time Limit: Unbounded
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  ------ 
% 35.47/5.01  Current options:
% 35.47/5.01  ------ 
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  ------ Proving...
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  % SZS status Theorem for theBenchmark.p
% 35.47/5.01  
% 35.47/5.01  % SZS output start CNFRefutation for theBenchmark.p
% 35.47/5.01  
% 35.47/5.01  fof(f10,axiom,(
% 35.47/5.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f25,plain,(
% 35.47/5.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.47/5.01    inference(ennf_transformation,[],[f10])).
% 35.47/5.01  
% 35.47/5.01  fof(f56,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f25])).
% 35.47/5.01  
% 35.47/5.01  fof(f11,axiom,(
% 35.47/5.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f57,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.47/5.01    inference(cnf_transformation,[],[f11])).
% 35.47/5.01  
% 35.47/5.01  fof(f92,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 35.47/5.01    inference(definition_unfolding,[],[f56,f57])).
% 35.47/5.01  
% 35.47/5.01  fof(f21,conjecture,(
% 35.47/5.01    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f22,negated_conjecture,(
% 35.47/5.01    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 35.47/5.01    inference(negated_conjecture,[],[f21])).
% 35.47/5.01  
% 35.47/5.01  fof(f27,plain,(
% 35.47/5.01    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 35.47/5.01    inference(ennf_transformation,[],[f22])).
% 35.47/5.01  
% 35.47/5.01  fof(f40,plain,(
% 35.47/5.01    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)) => (sK1 != sK2 & r2_hidden(sK2,sK3) & k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1))),
% 35.47/5.01    introduced(choice_axiom,[])).
% 35.47/5.01  
% 35.47/5.01  fof(f41,plain,(
% 35.47/5.01    sK1 != sK2 & r2_hidden(sK2,sK3) & k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1)),
% 35.47/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f40])).
% 35.47/5.01  
% 35.47/5.01  fof(f79,plain,(
% 35.47/5.01    k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1)),
% 35.47/5.01    inference(cnf_transformation,[],[f41])).
% 35.47/5.01  
% 35.47/5.01  fof(f15,axiom,(
% 35.47/5.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f68,plain,(
% 35.47/5.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f15])).
% 35.47/5.01  
% 35.47/5.01  fof(f16,axiom,(
% 35.47/5.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f69,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f16])).
% 35.47/5.01  
% 35.47/5.01  fof(f17,axiom,(
% 35.47/5.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f70,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f17])).
% 35.47/5.01  
% 35.47/5.01  fof(f18,axiom,(
% 35.47/5.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f71,plain,(
% 35.47/5.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f18])).
% 35.47/5.01  
% 35.47/5.01  fof(f82,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 35.47/5.01    inference(definition_unfolding,[],[f70,f71])).
% 35.47/5.01  
% 35.47/5.01  fof(f83,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 35.47/5.01    inference(definition_unfolding,[],[f69,f82])).
% 35.47/5.01  
% 35.47/5.01  fof(f84,plain,(
% 35.47/5.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 35.47/5.01    inference(definition_unfolding,[],[f68,f83])).
% 35.47/5.01  
% 35.47/5.01  fof(f109,plain,(
% 35.47/5.01    k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 35.47/5.01    inference(definition_unfolding,[],[f79,f57,f83,f84])).
% 35.47/5.01  
% 35.47/5.01  fof(f81,plain,(
% 35.47/5.01    sK1 != sK2),
% 35.47/5.01    inference(cnf_transformation,[],[f41])).
% 35.47/5.01  
% 35.47/5.01  fof(f14,axiom,(
% 35.47/5.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f26,plain,(
% 35.47/5.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 35.47/5.01    inference(ennf_transformation,[],[f14])).
% 35.47/5.01  
% 35.47/5.01  fof(f31,plain,(
% 35.47/5.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.47/5.01    inference(nnf_transformation,[],[f26])).
% 35.47/5.01  
% 35.47/5.01  fof(f32,plain,(
% 35.47/5.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.47/5.01    inference(flattening,[],[f31])).
% 35.47/5.01  
% 35.47/5.01  fof(f33,plain,(
% 35.47/5.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.47/5.01    inference(rectify,[],[f32])).
% 35.47/5.01  
% 35.47/5.01  fof(f34,plain,(
% 35.47/5.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 35.47/5.01    introduced(choice_axiom,[])).
% 35.47/5.01  
% 35.47/5.01  fof(f35,plain,(
% 35.47/5.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.47/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 35.47/5.01  
% 35.47/5.01  fof(f60,plain,(
% 35.47/5.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 35.47/5.01    inference(cnf_transformation,[],[f35])).
% 35.47/5.01  
% 35.47/5.01  fof(f101,plain,(
% 35.47/5.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 35.47/5.01    inference(definition_unfolding,[],[f60,f82])).
% 35.47/5.01  
% 35.47/5.01  fof(f118,plain,(
% 35.47/5.01    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 35.47/5.01    inference(equality_resolution,[],[f101])).
% 35.47/5.01  
% 35.47/5.01  fof(f61,plain,(
% 35.47/5.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 35.47/5.01    inference(cnf_transformation,[],[f35])).
% 35.47/5.01  
% 35.47/5.01  fof(f100,plain,(
% 35.47/5.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 35.47/5.01    inference(definition_unfolding,[],[f61,f82])).
% 35.47/5.01  
% 35.47/5.01  fof(f116,plain,(
% 35.47/5.01    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 35.47/5.01    inference(equality_resolution,[],[f100])).
% 35.47/5.01  
% 35.47/5.01  fof(f117,plain,(
% 35.47/5.01    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 35.47/5.01    inference(equality_resolution,[],[f116])).
% 35.47/5.01  
% 35.47/5.01  fof(f4,axiom,(
% 35.47/5.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f29,plain,(
% 35.47/5.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.47/5.01    inference(nnf_transformation,[],[f4])).
% 35.47/5.01  
% 35.47/5.01  fof(f30,plain,(
% 35.47/5.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.47/5.01    inference(flattening,[],[f29])).
% 35.47/5.01  
% 35.47/5.01  fof(f50,plain,(
% 35.47/5.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f30])).
% 35.47/5.01  
% 35.47/5.01  fof(f48,plain,(
% 35.47/5.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.47/5.01    inference(cnf_transformation,[],[f30])).
% 35.47/5.01  
% 35.47/5.01  fof(f111,plain,(
% 35.47/5.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.47/5.01    inference(equality_resolution,[],[f48])).
% 35.47/5.01  
% 35.47/5.01  fof(f20,axiom,(
% 35.47/5.01    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f38,plain,(
% 35.47/5.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 35.47/5.01    inference(nnf_transformation,[],[f20])).
% 35.47/5.01  
% 35.47/5.01  fof(f39,plain,(
% 35.47/5.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 35.47/5.01    inference(flattening,[],[f38])).
% 35.47/5.01  
% 35.47/5.01  fof(f77,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f39])).
% 35.47/5.01  
% 35.47/5.01  fof(f107,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 35.47/5.01    inference(definition_unfolding,[],[f77,f83])).
% 35.47/5.01  
% 35.47/5.01  fof(f78,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f39])).
% 35.47/5.01  
% 35.47/5.01  fof(f106,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 35.47/5.01    inference(definition_unfolding,[],[f78,f83])).
% 35.47/5.01  
% 35.47/5.01  fof(f1,axiom,(
% 35.47/5.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f42,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f1])).
% 35.47/5.01  
% 35.47/5.01  fof(f86,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 35.47/5.01    inference(definition_unfolding,[],[f42,f57,f57])).
% 35.47/5.01  
% 35.47/5.01  fof(f8,axiom,(
% 35.47/5.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f54,plain,(
% 35.47/5.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f8])).
% 35.47/5.01  
% 35.47/5.01  fof(f90,plain,(
% 35.47/5.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 35.47/5.01    inference(definition_unfolding,[],[f54,f57])).
% 35.47/5.01  
% 35.47/5.01  fof(f80,plain,(
% 35.47/5.01    r2_hidden(sK2,sK3)),
% 35.47/5.01    inference(cnf_transformation,[],[f41])).
% 35.47/5.01  
% 35.47/5.01  cnf(c_442,plain,
% 35.47/5.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.47/5.01      theory(equality) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_438,plain,( X0 = X0 ),theory(equality) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_2913,plain,
% 35.47/5.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_442,c_438]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_14,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 35.47/5.01      inference(cnf_transformation,[],[f92]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_9938,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1)
% 35.47/5.01      | ~ r2_hidden(X0,X2)
% 35.47/5.01      | r2_hidden(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_2913,c_14]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_33,negated_conjecture,
% 35.47/5.01      ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 35.47/5.01      inference(cnf_transformation,[],[f109]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_2909,plain,
% 35.47/5.01      ( ~ r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
% 35.47/5.01      | r2_hidden(X1,k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)))
% 35.47/5.01      | X1 != X0 ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_442,c_33]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_113603,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1)
% 35.47/5.01      | ~ r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
% 35.47/5.01      | r2_hidden(X2,k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)))
% 35.47/5.01      | X2 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_9938,c_2909]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_439,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_2242,plain,
% 35.47/5.01      ( X0 != X1 | X1 = X0 ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_439,c_438]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_9899,plain,
% 35.47/5.01      ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)) ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_2242,c_33]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_118534,plain,
% 35.47/5.01      ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)
% 35.47/5.01      | ~ r2_hidden(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
% 35.47/5.01      | r2_hidden(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3))) ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_113603,c_9899]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_31,negated_conjecture,
% 35.47/5.01      ( sK1 != sK2 ),
% 35.47/5.01      inference(cnf_transformation,[],[f81]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_23,plain,
% 35.47/5.01      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 35.47/5.01      | X0 = X1
% 35.47/5.01      | X0 = X2
% 35.47/5.01      | X0 = X3 ),
% 35.47/5.01      inference(cnf_transformation,[],[f118]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_53,plain,
% 35.47/5.01      ( ~ r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | sK1 = sK1 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_23]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_22,plain,
% 35.47/5.01      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 35.47/5.01      inference(cnf_transformation,[],[f117]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_56,plain,
% 35.47/5.01      ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_22]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1081,plain,
% 35.47/5.01      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_439]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1082,plain,
% 35.47/5.01      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1081]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1242,plain,
% 35.47/5.01      ( ~ r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,X2))
% 35.47/5.01      | sK2 = X0
% 35.47/5.01      | sK2 = X1
% 35.47/5.01      | sK2 = X2 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_23]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1244,plain,
% 35.47/5.01      ( ~ r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | sK2 = sK1 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1242]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_7,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.47/5.01      inference(cnf_transformation,[],[f50]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1237,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_7]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1427,plain,
% 35.47/5.01      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1237]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_9,plain,
% 35.47/5.01      ( r1_tarski(X0,X0) ),
% 35.47/5.01      inference(cnf_transformation,[],[f111]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1428,plain,
% 35.47/5.01      ( r1_tarski(sK2,sK2) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_9]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_29,plain,
% 35.47/5.01      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2) ),
% 35.47/5.01      inference(cnf_transformation,[],[f107]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1596,plain,
% 35.47/5.01      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),k3_enumset1(X1,X1,X1,X2,X3))
% 35.47/5.01      | r2_hidden(sK2,k3_enumset1(X1,X1,X1,X2,X3)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_29]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_3465,plain,
% 35.47/5.01      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),k3_enumset1(X0,X0,X0,X0,sK2))
% 35.47/5.01      | r2_hidden(sK2,k3_enumset1(X0,X0,X0,X0,sK2)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1596]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_3468,plain,
% 35.47/5.01      ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2))
% 35.47/5.01      | r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_3465]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1285,plain,
% 35.47/5.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X0,X0,X0,X0,X1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_9]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_3466,plain,
% 35.47/5.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),k3_enumset1(X0,X0,X0,X0,sK2)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1285]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_3472,plain,
% 35.47/5.01      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_3466]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1343,plain,
% 35.47/5.01      ( r2_hidden(X0,X1)
% 35.47/5.01      | ~ r2_hidden(X2,k3_enumset1(X3,X3,X3,X4,X2))
% 35.47/5.01      | X0 != X2
% 35.47/5.01      | X1 != k3_enumset1(X3,X3,X3,X4,X2) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_442]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1998,plain,
% 35.47/5.01      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0))
% 35.47/5.01      | r2_hidden(sK2,k3_enumset1(X3,X3,X3,X4,X5))
% 35.47/5.01      | k3_enumset1(X3,X3,X3,X4,X5) != k3_enumset1(X1,X1,X1,X2,X0)
% 35.47/5.01      | sK2 != X0 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1343]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_6401,plain,
% 35.47/5.01      ( r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,X2))
% 35.47/5.01      | ~ r2_hidden(sK2,k3_enumset1(X3,X3,X3,X4,sK2))
% 35.47/5.01      | k3_enumset1(X0,X0,X0,X1,X2) != k3_enumset1(X3,X3,X3,X4,sK2)
% 35.47/5.01      | sK2 != sK2 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1998]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_6403,plain,
% 35.47/5.01      ( ~ r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK2))
% 35.47/5.01      | r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
% 35.47/5.01      | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK2)
% 35.47/5.01      | sK2 != sK2 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_6401]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_9881,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1) | X0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_2242,c_14]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_10332,plain,
% 35.47/5.01      ( X0 != k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3))
% 35.47/5.01      | k3_enumset1(sK1,sK1,sK1,sK1,sK1) = X0 ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_9899,c_439]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_96648,plain,
% 35.47/5.01      ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3)
% 35.47/5.01      | k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK2) ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_9881,c_10332]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_119891,plain,
% 35.47/5.01      ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3) ),
% 35.47/5.01      inference(global_propositional_subsumption,
% 35.47/5.01                [status(thm)],
% 35.47/5.01                [c_118534,c_31,c_53,c_56,c_1082,c_1244,c_1427,c_1428,
% 35.47/5.01                 c_3468,c_3472,c_6403,c_96648]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_28,plain,
% 35.47/5.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 35.47/5.01      | ~ r2_hidden(X0,X2)
% 35.47/5.01      | ~ r2_hidden(X1,X2) ),
% 35.47/5.01      inference(cnf_transformation,[],[f106]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_119903,plain,
% 35.47/5.01      ( ~ r2_hidden(sK2,sK3) | ~ r2_hidden(sK1,sK3) ),
% 35.47/5.01      inference(resolution,[status(thm)],[c_119891,c_28]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1,plain,
% 35.47/5.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 35.47/5.01      inference(cnf_transformation,[],[f86]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1455,plain,
% 35.47/5.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k3_enumset1(sK1,sK1,sK1,sK1,sK2))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_1,c_33]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_12,plain,
% 35.47/5.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 35.47/5.01      inference(cnf_transformation,[],[f90]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_867,plain,
% 35.47/5.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 35.47/5.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1713,plain,
% 35.47/5.01      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3) = iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_1455,c_867]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_852,plain,
% 35.47/5.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
% 35.47/5.01      | r2_hidden(X1,X2) = iProver_top ),
% 35.47/5.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_4273,plain,
% 35.47/5.01      ( r2_hidden(sK1,sK3) = iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_1713,c_852]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_4275,plain,
% 35.47/5.01      ( r2_hidden(sK1,sK3) ),
% 35.47/5.01      inference(predicate_to_equality_rev,[status(thm)],[c_4273]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_32,negated_conjecture,
% 35.47/5.01      ( r2_hidden(sK2,sK3) ),
% 35.47/5.01      inference(cnf_transformation,[],[f80]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(contradiction,plain,
% 35.47/5.01      ( $false ),
% 35.47/5.01      inference(minisat,[status(thm)],[c_119903,c_4275,c_32]) ).
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.47/5.01  
% 35.47/5.01  ------                               Statistics
% 35.47/5.01  
% 35.47/5.01  ------ Selected
% 35.47/5.01  
% 35.47/5.01  total_time:                             4.389
% 35.47/5.01  
%------------------------------------------------------------------------------
