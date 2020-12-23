%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:37 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 188 expanded)
%              Number of clauses        :   37 (  37 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  356 ( 604 expanded)
%              Number of equality atoms :  165 ( 345 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f40])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f94,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f80])).

fof(f95,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f94])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

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
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f96,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f81])).

fof(f97,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f96])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f67,f76,f76,f76])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f66,f76,f76,f76])).

fof(f99,plain,(
    ! [X1] : k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f13,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f42])).

fof(f74,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f74,f76])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_25,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10449,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | sK3(k2_enumset1(X1,X1,X1,X2),X0) = X1
    | sK3(k2_enumset1(X1,X1,X1,X2),X0) = X2
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X2) ),
    inference(resolution,[status(thm)],[c_18,c_25])).

cnf(c_10451,plain,
    ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_10449])).

cnf(c_323,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10422,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_10424,plain,
    ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | ~ r1_tarski(sK4,sK4)
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_10422])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,sK3(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10339,plain,
    ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9450,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X3,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X3,X2) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_9607,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
    | r2_hidden(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != k2_enumset1(X1,X1,X1,X0) ),
    inference(instantiation,[status(thm)],[c_9450])).

cnf(c_9609,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_9607])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_7958,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_7962,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8687,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_7962])).

cnf(c_8928,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7958,c_8687])).

cnf(c_8930,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8928])).

cnf(c_8932,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8930])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8371,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r1_tarski(X0,sK4)
    | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_8373,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_8371])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2275,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_64,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_52,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_47,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k2_enumset1(sK4,sK4,sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_20,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_46,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_27,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f88])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10451,c_10424,c_10339,c_9609,c_8932,c_8373,c_2275,c_64,c_52,c_47,c_46,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:09:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.90/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/0.97  
% 3.90/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/0.97  
% 3.90/0.97  ------  iProver source info
% 3.90/0.97  
% 3.90/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.90/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/0.97  git: non_committed_changes: false
% 3.90/0.97  git: last_make_outside_of_git: false
% 3.90/0.97  
% 3.90/0.97  ------ 
% 3.90/0.97  ------ Parsing...
% 3.90/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  ------ Proving...
% 3.90/0.97  ------ Problem Properties 
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  clauses                                 27
% 3.90/0.97  conjectures                             1
% 3.90/0.97  EPR                                     3
% 3.90/0.97  Horn                                    16
% 3.90/0.97  unary                                   7
% 3.90/0.97  binary                                  6
% 3.90/0.97  lits                                    63
% 3.90/0.97  lits eq                                 21
% 3.90/0.97  fd_pure                                 0
% 3.90/0.97  fd_pseudo                               0
% 3.90/0.97  fd_cond                                 2
% 3.90/0.97  fd_pseudo_cond                          9
% 3.90/0.97  AC symbols                              0
% 3.90/0.97  
% 3.90/0.97  ------ Input Options Time Limit: Unbounded
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing...
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.90/0.97  Current options:
% 3.90/0.97  ------ 
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing...
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.90/0.97  
% 3.90/0.97  ------ Proving...
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  % SZS status Theorem for theBenchmark.p
% 3.90/0.97  
% 3.90/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/0.97  
% 3.90/0.97  fof(f5,axiom,(
% 3.90/0.97    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f32,plain,(
% 3.90/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.90/0.97    inference(nnf_transformation,[],[f5])).
% 3.90/0.97  
% 3.90/0.97  fof(f33,plain,(
% 3.90/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.90/0.97    inference(flattening,[],[f32])).
% 3.90/0.97  
% 3.90/0.97  fof(f34,plain,(
% 3.90/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.90/0.97    inference(rectify,[],[f33])).
% 3.90/0.97  
% 3.90/0.97  fof(f35,plain,(
% 3.90/0.97    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.90/0.97    introduced(choice_axiom,[])).
% 3.90/0.97  
% 3.90/0.97  fof(f36,plain,(
% 3.90/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.90/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 3.90/0.97  
% 3.90/0.97  fof(f57,plain,(
% 3.90/0.97    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.90/0.97    inference(cnf_transformation,[],[f36])).
% 3.90/0.97  
% 3.90/0.97  fof(f7,axiom,(
% 3.90/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f64,plain,(
% 3.90/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.90/0.97    inference(cnf_transformation,[],[f7])).
% 3.90/0.97  
% 3.90/0.97  fof(f8,axiom,(
% 3.90/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f65,plain,(
% 3.90/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.90/0.97    inference(cnf_transformation,[],[f8])).
% 3.90/0.97  
% 3.90/0.97  fof(f75,plain,(
% 3.90/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.90/0.97    inference(definition_unfolding,[],[f64,f65])).
% 3.90/0.97  
% 3.90/0.97  fof(f82,plain,(
% 3.90/0.97    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.90/0.97    inference(definition_unfolding,[],[f57,f75])).
% 3.90/0.97  
% 3.90/0.97  fof(f98,plain,(
% 3.90/0.97    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 3.90/0.97    inference(equality_resolution,[],[f82])).
% 3.90/0.97  
% 3.90/0.97  fof(f11,axiom,(
% 3.90/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f16,plain,(
% 3.90/0.97    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.90/0.97    inference(ennf_transformation,[],[f11])).
% 3.90/0.97  
% 3.90/0.97  fof(f17,plain,(
% 3.90/0.97    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.90/0.97    inference(flattening,[],[f16])).
% 3.90/0.97  
% 3.90/0.97  fof(f40,plain,(
% 3.90/0.97    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 3.90/0.97    introduced(choice_axiom,[])).
% 3.90/0.97  
% 3.90/0.97  fof(f41,plain,(
% 3.90/0.97    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 3.90/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f40])).
% 3.90/0.97  
% 3.90/0.97  fof(f71,plain,(
% 3.90/0.97    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 3.90/0.97    inference(cnf_transformation,[],[f41])).
% 3.90/0.97  
% 3.90/0.97  fof(f72,plain,(
% 3.90/0.97    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 3.90/0.97    inference(cnf_transformation,[],[f41])).
% 3.90/0.97  
% 3.90/0.97  fof(f59,plain,(
% 3.90/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.90/0.97    inference(cnf_transformation,[],[f36])).
% 3.90/0.97  
% 3.90/0.97  fof(f80,plain,(
% 3.90/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.90/0.97    inference(definition_unfolding,[],[f59,f75])).
% 3.90/0.97  
% 3.90/0.97  fof(f94,plain,(
% 3.90/0.97    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 3.90/0.97    inference(equality_resolution,[],[f80])).
% 3.90/0.97  
% 3.90/0.97  fof(f95,plain,(
% 3.90/0.97    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 3.90/0.97    inference(equality_resolution,[],[f94])).
% 3.90/0.97  
% 3.90/0.97  fof(f4,axiom,(
% 3.90/0.97    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f56,plain,(
% 3.90/0.97    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.90/0.97    inference(cnf_transformation,[],[f4])).
% 3.90/0.97  
% 3.90/0.97  fof(f2,axiom,(
% 3.90/0.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f25,plain,(
% 3.90/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.90/0.97    inference(nnf_transformation,[],[f2])).
% 3.90/0.97  
% 3.90/0.97  fof(f26,plain,(
% 3.90/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.90/0.97    inference(flattening,[],[f25])).
% 3.90/0.97  
% 3.90/0.97  fof(f27,plain,(
% 3.90/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.90/0.97    inference(rectify,[],[f26])).
% 3.90/0.97  
% 3.90/0.97  fof(f28,plain,(
% 3.90/0.97    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.90/0.97    introduced(choice_axiom,[])).
% 3.90/0.97  
% 3.90/0.97  fof(f29,plain,(
% 3.90/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.90/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 3.90/0.97  
% 3.90/0.97  fof(f48,plain,(
% 3.90/0.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.90/0.97    inference(cnf_transformation,[],[f29])).
% 3.90/0.97  
% 3.90/0.97  fof(f90,plain,(
% 3.90/0.97    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.90/0.97    inference(equality_resolution,[],[f48])).
% 3.90/0.97  
% 3.90/0.97  fof(f12,axiom,(
% 3.90/0.97    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f18,plain,(
% 3.90/0.97    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 3.90/0.97    inference(ennf_transformation,[],[f12])).
% 3.90/0.97  
% 3.90/0.97  fof(f19,plain,(
% 3.90/0.97    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 3.90/0.97    inference(flattening,[],[f18])).
% 3.90/0.97  
% 3.90/0.97  fof(f73,plain,(
% 3.90/0.97    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.90/0.97    inference(cnf_transformation,[],[f19])).
% 3.90/0.97  
% 3.90/0.97  fof(f3,axiom,(
% 3.90/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f30,plain,(
% 3.90/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.90/0.97    inference(nnf_transformation,[],[f3])).
% 3.90/0.97  
% 3.90/0.97  fof(f31,plain,(
% 3.90/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.90/0.97    inference(flattening,[],[f30])).
% 3.90/0.97  
% 3.90/0.97  fof(f55,plain,(
% 3.90/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.90/0.97    inference(cnf_transformation,[],[f31])).
% 3.90/0.97  
% 3.90/0.97  fof(f53,plain,(
% 3.90/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.90/0.97    inference(cnf_transformation,[],[f31])).
% 3.90/0.97  
% 3.90/0.97  fof(f93,plain,(
% 3.90/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.90/0.97    inference(equality_resolution,[],[f53])).
% 3.90/0.97  
% 3.90/0.97  fof(f58,plain,(
% 3.90/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.90/0.97    inference(cnf_transformation,[],[f36])).
% 3.90/0.97  
% 3.90/0.97  fof(f81,plain,(
% 3.90/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.90/0.97    inference(definition_unfolding,[],[f58,f75])).
% 3.90/0.97  
% 3.90/0.97  fof(f96,plain,(
% 3.90/0.97    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.90/0.97    inference(equality_resolution,[],[f81])).
% 3.90/0.97  
% 3.90/0.97  fof(f97,plain,(
% 3.90/0.97    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.90/0.97    inference(equality_resolution,[],[f96])).
% 3.90/0.97  
% 3.90/0.97  fof(f9,axiom,(
% 3.90/0.97    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f37,plain,(
% 3.90/0.97    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.90/0.97    inference(nnf_transformation,[],[f9])).
% 3.90/0.97  
% 3.90/0.97  fof(f67,plain,(
% 3.90/0.97    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.90/0.97    inference(cnf_transformation,[],[f37])).
% 3.90/0.97  
% 3.90/0.97  fof(f6,axiom,(
% 3.90/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f63,plain,(
% 3.90/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.90/0.97    inference(cnf_transformation,[],[f6])).
% 3.90/0.97  
% 3.90/0.97  fof(f76,plain,(
% 3.90/0.97    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.90/0.97    inference(definition_unfolding,[],[f63,f75])).
% 3.90/0.97  
% 3.90/0.97  fof(f83,plain,(
% 3.90/0.97    ( ! [X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0) | X0 = X1) )),
% 3.90/0.97    inference(definition_unfolding,[],[f67,f76,f76,f76])).
% 3.90/0.97  
% 3.90/0.97  fof(f66,plain,(
% 3.90/0.97    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.90/0.97    inference(cnf_transformation,[],[f37])).
% 3.90/0.97  
% 3.90/0.97  fof(f84,plain,(
% 3.90/0.97    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 3.90/0.97    inference(definition_unfolding,[],[f66,f76,f76,f76])).
% 3.90/0.97  
% 3.90/0.97  fof(f99,plain,(
% 3.90/0.97    ( ! [X1] : (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1)) )),
% 3.90/0.97    inference(equality_resolution,[],[f84])).
% 3.90/0.97  
% 3.90/0.97  fof(f13,conjecture,(
% 3.90/0.97    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.90/0.97  
% 3.90/0.97  fof(f14,negated_conjecture,(
% 3.90/0.97    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.90/0.97    inference(negated_conjecture,[],[f13])).
% 3.90/0.97  
% 3.90/0.97  fof(f20,plain,(
% 3.90/0.97    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 3.90/0.97    inference(ennf_transformation,[],[f14])).
% 3.90/0.97  
% 3.90/0.97  fof(f42,plain,(
% 3.90/0.97    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.90/0.97    introduced(choice_axiom,[])).
% 3.90/0.97  
% 3.90/0.97  fof(f43,plain,(
% 3.90/0.97    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.90/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f42])).
% 3.90/0.97  
% 3.90/0.97  fof(f74,plain,(
% 3.90/0.97    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.90/0.97    inference(cnf_transformation,[],[f43])).
% 3.90/0.97  
% 3.90/0.97  fof(f88,plain,(
% 3.90/0.97    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 3.90/0.97    inference(definition_unfolding,[],[f74,f76])).
% 3.90/0.97  
% 3.90/0.97  cnf(c_18,plain,
% 3.90/0.97      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.90/0.97      inference(cnf_transformation,[],[f98]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_25,plain,
% 3.90/0.97      ( r2_hidden(sK3(X0,X1),X0)
% 3.90/0.97      | r1_tarski(X1,k1_setfam_1(X0))
% 3.90/0.97      | k1_xboole_0 = X0 ),
% 3.90/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_10449,plain,
% 3.90/0.97      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
% 3.90/0.97      | sK3(k2_enumset1(X1,X1,X1,X2),X0) = X1
% 3.90/0.97      | sK3(k2_enumset1(X1,X1,X1,X2),X0) = X2
% 3.90/0.97      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X2) ),
% 3.90/0.97      inference(resolution,[status(thm)],[c_18,c_25]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_10451,plain,
% 3.90/0.97      ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.90/0.97      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
% 3.90/0.97      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_10449]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_323,plain,
% 3.90/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.90/0.97      theory(equality) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_10422,plain,
% 3.90/0.97      ( ~ r1_tarski(X0,X1)
% 3.90/0.97      | r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 3.90/0.97      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != X1
% 3.90/0.97      | sK4 != X0 ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_323]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_10424,plain,
% 3.90/0.97      ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 3.90/0.97      | ~ r1_tarski(sK4,sK4)
% 3.90/0.97      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
% 3.90/0.97      | sK4 != sK4 ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_10422]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_24,plain,
% 3.90/0.97      ( ~ r1_tarski(X0,sK3(X1,X0))
% 3.90/0.97      | r1_tarski(X0,k1_setfam_1(X1))
% 3.90/0.97      | k1_xboole_0 = X1 ),
% 3.90/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_10339,plain,
% 3.90/0.97      ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 3.90/0.97      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.90/0.97      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_24]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_324,plain,
% 3.90/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.90/0.97      theory(equality) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_9450,plain,
% 3.90/0.97      ( r2_hidden(X0,X1)
% 3.90/0.97      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X3,X2))
% 3.90/0.97      | X0 != X2
% 3.90/0.97      | X1 != k2_enumset1(X3,X3,X3,X2) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_324]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_9607,plain,
% 3.90/0.97      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
% 3.90/0.97      | r2_hidden(X2,k1_xboole_0)
% 3.90/0.97      | X2 != X0
% 3.90/0.97      | k1_xboole_0 != k2_enumset1(X1,X1,X1,X0) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_9450]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_9609,plain,
% 3.90/0.97      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.90/0.97      | r2_hidden(sK4,k1_xboole_0)
% 3.90/0.97      | sK4 != sK4
% 3.90/0.97      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_9607]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_16,plain,
% 3.90/0.97      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 3.90/0.97      inference(cnf_transformation,[],[f95]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_7958,plain,
% 3.90/0.97      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 3.90/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_12,plain,
% 3.90/0.97      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.90/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_7,plain,
% 3.90/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.90/0.97      inference(cnf_transformation,[],[f90]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_7962,plain,
% 3.90/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.90/0.97      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.90/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_8687,plain,
% 3.90/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.90/0.97      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.90/0.97      inference(superposition,[status(thm)],[c_12,c_7962]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_8928,plain,
% 3.90/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.90/0.97      inference(superposition,[status(thm)],[c_7958,c_8687]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_8930,plain,
% 3.90/0.97      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.90/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_8928]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_8932,plain,
% 3.90/0.97      ( ~ r2_hidden(sK4,k1_xboole_0) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_8930]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_26,plain,
% 3.90/0.97      ( ~ r2_hidden(X0,X1)
% 3.90/0.97      | ~ r1_tarski(X0,X2)
% 3.90/0.97      | r1_tarski(k1_setfam_1(X1),X2) ),
% 3.90/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_8371,plain,
% 3.90/0.97      ( ~ r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.90/0.97      | ~ r1_tarski(X0,sK4)
% 3.90/0.97      | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_26]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_8373,plain,
% 3.90/0.97      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.90/0.97      | r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 3.90/0.97      | ~ r1_tarski(sK4,sK4) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_8371]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_9,plain,
% 3.90/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.90/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_2275,plain,
% 3.90/0.97      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 3.90/0.97      | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.90/0.97      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_11,plain,
% 3.90/0.97      ( r1_tarski(X0,X0) ),
% 3.90/0.97      inference(cnf_transformation,[],[f93]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_64,plain,
% 3.90/0.97      ( r1_tarski(sK4,sK4) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_17,plain,
% 3.90/0.97      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.90/0.97      inference(cnf_transformation,[],[f97]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_52,plain,
% 3.90/0.97      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_17]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_19,plain,
% 3.90/0.97      ( X0 = X1
% 3.90/0.97      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
% 3.90/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_47,plain,
% 3.90/0.97      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k2_enumset1(sK4,sK4,sK4,sK4)
% 3.90/0.97      | sK4 = sK4 ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_19]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_20,plain,
% 3.90/0.97      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 3.90/0.97      inference(cnf_transformation,[],[f99]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_46,plain,
% 3.90/0.97      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.90/0.97      inference(instantiation,[status(thm)],[c_20]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(c_27,negated_conjecture,
% 3.90/0.97      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 3.90/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.90/0.97  
% 3.90/0.97  cnf(contradiction,plain,
% 3.90/0.97      ( $false ),
% 3.90/0.97      inference(minisat,
% 3.90/0.97                [status(thm)],
% 3.90/0.97                [c_10451,c_10424,c_10339,c_9609,c_8932,c_8373,c_2275,
% 3.90/0.97                 c_64,c_52,c_47,c_46,c_27]) ).
% 3.90/0.97  
% 3.90/0.97  
% 3.90/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/0.97  
% 3.90/0.97  ------                               Statistics
% 3.90/0.97  
% 3.90/0.97  ------ Selected
% 3.90/0.97  
% 3.90/0.97  total_time:                             0.316
% 3.90/0.97  
%------------------------------------------------------------------------------
