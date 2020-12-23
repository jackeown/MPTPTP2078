%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:10 EST 2020

% Result     : Theorem 27.71s
% Output     : CNFRefutation 27.71s
% Verified   : 
% Statistics : Number of formulae       :  262 (37857 expanded)
%              Number of clauses        :  145 (3847 expanded)
%              Number of leaves         :   32 (11746 expanded)
%              Depth                    :   35
%              Number of atoms          :  680 (64917 expanded)
%              Number of equality atoms :  424 (51262 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f23])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f24])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f25])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f95,f96])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f94,f104])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f93,f105])).

fof(f107,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f92,f106])).

fof(f108,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f91,f107])).

fof(f109,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f99,f108])).

fof(f110,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f85,f109])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f69,f110])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f58,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK6
        | k1_tarski(sK4) != sK5 )
      & ( k1_tarski(sK4) != sK6
        | k1_xboole_0 != sK5 )
      & ( k1_tarski(sK4) != sK6
        | k1_tarski(sK4) != sK5 )
      & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( k1_xboole_0 != sK6
      | k1_tarski(sK4) != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_xboole_0 != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_tarski(sK4) != sK5 )
    & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f58])).

fof(f100,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f112,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f90,f108])).

fof(f135,plain,(
    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f100,f109,f112])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f65,f110])).

fof(f138,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f119])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f67,f110])).

fof(f136,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f117])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f70,f110])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f120,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f109])).

fof(f16,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f7])).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f121,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f73,f110])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f88,f112])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f129,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f86,f112])).

fof(f143,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f129])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f49])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,
    ( k1_xboole_0 != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f59])).

fof(f132,plain,
    ( k1_xboole_0 != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f103,f112])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f128,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f87,f112])).

fof(f141,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f128])).

fof(f142,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f141])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f130,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f98,f112])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f140,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f113,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f60,f109,f109])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f124,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f81,f109,f109,f109])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f125,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f82,f109])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f118,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f66,f110])).

fof(f137,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f118])).

fof(f101,plain,
    ( k1_tarski(sK4) != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f59])).

fof(f134,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f101,f112,f112])).

fof(f102,plain,
    ( k1_tarski(sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f59])).

fof(f133,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(definition_unfolding,[],[f102,f112])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_22,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_567,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2 ),
    inference(theory_normalisation,[status(thm)],[c_6,c_22,c_1])).

cnf(c_1088,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_1117,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_22,c_1])).

cnf(c_33,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_563,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_22,c_1])).

cnf(c_1084,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_26756,plain,
    ( r2_hidden(X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1084])).

cnf(c_31005,plain,
    ( r2_hidden(X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_26756])).

cnf(c_41343,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | r2_hidden(sK1(X0,X1,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_31005])).

cnf(c_41342,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | r2_hidden(sK1(X0,X1,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_26756])).

cnf(c_41666,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | r2_hidden(sK1(X0,X1,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
    | r2_hidden(sK1(X0,X1,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_41342])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_565,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_8,c_22,c_1])).

cnf(c_1086,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_34502,plain,
    ( r2_hidden(X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1086])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_568,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2 ),
    inference(theory_normalisation,[status(thm)],[c_5,c_22,c_1])).

cnf(c_1089,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_55042,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) != iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_41666,c_1089])).

cnf(c_12,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_23,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_562,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_13,c_22,c_1])).

cnf(c_1093,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_562,c_12,c_23])).

cnf(c_55063,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) != iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_55042,c_12,c_23,c_1093])).

cnf(c_77893,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) != iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) != iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_34502,c_55063])).

cnf(c_78193,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) != iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_41666,c_77893])).

cnf(c_78200,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) != iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_78193,c_12,c_23,c_1093])).

cnf(c_81058,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_41343,c_78200])).

cnf(c_81069,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_81058,c_12,c_23,c_1093])).

cnf(c_25,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1075,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) = X0
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f143])).

cnf(c_1073,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8181,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | sK3(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X1
    | sK3(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1075,c_1073])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1082,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_31002,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0
    | r2_hidden(sK2(k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_26756])).

cnf(c_61217,plain,
    ( sK3(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = X0
    | sK3(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = sK4
    | k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0
    | r2_hidden(sK2(k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_8181,c_31002])).

cnf(c_30,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_41,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_26,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_44,plain,
    ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1130,plain,
    ( r2_hidden(sK2(sK6),sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1183,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
    | ~ r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1495,plain,
    ( ~ r2_hidden(sK4,sK6)
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1555,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2135,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_17,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_5359,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_576,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1893,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4,sK6)
    | sK4 != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_7200,plain,
    ( ~ r2_hidden(sK2(sK6),sK6)
    | r2_hidden(sK4,sK6)
    | sK4 != sK2(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1893])).

cnf(c_0,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1586,plain,
    ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_33,c_0])).

cnf(c_20,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1741,plain,
    ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK5)) ),
    inference(superposition,[status(thm)],[c_1586,c_20])).

cnf(c_1742,plain,
    ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_1741,c_1586])).

cnf(c_21,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1077,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13130,plain,
    ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_1077])).

cnf(c_13134,plain,
    ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13130])).

cnf(c_1072,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1739,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_33,c_20])).

cnf(c_1740,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_1739,c_33])).

cnf(c_13129,plain,
    ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1740,c_1077])).

cnf(c_1081,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_32989,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_13129,c_1081])).

cnf(c_34245,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_32989])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4227,plain,
    ( r2_hidden(sK2(sK6),X0)
    | ~ r2_hidden(sK2(sK6),sK6)
    | ~ r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_41278,plain,
    ( r2_hidden(sK2(sK6),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK2(sK6),sK6)
    | ~ r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_4227])).

cnf(c_571,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_42350,plain,
    ( sK2(sK6) != X0
    | sK4 != X0
    | sK4 = sK2(sK6) ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_42351,plain,
    ( sK2(sK6) != sK4
    | sK4 = sK2(sK6)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_42350])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_564,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_9,c_22,c_1])).

cnf(c_1085,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_31493,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1740,c_1085])).

cnf(c_1541,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_23,c_22])).

cnf(c_1418,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1093,c_1])).

cnf(c_1547,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1541,c_1418])).

cnf(c_1945,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_1547])).

cnf(c_31496,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31493,c_1945])).

cnf(c_34105,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_31496,c_1073])).

cnf(c_43612,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0
    | sK2(k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = sK4 ),
    inference(superposition,[status(thm)],[c_31002,c_34105])).

cnf(c_44083,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_43612,c_31002])).

cnf(c_32,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_61230,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != sK5
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | sK3(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = X0
    | sK3(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_8181,c_32])).

cnf(c_31,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_570,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12829,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_43609,plain,
    ( sK2(sK5) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1082,c_34105])).

cnf(c_43900,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_43609,c_1082])).

cnf(c_4176,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_14491,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4176])).

cnf(c_60487,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14491])).

cnf(c_62418,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_61230,c_32,c_31,c_12829,c_34245,c_43900,c_60487])).

cnf(c_66831,plain,
    ( ~ r2_hidden(sK2(sK6),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK2(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_66833,plain,
    ( ~ r2_hidden(sK2(sK6),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK2(sK6) = sK4 ),
    inference(instantiation,[status(thm)],[c_66831])).

cnf(c_84487,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_61217,c_32,c_31,c_30,c_41,c_44,c_1130,c_1183,c_1495,c_2135,c_5359,c_7200,c_12829,c_13134,c_34245,c_41278,c_42351,c_43900,c_44083,c_60487,c_66833])).

cnf(c_1118,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_22,c_1])).

cnf(c_2476,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_1118,c_1945])).

cnf(c_7520,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = X3 ),
    inference(superposition,[status(thm)],[c_22,c_2476])).

cnf(c_84894,plain,
    ( k5_xboole_0(k5_xboole_0(sK6,k5_xboole_0(X0,sK5)),k5_xboole_0(X0,k1_xboole_0)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_84487,c_7520])).

cnf(c_84903,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_xboole_0(k5_xboole_0(sK6,k5_xboole_0(X0,sK5)),X0) ),
    inference(light_normalisation,[status(thm)],[c_84894,c_1093])).

cnf(c_1119,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_22,c_1])).

cnf(c_2098,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1945,c_1945])).

cnf(c_2811,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_1119,c_2098])).

cnf(c_84904,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_xboole_0(sK5,sK6) ),
    inference(demodulation,[status(thm)],[c_84903,c_2811])).

cnf(c_34503,plain,
    ( r2_hidden(X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_1086])).

cnf(c_84542,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_84487,c_34503])).

cnf(c_1321,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1730,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_1900,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2276,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4,sK5)
    | sK5 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_41882,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK4,sK5)
    | sK5 != sK5
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2276])).

cnf(c_41883,plain,
    ( sK5 != sK5
    | sK4 != X0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41882])).

cnf(c_86148,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_84542,c_32,c_31,c_30,c_41,c_44,c_1130,c_1183,c_1495,c_1730,c_1900,c_2135,c_5359,c_7200,c_12829,c_13134,c_34105,c_34245,c_41278,c_41883,c_42351,c_43900,c_60487,c_66833])).

cnf(c_86161,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_43900,c_86148])).

cnf(c_93916,plain,
    ( k5_xboole_0(sK6,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK5,sK6))) = X0
    | k5_xboole_0(k1_xboole_0,k5_xboole_0(sK6,k5_xboole_0(sK5,sK6))) = X0
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK5,sK6)))),X0) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK5,sK6)))),sK6) != iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK6,k5_xboole_0(sK5,sK6)))),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_81069,c_84904,c_86161])).

cnf(c_2475,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1118,c_1547])).

cnf(c_2458,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1093,c_1118])).

cnf(c_2499,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_22,c_2458])).

cnf(c_6291,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1117,c_2499])).

cnf(c_93917,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k1_xboole_0)),X0) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k1_xboole_0)),sK6) != iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,sK6))),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_93916,c_23,c_1418,c_2475,c_6291,c_86161])).

cnf(c_93918,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(k1_xboole_0,sK6))),k1_xboole_0) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0) = iProver_top
    | r2_hidden(sK1(X0,X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_93917,c_86161])).

cnf(c_93919,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,X0,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK1(X0,X0,k1_xboole_0),sK6) != iProver_top
    | r2_hidden(sK1(X0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_93918,c_1418,c_1945])).

cnf(c_93923,plain,
    ( k5_xboole_0(sK6,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = k1_xboole_0
    | sK6 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK6,k1_xboole_0),sK6) = iProver_top
    | r2_hidden(sK1(sK6,sK6,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_93919])).

cnf(c_93927,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK6,k1_xboole_0),sK6) = iProver_top
    | r2_hidden(sK1(sK6,sK6,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_93923,c_12,c_1547])).

cnf(c_1565,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_2415,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_58147,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2415])).

cnf(c_93979,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_93927,c_32,c_31,c_41,c_44,c_1130,c_1183,c_1495,c_2135,c_5359,c_7200,c_12829,c_13134,c_34245,c_41278,c_42351,c_43900,c_58147,c_60487,c_66833])).

cnf(c_94053,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_93979,c_30])).

cnf(c_94054,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_94053])).

cnf(c_94055,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_94054,c_84904,c_86161,c_93979])).

cnf(c_94056,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_94055,c_1418])).

cnf(c_94057,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_94056])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:05:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.71/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.71/3.98  
% 27.71/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.71/3.98  
% 27.71/3.98  ------  iProver source info
% 27.71/3.98  
% 27.71/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.71/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.71/3.98  git: non_committed_changes: false
% 27.71/3.98  git: last_make_outside_of_git: false
% 27.71/3.98  
% 27.71/3.98  ------ 
% 27.71/3.98  
% 27.71/3.98  ------ Input Options
% 27.71/3.98  
% 27.71/3.98  --out_options                           all
% 27.71/3.98  --tptp_safe_out                         true
% 27.71/3.98  --problem_path                          ""
% 27.71/3.98  --include_path                          ""
% 27.71/3.98  --clausifier                            res/vclausify_rel
% 27.71/3.98  --clausifier_options                    ""
% 27.71/3.98  --stdin                                 false
% 27.71/3.98  --stats_out                             all
% 27.71/3.98  
% 27.71/3.98  ------ General Options
% 27.71/3.98  
% 27.71/3.98  --fof                                   false
% 27.71/3.98  --time_out_real                         305.
% 27.71/3.98  --time_out_virtual                      -1.
% 27.71/3.98  --symbol_type_check                     false
% 27.71/3.98  --clausify_out                          false
% 27.71/3.98  --sig_cnt_out                           false
% 27.71/3.98  --trig_cnt_out                          false
% 27.71/3.98  --trig_cnt_out_tolerance                1.
% 27.71/3.98  --trig_cnt_out_sk_spl                   false
% 27.71/3.98  --abstr_cl_out                          false
% 27.71/3.98  
% 27.71/3.98  ------ Global Options
% 27.71/3.98  
% 27.71/3.98  --schedule                              default
% 27.71/3.98  --add_important_lit                     false
% 27.71/3.98  --prop_solver_per_cl                    1000
% 27.71/3.98  --min_unsat_core                        false
% 27.71/3.98  --soft_assumptions                      false
% 27.71/3.98  --soft_lemma_size                       3
% 27.71/3.98  --prop_impl_unit_size                   0
% 27.71/3.98  --prop_impl_unit                        []
% 27.71/3.98  --share_sel_clauses                     true
% 27.71/3.98  --reset_solvers                         false
% 27.71/3.98  --bc_imp_inh                            [conj_cone]
% 27.71/3.98  --conj_cone_tolerance                   3.
% 27.71/3.98  --extra_neg_conj                        none
% 27.71/3.98  --large_theory_mode                     true
% 27.71/3.98  --prolific_symb_bound                   200
% 27.71/3.98  --lt_threshold                          2000
% 27.71/3.98  --clause_weak_htbl                      true
% 27.71/3.98  --gc_record_bc_elim                     false
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing Options
% 27.71/3.98  
% 27.71/3.98  --preprocessing_flag                    true
% 27.71/3.98  --time_out_prep_mult                    0.1
% 27.71/3.98  --splitting_mode                        input
% 27.71/3.98  --splitting_grd                         true
% 27.71/3.98  --splitting_cvd                         false
% 27.71/3.98  --splitting_cvd_svl                     false
% 27.71/3.98  --splitting_nvd                         32
% 27.71/3.98  --sub_typing                            true
% 27.71/3.98  --prep_gs_sim                           true
% 27.71/3.98  --prep_unflatten                        true
% 27.71/3.98  --prep_res_sim                          true
% 27.71/3.98  --prep_upred                            true
% 27.71/3.98  --prep_sem_filter                       exhaustive
% 27.71/3.98  --prep_sem_filter_out                   false
% 27.71/3.98  --pred_elim                             true
% 27.71/3.98  --res_sim_input                         true
% 27.71/3.98  --eq_ax_congr_red                       true
% 27.71/3.98  --pure_diseq_elim                       true
% 27.71/3.98  --brand_transform                       false
% 27.71/3.98  --non_eq_to_eq                          false
% 27.71/3.98  --prep_def_merge                        true
% 27.71/3.98  --prep_def_merge_prop_impl              false
% 27.71/3.98  --prep_def_merge_mbd                    true
% 27.71/3.98  --prep_def_merge_tr_red                 false
% 27.71/3.98  --prep_def_merge_tr_cl                  false
% 27.71/3.98  --smt_preprocessing                     true
% 27.71/3.98  --smt_ac_axioms                         fast
% 27.71/3.98  --preprocessed_out                      false
% 27.71/3.98  --preprocessed_stats                    false
% 27.71/3.98  
% 27.71/3.98  ------ Abstraction refinement Options
% 27.71/3.98  
% 27.71/3.98  --abstr_ref                             []
% 27.71/3.98  --abstr_ref_prep                        false
% 27.71/3.98  --abstr_ref_until_sat                   false
% 27.71/3.98  --abstr_ref_sig_restrict                funpre
% 27.71/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.71/3.98  --abstr_ref_under                       []
% 27.71/3.98  
% 27.71/3.98  ------ SAT Options
% 27.71/3.98  
% 27.71/3.98  --sat_mode                              false
% 27.71/3.98  --sat_fm_restart_options                ""
% 27.71/3.98  --sat_gr_def                            false
% 27.71/3.98  --sat_epr_types                         true
% 27.71/3.98  --sat_non_cyclic_types                  false
% 27.71/3.98  --sat_finite_models                     false
% 27.71/3.98  --sat_fm_lemmas                         false
% 27.71/3.98  --sat_fm_prep                           false
% 27.71/3.98  --sat_fm_uc_incr                        true
% 27.71/3.98  --sat_out_model                         small
% 27.71/3.98  --sat_out_clauses                       false
% 27.71/3.98  
% 27.71/3.98  ------ QBF Options
% 27.71/3.98  
% 27.71/3.98  --qbf_mode                              false
% 27.71/3.98  --qbf_elim_univ                         false
% 27.71/3.98  --qbf_dom_inst                          none
% 27.71/3.98  --qbf_dom_pre_inst                      false
% 27.71/3.98  --qbf_sk_in                             false
% 27.71/3.98  --qbf_pred_elim                         true
% 27.71/3.98  --qbf_split                             512
% 27.71/3.98  
% 27.71/3.98  ------ BMC1 Options
% 27.71/3.98  
% 27.71/3.98  --bmc1_incremental                      false
% 27.71/3.98  --bmc1_axioms                           reachable_all
% 27.71/3.98  --bmc1_min_bound                        0
% 27.71/3.98  --bmc1_max_bound                        -1
% 27.71/3.98  --bmc1_max_bound_default                -1
% 27.71/3.98  --bmc1_symbol_reachability              true
% 27.71/3.98  --bmc1_property_lemmas                  false
% 27.71/3.98  --bmc1_k_induction                      false
% 27.71/3.98  --bmc1_non_equiv_states                 false
% 27.71/3.98  --bmc1_deadlock                         false
% 27.71/3.98  --bmc1_ucm                              false
% 27.71/3.98  --bmc1_add_unsat_core                   none
% 27.71/3.98  --bmc1_unsat_core_children              false
% 27.71/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.71/3.98  --bmc1_out_stat                         full
% 27.71/3.98  --bmc1_ground_init                      false
% 27.71/3.98  --bmc1_pre_inst_next_state              false
% 27.71/3.98  --bmc1_pre_inst_state                   false
% 27.71/3.98  --bmc1_pre_inst_reach_state             false
% 27.71/3.98  --bmc1_out_unsat_core                   false
% 27.71/3.98  --bmc1_aig_witness_out                  false
% 27.71/3.98  --bmc1_verbose                          false
% 27.71/3.98  --bmc1_dump_clauses_tptp                false
% 27.71/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.71/3.98  --bmc1_dump_file                        -
% 27.71/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.71/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.71/3.98  --bmc1_ucm_extend_mode                  1
% 27.71/3.98  --bmc1_ucm_init_mode                    2
% 27.71/3.98  --bmc1_ucm_cone_mode                    none
% 27.71/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.71/3.98  --bmc1_ucm_relax_model                  4
% 27.71/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.71/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.71/3.98  --bmc1_ucm_layered_model                none
% 27.71/3.98  --bmc1_ucm_max_lemma_size               10
% 27.71/3.98  
% 27.71/3.98  ------ AIG Options
% 27.71/3.98  
% 27.71/3.98  --aig_mode                              false
% 27.71/3.98  
% 27.71/3.98  ------ Instantiation Options
% 27.71/3.98  
% 27.71/3.98  --instantiation_flag                    true
% 27.71/3.98  --inst_sos_flag                         true
% 27.71/3.98  --inst_sos_phase                        true
% 27.71/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.71/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.71/3.98  --inst_lit_sel_side                     num_symb
% 27.71/3.98  --inst_solver_per_active                1400
% 27.71/3.98  --inst_solver_calls_frac                1.
% 27.71/3.98  --inst_passive_queue_type               priority_queues
% 27.71/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.71/3.98  --inst_passive_queues_freq              [25;2]
% 27.71/3.98  --inst_dismatching                      true
% 27.71/3.98  --inst_eager_unprocessed_to_passive     true
% 27.71/3.98  --inst_prop_sim_given                   true
% 27.71/3.98  --inst_prop_sim_new                     false
% 27.71/3.98  --inst_subs_new                         false
% 27.71/3.98  --inst_eq_res_simp                      false
% 27.71/3.98  --inst_subs_given                       false
% 27.71/3.98  --inst_orphan_elimination               true
% 27.71/3.98  --inst_learning_loop_flag               true
% 27.71/3.98  --inst_learning_start                   3000
% 27.71/3.98  --inst_learning_factor                  2
% 27.71/3.98  --inst_start_prop_sim_after_learn       3
% 27.71/3.98  --inst_sel_renew                        solver
% 27.71/3.98  --inst_lit_activity_flag                true
% 27.71/3.98  --inst_restr_to_given                   false
% 27.71/3.98  --inst_activity_threshold               500
% 27.71/3.98  --inst_out_proof                        true
% 27.71/3.98  
% 27.71/3.98  ------ Resolution Options
% 27.71/3.98  
% 27.71/3.98  --resolution_flag                       true
% 27.71/3.98  --res_lit_sel                           adaptive
% 27.71/3.98  --res_lit_sel_side                      none
% 27.71/3.98  --res_ordering                          kbo
% 27.71/3.98  --res_to_prop_solver                    active
% 27.71/3.98  --res_prop_simpl_new                    false
% 27.71/3.98  --res_prop_simpl_given                  true
% 27.71/3.98  --res_passive_queue_type                priority_queues
% 27.71/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.71/3.98  --res_passive_queues_freq               [15;5]
% 27.71/3.98  --res_forward_subs                      full
% 27.71/3.98  --res_backward_subs                     full
% 27.71/3.98  --res_forward_subs_resolution           true
% 27.71/3.98  --res_backward_subs_resolution          true
% 27.71/3.98  --res_orphan_elimination                true
% 27.71/3.98  --res_time_limit                        2.
% 27.71/3.98  --res_out_proof                         true
% 27.71/3.98  
% 27.71/3.98  ------ Superposition Options
% 27.71/3.98  
% 27.71/3.98  --superposition_flag                    true
% 27.71/3.98  --sup_passive_queue_type                priority_queues
% 27.71/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.71/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.71/3.98  --demod_completeness_check              fast
% 27.71/3.98  --demod_use_ground                      true
% 27.71/3.98  --sup_to_prop_solver                    passive
% 27.71/3.98  --sup_prop_simpl_new                    true
% 27.71/3.98  --sup_prop_simpl_given                  true
% 27.71/3.98  --sup_fun_splitting                     true
% 27.71/3.98  --sup_smt_interval                      50000
% 27.71/3.98  
% 27.71/3.98  ------ Superposition Simplification Setup
% 27.71/3.98  
% 27.71/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.71/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.71/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.71/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.71/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.71/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.71/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.71/3.98  --sup_immed_triv                        [TrivRules]
% 27.71/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_immed_bw_main                     []
% 27.71/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.71/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.71/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_input_bw                          []
% 27.71/3.98  
% 27.71/3.98  ------ Combination Options
% 27.71/3.98  
% 27.71/3.98  --comb_res_mult                         3
% 27.71/3.98  --comb_sup_mult                         2
% 27.71/3.98  --comb_inst_mult                        10
% 27.71/3.98  
% 27.71/3.98  ------ Debug Options
% 27.71/3.98  
% 27.71/3.98  --dbg_backtrace                         false
% 27.71/3.98  --dbg_dump_prop_clauses                 false
% 27.71/3.98  --dbg_dump_prop_clauses_file            -
% 27.71/3.98  --dbg_out_stat                          false
% 27.71/3.98  ------ Parsing...
% 27.71/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.71/3.98  ------ Proving...
% 27.71/3.98  ------ Problem Properties 
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  clauses                                 33
% 27.71/3.98  conjectures                             4
% 27.71/3.98  EPR                                     4
% 27.71/3.98  Horn                                    27
% 27.71/3.98  unary                                   11
% 27.71/3.98  binary                                  13
% 27.71/3.98  lits                                    65
% 27.71/3.98  lits eq                                 27
% 27.71/3.98  fd_pure                                 0
% 27.71/3.98  fd_pseudo                               0
% 27.71/3.98  fd_cond                                 1
% 27.71/3.98  fd_pseudo_cond                          7
% 27.71/3.98  AC symbols                              1
% 27.71/3.98  
% 27.71/3.98  ------ Schedule dynamic 5 is on 
% 27.71/3.98  
% 27.71/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  ------ 
% 27.71/3.98  Current options:
% 27.71/3.98  ------ 
% 27.71/3.98  
% 27.71/3.98  ------ Input Options
% 27.71/3.98  
% 27.71/3.98  --out_options                           all
% 27.71/3.98  --tptp_safe_out                         true
% 27.71/3.98  --problem_path                          ""
% 27.71/3.98  --include_path                          ""
% 27.71/3.98  --clausifier                            res/vclausify_rel
% 27.71/3.98  --clausifier_options                    ""
% 27.71/3.98  --stdin                                 false
% 27.71/3.98  --stats_out                             all
% 27.71/3.98  
% 27.71/3.98  ------ General Options
% 27.71/3.98  
% 27.71/3.98  --fof                                   false
% 27.71/3.98  --time_out_real                         305.
% 27.71/3.98  --time_out_virtual                      -1.
% 27.71/3.98  --symbol_type_check                     false
% 27.71/3.98  --clausify_out                          false
% 27.71/3.98  --sig_cnt_out                           false
% 27.71/3.98  --trig_cnt_out                          false
% 27.71/3.98  --trig_cnt_out_tolerance                1.
% 27.71/3.98  --trig_cnt_out_sk_spl                   false
% 27.71/3.98  --abstr_cl_out                          false
% 27.71/3.98  
% 27.71/3.98  ------ Global Options
% 27.71/3.98  
% 27.71/3.98  --schedule                              default
% 27.71/3.98  --add_important_lit                     false
% 27.71/3.98  --prop_solver_per_cl                    1000
% 27.71/3.98  --min_unsat_core                        false
% 27.71/3.98  --soft_assumptions                      false
% 27.71/3.98  --soft_lemma_size                       3
% 27.71/3.98  --prop_impl_unit_size                   0
% 27.71/3.98  --prop_impl_unit                        []
% 27.71/3.98  --share_sel_clauses                     true
% 27.71/3.98  --reset_solvers                         false
% 27.71/3.98  --bc_imp_inh                            [conj_cone]
% 27.71/3.98  --conj_cone_tolerance                   3.
% 27.71/3.98  --extra_neg_conj                        none
% 27.71/3.98  --large_theory_mode                     true
% 27.71/3.98  --prolific_symb_bound                   200
% 27.71/3.98  --lt_threshold                          2000
% 27.71/3.98  --clause_weak_htbl                      true
% 27.71/3.98  --gc_record_bc_elim                     false
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing Options
% 27.71/3.98  
% 27.71/3.98  --preprocessing_flag                    true
% 27.71/3.98  --time_out_prep_mult                    0.1
% 27.71/3.98  --splitting_mode                        input
% 27.71/3.98  --splitting_grd                         true
% 27.71/3.98  --splitting_cvd                         false
% 27.71/3.98  --splitting_cvd_svl                     false
% 27.71/3.98  --splitting_nvd                         32
% 27.71/3.98  --sub_typing                            true
% 27.71/3.98  --prep_gs_sim                           true
% 27.71/3.98  --prep_unflatten                        true
% 27.71/3.98  --prep_res_sim                          true
% 27.71/3.98  --prep_upred                            true
% 27.71/3.98  --prep_sem_filter                       exhaustive
% 27.71/3.98  --prep_sem_filter_out                   false
% 27.71/3.98  --pred_elim                             true
% 27.71/3.98  --res_sim_input                         true
% 27.71/3.98  --eq_ax_congr_red                       true
% 27.71/3.98  --pure_diseq_elim                       true
% 27.71/3.98  --brand_transform                       false
% 27.71/3.98  --non_eq_to_eq                          false
% 27.71/3.98  --prep_def_merge                        true
% 27.71/3.98  --prep_def_merge_prop_impl              false
% 27.71/3.98  --prep_def_merge_mbd                    true
% 27.71/3.98  --prep_def_merge_tr_red                 false
% 27.71/3.98  --prep_def_merge_tr_cl                  false
% 27.71/3.98  --smt_preprocessing                     true
% 27.71/3.98  --smt_ac_axioms                         fast
% 27.71/3.98  --preprocessed_out                      false
% 27.71/3.98  --preprocessed_stats                    false
% 27.71/3.98  
% 27.71/3.98  ------ Abstraction refinement Options
% 27.71/3.98  
% 27.71/3.98  --abstr_ref                             []
% 27.71/3.98  --abstr_ref_prep                        false
% 27.71/3.98  --abstr_ref_until_sat                   false
% 27.71/3.98  --abstr_ref_sig_restrict                funpre
% 27.71/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.71/3.98  --abstr_ref_under                       []
% 27.71/3.98  
% 27.71/3.98  ------ SAT Options
% 27.71/3.98  
% 27.71/3.98  --sat_mode                              false
% 27.71/3.98  --sat_fm_restart_options                ""
% 27.71/3.98  --sat_gr_def                            false
% 27.71/3.98  --sat_epr_types                         true
% 27.71/3.98  --sat_non_cyclic_types                  false
% 27.71/3.98  --sat_finite_models                     false
% 27.71/3.98  --sat_fm_lemmas                         false
% 27.71/3.98  --sat_fm_prep                           false
% 27.71/3.98  --sat_fm_uc_incr                        true
% 27.71/3.98  --sat_out_model                         small
% 27.71/3.98  --sat_out_clauses                       false
% 27.71/3.98  
% 27.71/3.98  ------ QBF Options
% 27.71/3.98  
% 27.71/3.98  --qbf_mode                              false
% 27.71/3.98  --qbf_elim_univ                         false
% 27.71/3.98  --qbf_dom_inst                          none
% 27.71/3.98  --qbf_dom_pre_inst                      false
% 27.71/3.98  --qbf_sk_in                             false
% 27.71/3.98  --qbf_pred_elim                         true
% 27.71/3.98  --qbf_split                             512
% 27.71/3.98  
% 27.71/3.98  ------ BMC1 Options
% 27.71/3.98  
% 27.71/3.98  --bmc1_incremental                      false
% 27.71/3.98  --bmc1_axioms                           reachable_all
% 27.71/3.98  --bmc1_min_bound                        0
% 27.71/3.98  --bmc1_max_bound                        -1
% 27.71/3.98  --bmc1_max_bound_default                -1
% 27.71/3.98  --bmc1_symbol_reachability              true
% 27.71/3.98  --bmc1_property_lemmas                  false
% 27.71/3.98  --bmc1_k_induction                      false
% 27.71/3.98  --bmc1_non_equiv_states                 false
% 27.71/3.98  --bmc1_deadlock                         false
% 27.71/3.98  --bmc1_ucm                              false
% 27.71/3.98  --bmc1_add_unsat_core                   none
% 27.71/3.98  --bmc1_unsat_core_children              false
% 27.71/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.71/3.98  --bmc1_out_stat                         full
% 27.71/3.98  --bmc1_ground_init                      false
% 27.71/3.98  --bmc1_pre_inst_next_state              false
% 27.71/3.98  --bmc1_pre_inst_state                   false
% 27.71/3.98  --bmc1_pre_inst_reach_state             false
% 27.71/3.98  --bmc1_out_unsat_core                   false
% 27.71/3.98  --bmc1_aig_witness_out                  false
% 27.71/3.98  --bmc1_verbose                          false
% 27.71/3.98  --bmc1_dump_clauses_tptp                false
% 27.71/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.71/3.98  --bmc1_dump_file                        -
% 27.71/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.71/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.71/3.98  --bmc1_ucm_extend_mode                  1
% 27.71/3.98  --bmc1_ucm_init_mode                    2
% 27.71/3.98  --bmc1_ucm_cone_mode                    none
% 27.71/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.71/3.98  --bmc1_ucm_relax_model                  4
% 27.71/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.71/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.71/3.98  --bmc1_ucm_layered_model                none
% 27.71/3.98  --bmc1_ucm_max_lemma_size               10
% 27.71/3.98  
% 27.71/3.98  ------ AIG Options
% 27.71/3.98  
% 27.71/3.98  --aig_mode                              false
% 27.71/3.98  
% 27.71/3.98  ------ Instantiation Options
% 27.71/3.98  
% 27.71/3.98  --instantiation_flag                    true
% 27.71/3.98  --inst_sos_flag                         true
% 27.71/3.98  --inst_sos_phase                        true
% 27.71/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.71/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.71/3.98  --inst_lit_sel_side                     none
% 27.71/3.98  --inst_solver_per_active                1400
% 27.71/3.98  --inst_solver_calls_frac                1.
% 27.71/3.98  --inst_passive_queue_type               priority_queues
% 27.71/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.71/3.98  --inst_passive_queues_freq              [25;2]
% 27.71/3.98  --inst_dismatching                      true
% 27.71/3.98  --inst_eager_unprocessed_to_passive     true
% 27.71/3.98  --inst_prop_sim_given                   true
% 27.71/3.98  --inst_prop_sim_new                     false
% 27.71/3.98  --inst_subs_new                         false
% 27.71/3.98  --inst_eq_res_simp                      false
% 27.71/3.98  --inst_subs_given                       false
% 27.71/3.98  --inst_orphan_elimination               true
% 27.71/3.98  --inst_learning_loop_flag               true
% 27.71/3.98  --inst_learning_start                   3000
% 27.71/3.98  --inst_learning_factor                  2
% 27.71/3.98  --inst_start_prop_sim_after_learn       3
% 27.71/3.98  --inst_sel_renew                        solver
% 27.71/3.98  --inst_lit_activity_flag                true
% 27.71/3.98  --inst_restr_to_given                   false
% 27.71/3.98  --inst_activity_threshold               500
% 27.71/3.98  --inst_out_proof                        true
% 27.71/3.98  
% 27.71/3.98  ------ Resolution Options
% 27.71/3.98  
% 27.71/3.98  --resolution_flag                       false
% 27.71/3.98  --res_lit_sel                           adaptive
% 27.71/3.98  --res_lit_sel_side                      none
% 27.71/3.98  --res_ordering                          kbo
% 27.71/3.98  --res_to_prop_solver                    active
% 27.71/3.98  --res_prop_simpl_new                    false
% 27.71/3.98  --res_prop_simpl_given                  true
% 27.71/3.98  --res_passive_queue_type                priority_queues
% 27.71/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.71/3.98  --res_passive_queues_freq               [15;5]
% 27.71/3.98  --res_forward_subs                      full
% 27.71/3.98  --res_backward_subs                     full
% 27.71/3.98  --res_forward_subs_resolution           true
% 27.71/3.98  --res_backward_subs_resolution          true
% 27.71/3.98  --res_orphan_elimination                true
% 27.71/3.98  --res_time_limit                        2.
% 27.71/3.98  --res_out_proof                         true
% 27.71/3.98  
% 27.71/3.98  ------ Superposition Options
% 27.71/3.98  
% 27.71/3.98  --superposition_flag                    true
% 27.71/3.98  --sup_passive_queue_type                priority_queues
% 27.71/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.71/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.71/3.98  --demod_completeness_check              fast
% 27.71/3.98  --demod_use_ground                      true
% 27.71/3.98  --sup_to_prop_solver                    passive
% 27.71/3.98  --sup_prop_simpl_new                    true
% 27.71/3.98  --sup_prop_simpl_given                  true
% 27.71/3.98  --sup_fun_splitting                     true
% 27.71/3.98  --sup_smt_interval                      50000
% 27.71/3.98  
% 27.71/3.98  ------ Superposition Simplification Setup
% 27.71/3.98  
% 27.71/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.71/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.71/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.71/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.71/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.71/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.71/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.71/3.98  --sup_immed_triv                        [TrivRules]
% 27.71/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_immed_bw_main                     []
% 27.71/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.71/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.71/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_input_bw                          []
% 27.71/3.98  
% 27.71/3.98  ------ Combination Options
% 27.71/3.98  
% 27.71/3.98  --comb_res_mult                         3
% 27.71/3.98  --comb_sup_mult                         2
% 27.71/3.98  --comb_inst_mult                        10
% 27.71/3.98  
% 27.71/3.98  ------ Debug Options
% 27.71/3.98  
% 27.71/3.98  --dbg_backtrace                         false
% 27.71/3.98  --dbg_dump_prop_clauses                 false
% 27.71/3.98  --dbg_dump_prop_clauses_file            -
% 27.71/3.98  --dbg_out_stat                          false
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  ------ Proving...
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  % SZS status Theorem for theBenchmark.p
% 27.71/3.98  
% 27.71/3.98   Resolution empty clause
% 27.71/3.98  
% 27.71/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.71/3.98  
% 27.71/3.98  fof(f4,axiom,(
% 27.71/3.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f44,plain,(
% 27.71/3.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.71/3.98    inference(nnf_transformation,[],[f4])).
% 27.71/3.98  
% 27.71/3.98  fof(f45,plain,(
% 27.71/3.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.71/3.98    inference(flattening,[],[f44])).
% 27.71/3.98  
% 27.71/3.98  fof(f46,plain,(
% 27.71/3.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.71/3.98    inference(rectify,[],[f45])).
% 27.71/3.98  
% 27.71/3.98  fof(f47,plain,(
% 27.71/3.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 27.71/3.98    introduced(choice_axiom,[])).
% 27.71/3.98  
% 27.71/3.98  fof(f48,plain,(
% 27.71/3.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 27.71/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 27.71/3.98  
% 27.71/3.98  fof(f69,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f48])).
% 27.71/3.98  
% 27.71/3.98  fof(f17,axiom,(
% 27.71/3.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f85,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f17])).
% 27.71/3.98  
% 27.71/3.98  fof(f27,axiom,(
% 27.71/3.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f99,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 27.71/3.98    inference(cnf_transformation,[],[f27])).
% 27.71/3.98  
% 27.71/3.98  fof(f20,axiom,(
% 27.71/3.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f91,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f20])).
% 27.71/3.98  
% 27.71/3.98  fof(f21,axiom,(
% 27.71/3.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f92,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f21])).
% 27.71/3.98  
% 27.71/3.98  fof(f22,axiom,(
% 27.71/3.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f93,plain,(
% 27.71/3.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f22])).
% 27.71/3.98  
% 27.71/3.98  fof(f23,axiom,(
% 27.71/3.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f94,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f23])).
% 27.71/3.98  
% 27.71/3.98  fof(f24,axiom,(
% 27.71/3.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f95,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f24])).
% 27.71/3.98  
% 27.71/3.98  fof(f25,axiom,(
% 27.71/3.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f96,plain,(
% 27.71/3.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f25])).
% 27.71/3.98  
% 27.71/3.98  fof(f104,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f95,f96])).
% 27.71/3.98  
% 27.71/3.98  fof(f105,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f94,f104])).
% 27.71/3.98  
% 27.71/3.98  fof(f106,plain,(
% 27.71/3.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f93,f105])).
% 27.71/3.98  
% 27.71/3.98  fof(f107,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f92,f106])).
% 27.71/3.98  
% 27.71/3.98  fof(f108,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f91,f107])).
% 27.71/3.98  
% 27.71/3.98  fof(f109,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f99,f108])).
% 27.71/3.98  
% 27.71/3.98  fof(f110,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f85,f109])).
% 27.71/3.98  
% 27.71/3.98  fof(f115,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f69,f110])).
% 27.71/3.98  
% 27.71/3.98  fof(f15,axiom,(
% 27.71/3.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f83,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f15])).
% 27.71/3.98  
% 27.71/3.98  fof(f2,axiom,(
% 27.71/3.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f61,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f2])).
% 27.71/3.98  
% 27.71/3.98  fof(f28,conjecture,(
% 27.71/3.98    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f29,negated_conjecture,(
% 27.71/3.98    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 27.71/3.98    inference(negated_conjecture,[],[f28])).
% 27.71/3.98  
% 27.71/3.98  fof(f39,plain,(
% 27.71/3.98    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 27.71/3.98    inference(ennf_transformation,[],[f29])).
% 27.71/3.98  
% 27.71/3.98  fof(f58,plain,(
% 27.71/3.98    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 27.71/3.98    introduced(choice_axiom,[])).
% 27.71/3.98  
% 27.71/3.98  fof(f59,plain,(
% 27.71/3.98    (k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 27.71/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f58])).
% 27.71/3.98  
% 27.71/3.98  fof(f100,plain,(
% 27.71/3.98    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 27.71/3.98    inference(cnf_transformation,[],[f59])).
% 27.71/3.98  
% 27.71/3.98  fof(f19,axiom,(
% 27.71/3.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f90,plain,(
% 27.71/3.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f19])).
% 27.71/3.98  
% 27.71/3.98  fof(f112,plain,(
% 27.71/3.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f90,f108])).
% 27.71/3.98  
% 27.71/3.98  fof(f135,plain,(
% 27.71/3.98    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 27.71/3.98    inference(definition_unfolding,[],[f100,f109,f112])).
% 27.71/3.98  
% 27.71/3.98  fof(f65,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 27.71/3.98    inference(cnf_transformation,[],[f48])).
% 27.71/3.98  
% 27.71/3.98  fof(f119,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 27.71/3.98    inference(definition_unfolding,[],[f65,f110])).
% 27.71/3.98  
% 27.71/3.98  fof(f138,plain,(
% 27.71/3.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 27.71/3.98    inference(equality_resolution,[],[f119])).
% 27.71/3.98  
% 27.71/3.98  fof(f67,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 27.71/3.98    inference(cnf_transformation,[],[f48])).
% 27.71/3.98  
% 27.71/3.98  fof(f117,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 27.71/3.98    inference(definition_unfolding,[],[f67,f110])).
% 27.71/3.98  
% 27.71/3.98  fof(f136,plain,(
% 27.71/3.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 27.71/3.98    inference(equality_resolution,[],[f117])).
% 27.71/3.98  
% 27.71/3.98  fof(f70,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f48])).
% 27.71/3.98  
% 27.71/3.98  fof(f114,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f70,f110])).
% 27.71/3.98  
% 27.71/3.98  fof(f6,axiom,(
% 27.71/3.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f30,plain,(
% 27.71/3.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 27.71/3.98    inference(rectify,[],[f6])).
% 27.71/3.98  
% 27.71/3.98  fof(f72,plain,(
% 27.71/3.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 27.71/3.98    inference(cnf_transformation,[],[f30])).
% 27.71/3.98  
% 27.71/3.98  fof(f120,plain,(
% 27.71/3.98    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 27.71/3.98    inference(definition_unfolding,[],[f72,f109])).
% 27.71/3.98  
% 27.71/3.98  fof(f16,axiom,(
% 27.71/3.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f84,plain,(
% 27.71/3.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 27.71/3.98    inference(cnf_transformation,[],[f16])).
% 27.71/3.98  
% 27.71/3.98  fof(f7,axiom,(
% 27.71/3.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f31,plain,(
% 27.71/3.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 27.71/3.98    inference(rectify,[],[f7])).
% 27.71/3.98  
% 27.71/3.98  fof(f73,plain,(
% 27.71/3.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 27.71/3.98    inference(cnf_transformation,[],[f31])).
% 27.71/3.98  
% 27.71/3.98  fof(f121,plain,(
% 27.71/3.98    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 27.71/3.98    inference(definition_unfolding,[],[f73,f110])).
% 27.71/3.98  
% 27.71/3.98  fof(f18,axiom,(
% 27.71/3.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f53,plain,(
% 27.71/3.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 27.71/3.98    inference(nnf_transformation,[],[f18])).
% 27.71/3.98  
% 27.71/3.98  fof(f54,plain,(
% 27.71/3.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 27.71/3.98    inference(rectify,[],[f53])).
% 27.71/3.98  
% 27.71/3.98  fof(f55,plain,(
% 27.71/3.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 27.71/3.98    introduced(choice_axiom,[])).
% 27.71/3.98  
% 27.71/3.98  fof(f56,plain,(
% 27.71/3.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 27.71/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).
% 27.71/3.98  
% 27.71/3.98  fof(f88,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f56])).
% 27.71/3.98  
% 27.71/3.98  fof(f127,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f88,f112])).
% 27.71/3.98  
% 27.71/3.98  fof(f86,plain,(
% 27.71/3.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 27.71/3.98    inference(cnf_transformation,[],[f56])).
% 27.71/3.98  
% 27.71/3.98  fof(f129,plain,(
% 27.71/3.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 27.71/3.98    inference(definition_unfolding,[],[f86,f112])).
% 27.71/3.98  
% 27.71/3.98  fof(f143,plain,(
% 27.71/3.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 27.71/3.98    inference(equality_resolution,[],[f129])).
% 27.71/3.98  
% 27.71/3.98  fof(f8,axiom,(
% 27.71/3.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f36,plain,(
% 27.71/3.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 27.71/3.98    inference(ennf_transformation,[],[f8])).
% 27.71/3.98  
% 27.71/3.98  fof(f49,plain,(
% 27.71/3.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 27.71/3.98    introduced(choice_axiom,[])).
% 27.71/3.98  
% 27.71/3.98  fof(f50,plain,(
% 27.71/3.98    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 27.71/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f49])).
% 27.71/3.98  
% 27.71/3.98  fof(f74,plain,(
% 27.71/3.98    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 27.71/3.98    inference(cnf_transformation,[],[f50])).
% 27.71/3.98  
% 27.71/3.98  fof(f103,plain,(
% 27.71/3.98    k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5),
% 27.71/3.98    inference(cnf_transformation,[],[f59])).
% 27.71/3.98  
% 27.71/3.98  fof(f132,plain,(
% 27.71/3.98    k1_xboole_0 != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 27.71/3.98    inference(definition_unfolding,[],[f103,f112])).
% 27.71/3.98  
% 27.71/3.98  fof(f87,plain,(
% 27.71/3.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 27.71/3.98    inference(cnf_transformation,[],[f56])).
% 27.71/3.98  
% 27.71/3.98  fof(f128,plain,(
% 27.71/3.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 27.71/3.98    inference(definition_unfolding,[],[f87,f112])).
% 27.71/3.98  
% 27.71/3.98  fof(f141,plain,(
% 27.71/3.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 27.71/3.98    inference(equality_resolution,[],[f128])).
% 27.71/3.98  
% 27.71/3.98  fof(f142,plain,(
% 27.71/3.98    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 27.71/3.98    inference(equality_resolution,[],[f141])).
% 27.71/3.98  
% 27.71/3.98  fof(f9,axiom,(
% 27.71/3.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f51,plain,(
% 27.71/3.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.71/3.98    inference(nnf_transformation,[],[f9])).
% 27.71/3.98  
% 27.71/3.98  fof(f52,plain,(
% 27.71/3.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.71/3.98    inference(flattening,[],[f51])).
% 27.71/3.98  
% 27.71/3.98  fof(f77,plain,(
% 27.71/3.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f52])).
% 27.71/3.98  
% 27.71/3.98  fof(f26,axiom,(
% 27.71/3.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f57,plain,(
% 27.71/3.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 27.71/3.98    inference(nnf_transformation,[],[f26])).
% 27.71/3.98  
% 27.71/3.98  fof(f98,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f57])).
% 27.71/3.98  
% 27.71/3.98  fof(f130,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 27.71/3.98    inference(definition_unfolding,[],[f98,f112])).
% 27.71/3.98  
% 27.71/3.98  fof(f75,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.71/3.98    inference(cnf_transformation,[],[f52])).
% 27.71/3.98  
% 27.71/3.98  fof(f140,plain,(
% 27.71/3.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.71/3.98    inference(equality_resolution,[],[f75])).
% 27.71/3.98  
% 27.71/3.98  fof(f1,axiom,(
% 27.71/3.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f60,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f1])).
% 27.71/3.98  
% 27.71/3.98  fof(f113,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f60,f109,f109])).
% 27.71/3.98  
% 27.71/3.98  fof(f13,axiom,(
% 27.71/3.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f81,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 27.71/3.98    inference(cnf_transformation,[],[f13])).
% 27.71/3.98  
% 27.71/3.98  fof(f124,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f81,f109,f109,f109])).
% 27.71/3.98  
% 27.71/3.98  fof(f14,axiom,(
% 27.71/3.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f82,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.71/3.98    inference(cnf_transformation,[],[f14])).
% 27.71/3.98  
% 27.71/3.98  fof(f125,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f82,f109])).
% 27.71/3.98  
% 27.71/3.98  fof(f3,axiom,(
% 27.71/3.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f33,plain,(
% 27.71/3.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 27.71/3.98    inference(ennf_transformation,[],[f3])).
% 27.71/3.98  
% 27.71/3.98  fof(f40,plain,(
% 27.71/3.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 27.71/3.98    inference(nnf_transformation,[],[f33])).
% 27.71/3.98  
% 27.71/3.98  fof(f41,plain,(
% 27.71/3.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.71/3.98    inference(rectify,[],[f40])).
% 27.71/3.98  
% 27.71/3.98  fof(f42,plain,(
% 27.71/3.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 27.71/3.98    introduced(choice_axiom,[])).
% 27.71/3.98  
% 27.71/3.98  fof(f43,plain,(
% 27.71/3.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.71/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 27.71/3.98  
% 27.71/3.98  fof(f62,plain,(
% 27.71/3.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f43])).
% 27.71/3.98  
% 27.71/3.98  fof(f66,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 27.71/3.98    inference(cnf_transformation,[],[f48])).
% 27.71/3.98  
% 27.71/3.98  fof(f118,plain,(
% 27.71/3.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 27.71/3.98    inference(definition_unfolding,[],[f66,f110])).
% 27.71/3.98  
% 27.71/3.98  fof(f137,plain,(
% 27.71/3.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 27.71/3.98    inference(equality_resolution,[],[f118])).
% 27.71/3.98  
% 27.71/3.98  fof(f101,plain,(
% 27.71/3.98    k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5),
% 27.71/3.98    inference(cnf_transformation,[],[f59])).
% 27.71/3.98  
% 27.71/3.98  fof(f134,plain,(
% 27.71/3.98    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 27.71/3.98    inference(definition_unfolding,[],[f101,f112,f112])).
% 27.71/3.98  
% 27.71/3.98  fof(f102,plain,(
% 27.71/3.98    k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5),
% 27.71/3.98    inference(cnf_transformation,[],[f59])).
% 27.71/3.98  
% 27.71/3.98  fof(f133,plain,(
% 27.71/3.98    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k1_xboole_0 != sK5),
% 27.71/3.98    inference(definition_unfolding,[],[f102,f112])).
% 27.71/3.98  
% 27.71/3.98  cnf(c_6,plain,
% 27.71/3.98      ( r2_hidden(sK1(X0,X1,X2),X1)
% 27.71/3.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 27.71/3.98      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
% 27.71/3.98      inference(cnf_transformation,[],[f115]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_22,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 27.71/3.98      inference(cnf_transformation,[],[f83]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1,plain,
% 27.71/3.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 27.71/3.98      inference(cnf_transformation,[],[f61]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_567,plain,
% 27.71/3.98      ( r2_hidden(sK1(X0,X1,X2),X1)
% 27.71/3.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 27.71/3.98      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2 ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_6,c_22,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1088,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2
% 27.71/3.98      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1117,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_22,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_33,negated_conjecture,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 27.71/3.98      inference(cnf_transformation,[],[f135]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_10,plain,
% 27.71/3.98      ( r2_hidden(X0,X1)
% 27.71/3.98      | ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 27.71/3.98      inference(cnf_transformation,[],[f138]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_563,plain,
% 27.71/3.98      ( r2_hidden(X0,X1)
% 27.71/3.98      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_10,c_22,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1084,plain,
% 27.71/3.98      ( r2_hidden(X0,X1) = iProver_top
% 27.71/3.98      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) != iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_26756,plain,
% 27.71/3.98      ( r2_hidden(X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
% 27.71/3.98      | r2_hidden(X0,sK5) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_33,c_1084]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_31005,plain,
% 27.71/3.98      ( r2_hidden(X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
% 27.71/3.98      | r2_hidden(X0,sK5) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1117,c_26756]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_41343,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 27.71/3.98      | r2_hidden(sK1(X0,X1,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X1) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X1,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1088,c_31005]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_41342,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 27.71/3.98      | r2_hidden(sK1(X0,X1,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X1) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X1,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1088,c_26756]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_41666,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 27.71/3.98      | r2_hidden(sK1(X0,X1,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X1,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X1) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1117,c_41342]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_8,plain,
% 27.71/3.98      ( ~ r2_hidden(X0,X1)
% 27.71/3.98      | ~ r2_hidden(X0,X2)
% 27.71/3.98      | r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
% 27.71/3.98      inference(cnf_transformation,[],[f136]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_565,plain,
% 27.71/3.98      ( ~ r2_hidden(X0,X1)
% 27.71/3.98      | ~ r2_hidden(X0,X2)
% 27.71/3.98      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_8,c_22,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1086,plain,
% 27.71/3.98      ( r2_hidden(X0,X1) != iProver_top
% 27.71/3.98      | r2_hidden(X0,X2) != iProver_top
% 27.71/3.98      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_34502,plain,
% 27.71/3.98      ( r2_hidden(X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
% 27.71/3.98      | r2_hidden(X0,sK5) != iProver_top
% 27.71/3.98      | r2_hidden(X0,sK6) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_33,c_1086]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_5,plain,
% 27.71/3.98      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 27.71/3.98      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 27.71/3.98      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 27.71/3.98      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
% 27.71/3.98      inference(cnf_transformation,[],[f114]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_568,plain,
% 27.71/3.98      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 27.71/3.98      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 27.71/3.98      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 27.71/3.98      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2 ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_5,c_22,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1089,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2
% 27.71/3.98      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_55042,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 27.71/3.98      | k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_41666,c_1089]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_12,plain,
% 27.71/3.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f120]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_23,plain,
% 27.71/3.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f84]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_13,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f121]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_562,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_13,c_22,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1093,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_562,c_12,c_23]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_55063,plain,
% 27.71/3.98      ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_55042,c_12,c_23,c_1093]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_77893,plain,
% 27.71/3.98      ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_34502,c_55063]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_78193,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 27.71/3.98      | k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_41666,c_77893]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_78200,plain,
% 27.71/3.98      ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_78193,c_12,c_23,c_1093]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_81058,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 27.71/3.98      | k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_41343,c_78200]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_81069,plain,
% 27.71/3.98      ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK6) != iProver_top ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_81058,c_12,c_23,c_1093]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_25,plain,
% 27.71/3.98      ( r2_hidden(sK3(X0,X1),X1)
% 27.71/3.98      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 27.71/3.98      | sK3(X0,X1) = X0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f127]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1075,plain,
% 27.71/3.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 27.71/3.98      | sK3(X0,X1) = X0
% 27.71/3.98      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_27,plain,
% 27.71/3.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 27.71/3.98      inference(cnf_transformation,[],[f143]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1073,plain,
% 27.71/3.98      ( X0 = X1
% 27.71/3.98      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_8181,plain,
% 27.71/3.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 27.71/3.98      | sK3(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X1
% 27.71/3.98      | sK3(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1075,c_1073]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_14,plain,
% 27.71/3.98      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f74]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1082,plain,
% 27.71/3.98      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_31002,plain,
% 27.71/3.98      ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0
% 27.71/3.98      | r2_hidden(sK2(k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),sK5) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1082,c_26756]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_61217,plain,
% 27.71/3.98      ( sK3(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = X0
% 27.71/3.98      | sK3(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = sK4
% 27.71/3.98      | k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0
% 27.71/3.98      | r2_hidden(sK2(k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))),sK5) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_8181,c_31002]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_30,negated_conjecture,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 27.71/3.98      | k1_xboole_0 != sK6 ),
% 27.71/3.98      inference(cnf_transformation,[],[f132]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_41,plain,
% 27.71/3.98      ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 27.71/3.98      | sK4 = sK4 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_27]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_26,plain,
% 27.71/3.98      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 27.71/3.98      inference(cnf_transformation,[],[f142]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_44,plain,
% 27.71/3.98      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_26]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1130,plain,
% 27.71/3.98      ( r2_hidden(sK2(sK6),sK6) | k1_xboole_0 = sK6 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_14]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_15,plain,
% 27.71/3.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f77]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1183,plain,
% 27.71/3.98      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
% 27.71/3.98      | ~ r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 27.71/3.98      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_15]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_28,plain,
% 27.71/3.98      ( ~ r2_hidden(X0,X1)
% 27.71/3.98      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 27.71/3.98      inference(cnf_transformation,[],[f130]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1495,plain,
% 27.71/3.98      ( ~ r2_hidden(sK4,sK6)
% 27.71/3.98      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_28]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1555,plain,
% 27.71/3.98      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_15]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2135,plain,
% 27.71/3.98      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_1555]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_17,plain,
% 27.71/3.98      ( r1_tarski(X0,X0) ),
% 27.71/3.98      inference(cnf_transformation,[],[f140]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_5359,plain,
% 27.71/3.98      ( r1_tarski(sK6,sK6) ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_17]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_576,plain,
% 27.71/3.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.71/3.98      theory(equality) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1893,plain,
% 27.71/3.98      ( ~ r2_hidden(X0,X1) | r2_hidden(sK4,sK6) | sK4 != X0 | sK6 != X1 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_576]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7200,plain,
% 27.71/3.98      ( ~ r2_hidden(sK2(sK6),sK6)
% 27.71/3.98      | r2_hidden(sK4,sK6)
% 27.71/3.98      | sK4 != sK2(sK6)
% 27.71/3.98      | sK6 != sK6 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_1893]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_0,plain,
% 27.71/3.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
% 27.71/3.98      inference(cnf_transformation,[],[f113]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1586,plain,
% 27.71/3.98      ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_33,c_0]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_20,plain,
% 27.71/3.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 27.71/3.98      inference(cnf_transformation,[],[f124]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1741,plain,
% 27.71/3.98      ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK5)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1586,c_20]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1742,plain,
% 27.71/3.98      ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_1741,c_1586]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_21,plain,
% 27.71/3.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 27.71/3.98      inference(cnf_transformation,[],[f125]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1077,plain,
% 27.71/3.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_13130,plain,
% 27.71/3.98      ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1742,c_1077]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_13134,plain,
% 27.71/3.98      ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 27.71/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_13130]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1072,plain,
% 27.71/3.98      ( r2_hidden(X0,X1) != iProver_top
% 27.71/3.98      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1739,plain,
% 27.71/3.98      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_33,c_20]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1740,plain,
% 27.71/3.98      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_1739,c_33]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_13129,plain,
% 27.71/3.98      ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1740,c_1077]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1081,plain,
% 27.71/3.98      ( X0 = X1
% 27.71/3.98      | r1_tarski(X1,X0) != iProver_top
% 27.71/3.98      | r1_tarski(X0,X1) != iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_32989,plain,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
% 27.71/3.98      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_13129,c_1081]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_34245,plain,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
% 27.71/3.98      | r2_hidden(sK4,sK5) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1072,c_32989]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_4,plain,
% 27.71/3.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 27.71/3.98      inference(cnf_transformation,[],[f62]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_4227,plain,
% 27.71/3.98      ( r2_hidden(sK2(sK6),X0)
% 27.71/3.98      | ~ r2_hidden(sK2(sK6),sK6)
% 27.71/3.98      | ~ r1_tarski(sK6,X0) ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_4]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_41278,plain,
% 27.71/3.98      ( r2_hidden(sK2(sK6),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 27.71/3.98      | ~ r2_hidden(sK2(sK6),sK6)
% 27.71/3.98      | ~ r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_4227]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_571,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_42350,plain,
% 27.71/3.98      ( sK2(sK6) != X0 | sK4 != X0 | sK4 = sK2(sK6) ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_571]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_42351,plain,
% 27.71/3.98      ( sK2(sK6) != sK4 | sK4 = sK2(sK6) | sK4 != sK4 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_42350]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_9,plain,
% 27.71/3.98      ( r2_hidden(X0,X1)
% 27.71/3.98      | ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
% 27.71/3.98      inference(cnf_transformation,[],[f137]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_564,plain,
% 27.71/3.98      ( r2_hidden(X0,X1)
% 27.71/3.98      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_9,c_22,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1085,plain,
% 27.71/3.98      ( r2_hidden(X0,X1) = iProver_top
% 27.71/3.98      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) != iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_31493,plain,
% 27.71/3.98      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 27.71/3.98      | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1740,c_1085]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1541,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_23,c_22]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1418,plain,
% 27.71/3.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1093,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1547,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_1541,c_1418]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1945,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1,c_1547]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_31496,plain,
% 27.71/3.98      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 27.71/3.98      | r2_hidden(X0,sK5) != iProver_top ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_31493,c_1945]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_34105,plain,
% 27.71/3.98      ( sK4 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_31496,c_1073]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_43612,plain,
% 27.71/3.98      ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0
% 27.71/3.98      | sK2(k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = sK4 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_31002,c_34105]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_44083,plain,
% 27.71/3.98      ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0
% 27.71/3.98      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_43612,c_31002]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_32,negated_conjecture,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 27.71/3.98      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 27.71/3.98      inference(cnf_transformation,[],[f134]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_61230,plain,
% 27.71/3.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != sK5
% 27.71/3.98      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
% 27.71/3.98      | sK3(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = X0
% 27.71/3.98      | sK3(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = sK4 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_8181,c_32]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_31,negated_conjecture,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
% 27.71/3.98      | k1_xboole_0 != sK5 ),
% 27.71/3.98      inference(cnf_transformation,[],[f133]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_570,plain,( X0 = X0 ),theory(equality) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_12829,plain,
% 27.71/3.98      ( k1_xboole_0 = k1_xboole_0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_570]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_43609,plain,
% 27.71/3.98      ( sK2(sK5) = sK4 | sK5 = k1_xboole_0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1082,c_34105]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_43900,plain,
% 27.71/3.98      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK5) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_43609,c_1082]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_4176,plain,
% 27.71/3.98      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_571]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_14491,plain,
% 27.71/3.98      ( X0 != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 != k1_xboole_0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_4176]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_60487,plain,
% 27.71/3.98      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_14491]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_62418,plain,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 27.71/3.98      inference(global_propositional_subsumption,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_61230,c_32,c_31,c_12829,c_34245,c_43900,c_60487]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_66831,plain,
% 27.71/3.98      ( ~ r2_hidden(sK2(sK6),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 27.71/3.98      | sK2(sK6) = X0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_27]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_66833,plain,
% 27.71/3.98      ( ~ r2_hidden(sK2(sK6),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 27.71/3.98      | sK2(sK6) = sK4 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_66831]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_84487,plain,
% 27.71/3.98      ( k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
% 27.71/3.98      inference(global_propositional_subsumption,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_61217,c_32,c_31,c_30,c_41,c_44,c_1130,c_1183,c_1495,
% 27.71/3.98                 c_2135,c_5359,c_7200,c_12829,c_13134,c_34245,c_41278,c_42351,
% 27.71/3.98                 c_43900,c_44083,c_60487,c_66833]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1118,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_22,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2476,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1118,c_1945]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7520,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = X3 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_22,c_2476]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_84894,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(sK6,k5_xboole_0(X0,sK5)),k5_xboole_0(X0,k1_xboole_0)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_84487,c_7520]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_84903,plain,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_xboole_0(k5_xboole_0(sK6,k5_xboole_0(X0,sK5)),X0) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_84894,c_1093]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1119,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_22,c_1]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2098,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1945,c_1945]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2811,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X2,X0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1119,c_2098]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_84904,plain,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_xboole_0(sK5,sK6) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_84903,c_2811]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_34503,plain,
% 27.71/3.98      ( r2_hidden(X0,k5_xboole_0(sK5,k5_xboole_0(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
% 27.71/3.98      | r2_hidden(X0,sK5) != iProver_top
% 27.71/3.98      | r2_hidden(X0,sK6) != iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1586,c_1086]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_84542,plain,
% 27.71/3.98      ( r2_hidden(X0,sK5) != iProver_top
% 27.71/3.98      | r2_hidden(X0,sK6) != iProver_top
% 27.71/3.98      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_84487,c_34503]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1321,plain,
% 27.71/3.98      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_15]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1730,plain,
% 27.71/3.98      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_1321]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1900,plain,
% 27.71/3.98      ( r1_tarski(sK5,sK5) ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_17]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2276,plain,
% 27.71/3.98      ( ~ r2_hidden(X0,X1) | r2_hidden(sK4,sK5) | sK5 != X1 | sK4 != X0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_576]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_41882,plain,
% 27.71/3.98      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK4,sK5) | sK5 != sK5 | sK4 != X0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_2276]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_41883,plain,
% 27.71/3.98      ( sK5 != sK5
% 27.71/3.98      | sK4 != X0
% 27.71/3.98      | r2_hidden(X0,sK5) != iProver_top
% 27.71/3.98      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_41882]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_86148,plain,
% 27.71/3.98      ( r2_hidden(X0,sK5) != iProver_top ),
% 27.71/3.98      inference(global_propositional_subsumption,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_84542,c_32,c_31,c_30,c_41,c_44,c_1130,c_1183,c_1495,
% 27.71/3.98                 c_1730,c_1900,c_2135,c_5359,c_7200,c_12829,c_13134,c_34105,
% 27.71/3.98                 c_34245,c_41278,c_41883,c_42351,c_43900,c_60487,c_66833]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_86161,plain,
% 27.71/3.98      ( sK5 = k1_xboole_0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_43900,c_86148]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_93916,plain,
% 27.71/3.98      ( k5_xboole_0(sK6,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK5,sK6))) = X0
% 27.71/3.98      | k5_xboole_0(k1_xboole_0,k5_xboole_0(sK6,k5_xboole_0(sK5,sK6))) = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK5,sK6)))),X0) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK5,sK6)))),sK6) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK6,k5_xboole_0(sK5,sK6)))),k1_xboole_0) = iProver_top ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_81069,c_84904,c_86161]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2475,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1118,c_1547]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2458,plain,
% 27.71/3.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1093,c_1118]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2499,plain,
% 27.71/3.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_22,c_2458]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_6291,plain,
% 27.71/3.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1117,c_2499]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_93917,plain,
% 27.71/3.98      ( k1_xboole_0 = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k1_xboole_0)),X0) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK5,k1_xboole_0)),sK6) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(sK5,sK6))),k1_xboole_0) = iProver_top ),
% 27.71/3.98      inference(demodulation,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_93916,c_23,c_1418,c_2475,c_6291,c_86161]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_93918,plain,
% 27.71/3.98      ( k1_xboole_0 = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(sK6,k5_xboole_0(k1_xboole_0,sK6))),k1_xboole_0) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),sK6) != iProver_top ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_93917,c_86161]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_93919,plain,
% 27.71/3.98      ( k1_xboole_0 = X0
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k1_xboole_0),X0) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k1_xboole_0),sK6) != iProver_top
% 27.71/3.98      | r2_hidden(sK1(X0,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_93918,c_1418,c_1945]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_93923,plain,
% 27.71/3.98      ( k5_xboole_0(sK6,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = k1_xboole_0
% 27.71/3.98      | sK6 = k1_xboole_0
% 27.71/3.98      | r2_hidden(sK1(sK6,sK6,k1_xboole_0),sK6) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(sK6,sK6,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1088,c_93919]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_93927,plain,
% 27.71/3.98      ( sK6 = k1_xboole_0
% 27.71/3.98      | r2_hidden(sK1(sK6,sK6,k1_xboole_0),sK6) = iProver_top
% 27.71/3.98      | r2_hidden(sK1(sK6,sK6,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_93923,c_12,c_1547]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1565,plain,
% 27.71/3.98      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_571]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2415,plain,
% 27.71/3.98      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_1565]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_58147,plain,
% 27.71/3.98      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 27.71/3.98      inference(instantiation,[status(thm)],[c_2415]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_93979,plain,
% 27.71/3.98      ( sK6 = k1_xboole_0 ),
% 27.71/3.98      inference(global_propositional_subsumption,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_93927,c_32,c_31,c_41,c_44,c_1130,c_1183,c_1495,c_2135,
% 27.71/3.98                 c_5359,c_7200,c_12829,c_13134,c_34245,c_41278,c_42351,
% 27.71/3.98                 c_43900,c_58147,c_60487,c_66833]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_94053,plain,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 27.71/3.98      | k1_xboole_0 != k1_xboole_0 ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_93979,c_30]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_94054,plain,
% 27.71/3.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
% 27.71/3.98      inference(equality_resolution_simp,[status(thm)],[c_94053]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_94055,plain,
% 27.71/3.98      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 27.71/3.98      inference(light_normalisation,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_94054,c_84904,c_86161,c_93979]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_94056,plain,
% 27.71/3.98      ( k1_xboole_0 != k1_xboole_0 ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_94055,c_1418]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_94057,plain,
% 27.71/3.98      ( $false ),
% 27.71/3.98      inference(equality_resolution_simp,[status(thm)],[c_94056]) ).
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 27.71/3.98  
% 27.71/3.98  ------                               Statistics
% 27.71/3.98  
% 27.71/3.98  ------ General
% 27.71/3.98  
% 27.71/3.98  abstr_ref_over_cycles:                  0
% 27.71/3.98  abstr_ref_under_cycles:                 0
% 27.71/3.98  gc_basic_clause_elim:                   0
% 27.71/3.98  forced_gc_time:                         0
% 27.71/3.98  parsing_time:                           0.01
% 27.71/3.98  unif_index_cands_time:                  0.
% 27.71/3.98  unif_index_add_time:                    0.
% 27.71/3.98  orderings_time:                         0.
% 27.71/3.98  out_proof_time:                         0.019
% 27.71/3.98  total_time:                             3.147
% 27.71/3.98  num_of_symbols:                         45
% 27.71/3.98  num_of_terms:                           180308
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing
% 27.71/3.98  
% 27.71/3.98  num_of_splits:                          0
% 27.71/3.98  num_of_split_atoms:                     0
% 27.71/3.98  num_of_reused_defs:                     0
% 27.71/3.98  num_eq_ax_congr_red:                    30
% 27.71/3.98  num_of_sem_filtered_clauses:            1
% 27.71/3.98  num_of_subtypes:                        0
% 27.71/3.98  monotx_restored_types:                  0
% 27.71/3.98  sat_num_of_epr_types:                   0
% 27.71/3.98  sat_num_of_non_cyclic_types:            0
% 27.71/3.98  sat_guarded_non_collapsed_types:        0
% 27.71/3.98  num_pure_diseq_elim:                    0
% 27.71/3.98  simp_replaced_by:                       0
% 27.71/3.98  res_preprocessed:                       147
% 27.71/3.98  prep_upred:                             0
% 27.71/3.98  prep_unflattend:                        0
% 27.71/3.98  smt_new_axioms:                         0
% 27.71/3.98  pred_elim_cands:                        3
% 27.71/3.98  pred_elim:                              0
% 27.71/3.98  pred_elim_cl:                           0
% 27.71/3.98  pred_elim_cycles:                       2
% 27.71/3.98  merged_defs:                            8
% 27.71/3.98  merged_defs_ncl:                        0
% 27.71/3.98  bin_hyper_res:                          8
% 27.71/3.98  prep_cycles:                            4
% 27.71/3.98  pred_elim_time:                         0.001
% 27.71/3.98  splitting_time:                         0.
% 27.71/3.98  sem_filter_time:                        0.
% 27.71/3.98  monotx_time:                            0.
% 27.71/3.98  subtype_inf_time:                       0.
% 27.71/3.98  
% 27.71/3.98  ------ Problem properties
% 27.71/3.98  
% 27.71/3.98  clauses:                                33
% 27.71/3.98  conjectures:                            4
% 27.71/3.98  epr:                                    4
% 27.71/3.98  horn:                                   27
% 27.71/3.98  ground:                                 4
% 27.71/3.98  unary:                                  11
% 27.71/3.98  binary:                                 13
% 27.71/3.98  lits:                                   65
% 27.71/3.98  lits_eq:                                27
% 27.71/3.98  fd_pure:                                0
% 27.71/3.98  fd_pseudo:                              0
% 27.71/3.98  fd_cond:                                1
% 27.71/3.98  fd_pseudo_cond:                         7
% 27.71/3.98  ac_symbols:                             1
% 27.71/3.98  
% 27.71/3.98  ------ Propositional Solver
% 27.71/3.98  
% 27.71/3.98  prop_solver_calls:                      31
% 27.71/3.98  prop_fast_solver_calls:                 1905
% 27.71/3.98  smt_solver_calls:                       0
% 27.71/3.98  smt_fast_solver_calls:                  0
% 27.71/3.98  prop_num_of_clauses:                    18964
% 27.71/3.98  prop_preprocess_simplified:             28832
% 27.71/3.98  prop_fo_subsumed:                       80
% 27.71/3.98  prop_solver_time:                       0.
% 27.71/3.98  smt_solver_time:                        0.
% 27.71/3.98  smt_fast_solver_time:                   0.
% 27.71/3.98  prop_fast_solver_time:                  0.
% 27.71/3.98  prop_unsat_core_time:                   0.
% 27.71/3.98  
% 27.71/3.98  ------ QBF
% 27.71/3.98  
% 27.71/3.98  qbf_q_res:                              0
% 27.71/3.98  qbf_num_tautologies:                    0
% 27.71/3.98  qbf_prep_cycles:                        0
% 27.71/3.98  
% 27.71/3.98  ------ BMC1
% 27.71/3.98  
% 27.71/3.98  bmc1_current_bound:                     -1
% 27.71/3.98  bmc1_last_solved_bound:                 -1
% 27.71/3.98  bmc1_unsat_core_size:                   -1
% 27.71/3.98  bmc1_unsat_core_parents_size:           -1
% 27.71/3.98  bmc1_merge_next_fun:                    0
% 27.71/3.98  bmc1_unsat_core_clauses_time:           0.
% 27.71/3.98  
% 27.71/3.98  ------ Instantiation
% 27.71/3.98  
% 27.71/3.98  inst_num_of_clauses:                    3677
% 27.71/3.98  inst_num_in_passive:                    976
% 27.71/3.98  inst_num_in_active:                     1374
% 27.71/3.98  inst_num_in_unprocessed:                1334
% 27.71/3.98  inst_num_of_loops:                      1920
% 27.71/3.98  inst_num_of_learning_restarts:          0
% 27.71/3.98  inst_num_moves_active_passive:          545
% 27.71/3.98  inst_lit_activity:                      0
% 27.71/3.98  inst_lit_activity_moves:                0
% 27.71/3.98  inst_num_tautologies:                   0
% 27.71/3.98  inst_num_prop_implied:                  0
% 27.71/3.98  inst_num_existing_simplified:           0
% 27.71/3.98  inst_num_eq_res_simplified:             0
% 27.71/3.98  inst_num_child_elim:                    0
% 27.71/3.98  inst_num_of_dismatching_blockings:      3012
% 27.71/3.98  inst_num_of_non_proper_insts:           5145
% 27.71/3.98  inst_num_of_duplicates:                 0
% 27.71/3.98  inst_inst_num_from_inst_to_res:         0
% 27.71/3.98  inst_dismatching_checking_time:         0.
% 27.71/3.98  
% 27.71/3.98  ------ Resolution
% 27.71/3.98  
% 27.71/3.98  res_num_of_clauses:                     0
% 27.71/3.98  res_num_in_passive:                     0
% 27.71/3.98  res_num_in_active:                      0
% 27.71/3.98  res_num_of_loops:                       151
% 27.71/3.98  res_forward_subset_subsumed:            459
% 27.71/3.98  res_backward_subset_subsumed:           18
% 27.71/3.98  res_forward_subsumed:                   0
% 27.71/3.98  res_backward_subsumed:                  0
% 27.71/3.98  res_forward_subsumption_resolution:     0
% 27.71/3.98  res_backward_subsumption_resolution:    0
% 27.71/3.98  res_clause_to_clause_subsumption:       175992
% 27.71/3.98  res_orphan_elimination:                 0
% 27.71/3.98  res_tautology_del:                      299
% 27.71/3.98  res_num_eq_res_simplified:              0
% 27.71/3.98  res_num_sel_changes:                    0
% 27.71/3.98  res_moves_from_active_to_pass:          0
% 27.71/3.98  
% 27.71/3.98  ------ Superposition
% 27.71/3.98  
% 27.71/3.98  sup_time_total:                         0.
% 27.71/3.98  sup_time_generating:                    0.
% 27.71/3.98  sup_time_sim_full:                      0.
% 27.71/3.98  sup_time_sim_immed:                     0.
% 27.71/3.98  
% 27.71/3.98  sup_num_of_clauses:                     3402
% 27.71/3.98  sup_num_in_active:                      169
% 27.71/3.98  sup_num_in_passive:                     3233
% 27.71/3.98  sup_num_of_loops:                       382
% 27.71/3.98  sup_fw_superposition:                   20560
% 27.71/3.98  sup_bw_superposition:                   13985
% 27.71/3.98  sup_immediate_simplified:               20097
% 27.71/3.98  sup_given_eliminated:                   15
% 27.71/3.98  comparisons_done:                       0
% 27.71/3.98  comparisons_avoided:                    393
% 27.71/3.98  
% 27.71/3.98  ------ Simplifications
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  sim_fw_subset_subsumed:                 580
% 27.71/3.98  sim_bw_subset_subsumed:                 534
% 27.71/3.98  sim_fw_subsumed:                        879
% 27.71/3.98  sim_bw_subsumed:                        127
% 27.71/3.98  sim_fw_subsumption_res:                 0
% 27.71/3.98  sim_bw_subsumption_res:                 0
% 27.71/3.98  sim_tautology_del:                      179
% 27.71/3.98  sim_eq_tautology_del:                   3054
% 27.71/3.98  sim_eq_res_simp:                        54
% 27.71/3.98  sim_fw_demodulated:                     22018
% 27.71/3.98  sim_bw_demodulated:                     145
% 27.71/3.98  sim_light_normalised:                   4620
% 27.71/3.98  sim_joinable_taut:                      591
% 27.71/3.98  sim_joinable_simp:                      0
% 27.71/3.98  sim_ac_normalised:                      0
% 27.71/3.98  sim_smt_subsumption:                    0
% 27.71/3.98  
%------------------------------------------------------------------------------
