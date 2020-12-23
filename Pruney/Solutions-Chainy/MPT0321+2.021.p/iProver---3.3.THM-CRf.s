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
% DateTime   : Thu Dec  3 11:37:41 EST 2020

% Result     : Theorem 19.79s
% Output     : CNFRefutation 19.79s
% Verified   : 
% Statistics : Number of formulae       :  167 (1235 expanded)
%              Number of clauses        :   90 ( 383 expanded)
%              Number of leaves         :   24 ( 315 expanded)
%              Depth                    :   28
%              Number of atoms          :  392 (2625 expanded)
%              Number of equality atoms :  258 (2488 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f54,f76,f76])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f35])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK5 != sK7
        | sK4 != sK6 )
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( sK5 != sK7
      | sK4 != sK6 )
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f36,f52])).

fof(f91,plain,(
    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f82,f95])).

fof(f98,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f96])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f102,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f75,f96])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f85])).

fof(f9,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(definition_unfolding,[],[f88,f76,f76,f76])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f108,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f93,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,
    ( sK5 != sK7
    | sK4 != sK6 ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f42])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_36,negated_conjecture,
    ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_31,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1413,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK6,X0)) = k2_zfmisc_1(sK6,k4_xboole_0(sK7,X0)) ),
    inference(superposition,[status(thm)],[c_36,c_31])).

cnf(c_32,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_5499,plain,
    ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,sK6),sK5) ),
    inference(superposition,[status(thm)],[c_1413,c_32])).

cnf(c_7,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_21,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1818,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_21])).

cnf(c_1778,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_32,c_0])).

cnf(c_1782,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1778,c_32])).

cnf(c_12186,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_1818,c_1782])).

cnf(c_25,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_17,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_20,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_794,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17,c_20])).

cnf(c_12355,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X2,X0)),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12186,c_25,c_31,c_32,c_794])).

cnf(c_12855,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12355,c_32])).

cnf(c_30,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_13101,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12855,c_30])).

cnf(c_52375,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK6,X0),k4_xboole_0(k2_zfmisc_1(sK6,X0),k2_zfmisc_1(sK6,k4_xboole_0(sK7,sK5)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5499,c_13101])).

cnf(c_52972,plain,
    ( k2_zfmisc_1(sK6,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK7,sK5)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_52375,c_31])).

cnf(c_68628,plain,
    ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,k4_xboole_0(sK5,k4_xboole_0(sK5,sK7)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_52972])).

cnf(c_1770,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(X0,sK7)) = k2_zfmisc_1(k4_xboole_0(sK6,X0),sK7) ),
    inference(superposition,[status(thm)],[c_36,c_32])).

cnf(c_6689,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK6,sK4),sK7) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_1770,c_31])).

cnf(c_52377,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,X0),k4_xboole_0(k2_zfmisc_1(sK4,X0),k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK7)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6689,c_13101])).

cnf(c_52967,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK5,sK7)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_52377,c_31])).

cnf(c_53145,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(k4_xboole_0(sK5,sK7),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_794,c_52967])).

cnf(c_53584,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_53145,c_20])).

cnf(c_27,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_53867,plain,
    ( k4_xboole_0(sK5,sK7) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_53584,c_27])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_44,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_26,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_45,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_280,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1001,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_1002,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_55707,plain,
    ( k4_xboole_0(sK5,sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_53867,c_35,c_44,c_45,c_1002])).

cnf(c_69151,plain,
    ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,k4_xboole_0(sK5,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_68628,c_55707])).

cnf(c_69152,plain,
    ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_69151,c_20])).

cnf(c_69329,plain,
    ( k4_xboole_0(sK7,sK5) = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_69152,c_27])).

cnf(c_73671,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK7)) = k4_xboole_0(sK7,k1_xboole_0)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_69329,c_0])).

cnf(c_73977,plain,
    ( k4_xboole_0(sK7,k1_xboole_0) = k4_xboole_0(sK5,k1_xboole_0)
    | sK6 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_73671,c_55707])).

cnf(c_73978,plain,
    ( sK6 = k1_xboole_0
    | sK7 = sK5 ),
    inference(demodulation,[status(thm)],[c_73977,c_20])).

cnf(c_75155,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(sK4,sK5)
    | sK7 = sK5 ),
    inference(superposition,[status(thm)],[c_73978,c_36])).

cnf(c_75158,plain,
    ( k2_zfmisc_1(sK4,sK5) = k1_xboole_0
    | sK7 = sK5 ),
    inference(demodulation,[status(thm)],[c_75155,c_26])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_982,plain,
    ( k2_zfmisc_1(X0,sK5) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1204,plain,
    ( k2_zfmisc_1(sK4,sK5) != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_76825,plain,
    ( sK7 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_75158,c_35,c_34,c_1204])).

cnf(c_33,negated_conjecture,
    ( sK4 != sK6
    | sK5 != sK7 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_76867,plain,
    ( sK6 != sK4
    | sK5 != sK5 ),
    inference(demodulation,[status(thm)],[c_76825,c_33])).

cnf(c_76869,plain,
    ( sK6 != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_76867])).

cnf(c_1416,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK6,X0),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK6,k4_xboole_0(X0,sK7)) ),
    inference(superposition,[status(thm)],[c_36,c_31])).

cnf(c_5913,plain,
    ( k2_zfmisc_1(sK6,k4_xboole_0(sK5,sK7)) = k2_zfmisc_1(k4_xboole_0(sK6,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1416,c_32])).

cnf(c_55716,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK6,sK4),sK5) = k2_zfmisc_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_55707,c_5913])).

cnf(c_55718,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK6,sK4),sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_55716,c_25])).

cnf(c_56271,plain,
    ( k4_xboole_0(sK6,sK4) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_55718,c_27])).

cnf(c_23,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_50,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_52,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_59,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_61,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_999,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_1000,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_18,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1207,plain,
    ( k4_xboole_0(sK5,X0) != k4_xboole_0(X0,sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1208,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) != k4_xboole_0(k1_xboole_0,sK5)
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1207])).

cnf(c_1531,plain,
    ( k4_xboole_0(X0,sK5) != X1
    | k4_xboole_0(sK5,X0) != X1
    | k4_xboole_0(sK5,X0) = k4_xboole_0(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_1532,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK5)
    | k4_xboole_0(sK5,k1_xboole_0) != k1_xboole_0
    | k4_xboole_0(k1_xboole_0,sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1639,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5,X0),X0)
    | r2_hidden(sK0(k1_xboole_0,sK5,X0),k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1646,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5,k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2498,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2499,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2498])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5765,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK5,X1),X0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK5,X1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5767,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK5,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5765])).

cnf(c_28,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_759,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1016,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,k1_xboole_0) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_759])).

cnf(c_56270,plain,
    ( k4_xboole_0(sK6,sK4) = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_55718,c_1016])).

cnf(c_62693,plain,
    ( k4_xboole_0(sK6,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_56271,c_34,c_44,c_45,c_50,c_52,c_61,c_1000,c_1208,c_1532,c_1646,c_2499,c_5767,c_56270])).

cnf(c_62756,plain,
    ( k4_xboole_0(sK4,sK6) != k1_xboole_0
    | sK6 = sK4 ),
    inference(superposition,[status(thm)],[c_62693,c_18])).

cnf(c_5800,plain,
    ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,sK5)) != k1_xboole_0
    | k4_xboole_0(sK4,sK6) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5499,c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76869,c_69152,c_62756,c_5800,c_1000,c_45,c_44,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n025.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 20:55:36 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.33  % Running in FOF mode
% 19.79/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.79/2.99  
% 19.79/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.79/2.99  
% 19.79/2.99  ------  iProver source info
% 19.79/2.99  
% 19.79/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.79/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.79/2.99  git: non_committed_changes: false
% 19.79/2.99  git: last_make_outside_of_git: false
% 19.79/2.99  
% 19.79/2.99  ------ 
% 19.79/2.99  
% 19.79/2.99  ------ Input Options
% 19.79/2.99  
% 19.79/2.99  --out_options                           all
% 19.79/2.99  --tptp_safe_out                         true
% 19.79/2.99  --problem_path                          ""
% 19.79/2.99  --include_path                          ""
% 19.79/2.99  --clausifier                            res/vclausify_rel
% 19.79/2.99  --clausifier_options                    --mode clausify
% 19.79/2.99  --stdin                                 false
% 19.79/2.99  --stats_out                             sel
% 19.79/2.99  
% 19.79/2.99  ------ General Options
% 19.79/2.99  
% 19.79/2.99  --fof                                   false
% 19.79/2.99  --time_out_real                         604.99
% 19.79/2.99  --time_out_virtual                      -1.
% 19.79/2.99  --symbol_type_check                     false
% 19.79/2.99  --clausify_out                          false
% 19.79/2.99  --sig_cnt_out                           false
% 19.79/2.99  --trig_cnt_out                          false
% 19.79/2.99  --trig_cnt_out_tolerance                1.
% 19.79/2.99  --trig_cnt_out_sk_spl                   false
% 19.79/2.99  --abstr_cl_out                          false
% 19.79/2.99  
% 19.79/2.99  ------ Global Options
% 19.79/2.99  
% 19.79/2.99  --schedule                              none
% 19.79/2.99  --add_important_lit                     false
% 19.79/2.99  --prop_solver_per_cl                    1000
% 19.79/2.99  --min_unsat_core                        false
% 19.79/2.99  --soft_assumptions                      false
% 19.79/2.99  --soft_lemma_size                       3
% 19.79/2.99  --prop_impl_unit_size                   0
% 19.79/2.99  --prop_impl_unit                        []
% 19.79/2.99  --share_sel_clauses                     true
% 19.79/2.99  --reset_solvers                         false
% 19.79/2.99  --bc_imp_inh                            [conj_cone]
% 19.79/2.99  --conj_cone_tolerance                   3.
% 19.79/2.99  --extra_neg_conj                        none
% 19.79/2.99  --large_theory_mode                     true
% 19.79/2.99  --prolific_symb_bound                   200
% 19.79/2.99  --lt_threshold                          2000
% 19.79/2.99  --clause_weak_htbl                      true
% 19.79/2.99  --gc_record_bc_elim                     false
% 19.79/2.99  
% 19.79/2.99  ------ Preprocessing Options
% 19.79/2.99  
% 19.79/2.99  --preprocessing_flag                    true
% 19.79/2.99  --time_out_prep_mult                    0.1
% 19.79/2.99  --splitting_mode                        input
% 19.79/2.99  --splitting_grd                         true
% 19.79/2.99  --splitting_cvd                         false
% 19.79/2.99  --splitting_cvd_svl                     false
% 19.79/2.99  --splitting_nvd                         32
% 19.79/2.99  --sub_typing                            true
% 19.79/2.99  --prep_gs_sim                           false
% 19.79/2.99  --prep_unflatten                        true
% 19.79/2.99  --prep_res_sim                          true
% 19.79/2.99  --prep_upred                            true
% 19.79/2.99  --prep_sem_filter                       exhaustive
% 19.79/2.99  --prep_sem_filter_out                   false
% 19.79/2.99  --pred_elim                             false
% 19.79/2.99  --res_sim_input                         true
% 19.79/2.99  --eq_ax_congr_red                       true
% 19.79/2.99  --pure_diseq_elim                       true
% 19.79/2.99  --brand_transform                       false
% 19.79/2.99  --non_eq_to_eq                          false
% 19.79/2.99  --prep_def_merge                        true
% 19.79/2.99  --prep_def_merge_prop_impl              false
% 19.79/2.99  --prep_def_merge_mbd                    true
% 19.79/2.99  --prep_def_merge_tr_red                 false
% 19.79/2.99  --prep_def_merge_tr_cl                  false
% 19.79/2.99  --smt_preprocessing                     true
% 19.79/2.99  --smt_ac_axioms                         fast
% 19.79/2.99  --preprocessed_out                      false
% 19.79/2.99  --preprocessed_stats                    false
% 19.79/2.99  
% 19.79/2.99  ------ Abstraction refinement Options
% 19.79/2.99  
% 19.79/2.99  --abstr_ref                             []
% 19.79/2.99  --abstr_ref_prep                        false
% 19.79/2.99  --abstr_ref_until_sat                   false
% 19.79/2.99  --abstr_ref_sig_restrict                funpre
% 19.79/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.79/2.99  --abstr_ref_under                       []
% 19.79/2.99  
% 19.79/2.99  ------ SAT Options
% 19.79/2.99  
% 19.79/2.99  --sat_mode                              false
% 19.79/2.99  --sat_fm_restart_options                ""
% 19.79/2.99  --sat_gr_def                            false
% 19.79/2.99  --sat_epr_types                         true
% 19.79/2.99  --sat_non_cyclic_types                  false
% 19.79/2.99  --sat_finite_models                     false
% 19.79/2.99  --sat_fm_lemmas                         false
% 19.79/2.99  --sat_fm_prep                           false
% 19.79/2.99  --sat_fm_uc_incr                        true
% 19.79/2.99  --sat_out_model                         small
% 19.79/2.99  --sat_out_clauses                       false
% 19.79/2.99  
% 19.79/2.99  ------ QBF Options
% 19.79/2.99  
% 19.79/2.99  --qbf_mode                              false
% 19.79/2.99  --qbf_elim_univ                         false
% 19.79/2.99  --qbf_dom_inst                          none
% 19.79/2.99  --qbf_dom_pre_inst                      false
% 19.79/2.99  --qbf_sk_in                             false
% 19.79/2.99  --qbf_pred_elim                         true
% 19.79/2.99  --qbf_split                             512
% 19.79/2.99  
% 19.79/2.99  ------ BMC1 Options
% 19.79/2.99  
% 19.79/2.99  --bmc1_incremental                      false
% 19.79/2.99  --bmc1_axioms                           reachable_all
% 19.79/2.99  --bmc1_min_bound                        0
% 19.79/2.99  --bmc1_max_bound                        -1
% 19.79/2.99  --bmc1_max_bound_default                -1
% 19.79/2.99  --bmc1_symbol_reachability              true
% 19.79/2.99  --bmc1_property_lemmas                  false
% 19.79/2.99  --bmc1_k_induction                      false
% 19.79/2.99  --bmc1_non_equiv_states                 false
% 19.79/2.99  --bmc1_deadlock                         false
% 19.79/2.99  --bmc1_ucm                              false
% 19.79/2.99  --bmc1_add_unsat_core                   none
% 19.79/2.99  --bmc1_unsat_core_children              false
% 19.79/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.79/2.99  --bmc1_out_stat                         full
% 19.79/2.99  --bmc1_ground_init                      false
% 19.79/2.99  --bmc1_pre_inst_next_state              false
% 19.79/2.99  --bmc1_pre_inst_state                   false
% 19.79/2.99  --bmc1_pre_inst_reach_state             false
% 19.79/2.99  --bmc1_out_unsat_core                   false
% 19.79/2.99  --bmc1_aig_witness_out                  false
% 19.79/2.99  --bmc1_verbose                          false
% 19.79/2.99  --bmc1_dump_clauses_tptp                false
% 19.79/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.79/2.99  --bmc1_dump_file                        -
% 19.79/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.79/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.79/2.99  --bmc1_ucm_extend_mode                  1
% 19.79/2.99  --bmc1_ucm_init_mode                    2
% 19.79/2.99  --bmc1_ucm_cone_mode                    none
% 19.79/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.79/2.99  --bmc1_ucm_relax_model                  4
% 19.79/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.79/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.79/2.99  --bmc1_ucm_layered_model                none
% 19.79/2.99  --bmc1_ucm_max_lemma_size               10
% 19.79/2.99  
% 19.79/2.99  ------ AIG Options
% 19.79/2.99  
% 19.79/2.99  --aig_mode                              false
% 19.79/2.99  
% 19.79/2.99  ------ Instantiation Options
% 19.79/2.99  
% 19.79/2.99  --instantiation_flag                    true
% 19.79/2.99  --inst_sos_flag                         false
% 19.79/2.99  --inst_sos_phase                        true
% 19.79/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.79/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.79/2.99  --inst_lit_sel_side                     num_symb
% 19.79/2.99  --inst_solver_per_active                1400
% 19.79/2.99  --inst_solver_calls_frac                1.
% 19.79/2.99  --inst_passive_queue_type               priority_queues
% 19.79/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.79/2.99  --inst_passive_queues_freq              [25;2]
% 19.79/2.99  --inst_dismatching                      true
% 19.79/2.99  --inst_eager_unprocessed_to_passive     true
% 19.79/2.99  --inst_prop_sim_given                   true
% 19.79/2.99  --inst_prop_sim_new                     false
% 19.79/2.99  --inst_subs_new                         false
% 19.79/2.99  --inst_eq_res_simp                      false
% 19.79/2.99  --inst_subs_given                       false
% 19.79/2.99  --inst_orphan_elimination               true
% 19.79/2.99  --inst_learning_loop_flag               true
% 19.79/2.99  --inst_learning_start                   3000
% 19.79/2.99  --inst_learning_factor                  2
% 19.79/2.99  --inst_start_prop_sim_after_learn       3
% 19.79/2.99  --inst_sel_renew                        solver
% 19.79/2.99  --inst_lit_activity_flag                true
% 19.79/2.99  --inst_restr_to_given                   false
% 19.79/2.99  --inst_activity_threshold               500
% 19.79/2.99  --inst_out_proof                        true
% 19.79/2.99  
% 19.79/2.99  ------ Resolution Options
% 19.79/2.99  
% 19.79/2.99  --resolution_flag                       true
% 19.79/2.99  --res_lit_sel                           adaptive
% 19.79/2.99  --res_lit_sel_side                      none
% 19.79/2.99  --res_ordering                          kbo
% 19.79/2.99  --res_to_prop_solver                    active
% 19.79/2.99  --res_prop_simpl_new                    false
% 19.79/2.99  --res_prop_simpl_given                  true
% 19.79/2.99  --res_passive_queue_type                priority_queues
% 19.79/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.79/2.99  --res_passive_queues_freq               [15;5]
% 19.79/2.99  --res_forward_subs                      full
% 19.79/2.99  --res_backward_subs                     full
% 19.79/2.99  --res_forward_subs_resolution           true
% 19.79/2.99  --res_backward_subs_resolution          true
% 19.79/2.99  --res_orphan_elimination                true
% 19.79/2.99  --res_time_limit                        2.
% 19.79/2.99  --res_out_proof                         true
% 19.79/2.99  
% 19.79/2.99  ------ Superposition Options
% 19.79/2.99  
% 19.79/2.99  --superposition_flag                    true
% 19.79/2.99  --sup_passive_queue_type                priority_queues
% 19.79/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.79/2.99  --sup_passive_queues_freq               [1;4]
% 19.79/2.99  --demod_completeness_check              fast
% 19.79/2.99  --demod_use_ground                      true
% 19.79/2.99  --sup_to_prop_solver                    passive
% 19.79/2.99  --sup_prop_simpl_new                    true
% 19.79/2.99  --sup_prop_simpl_given                  true
% 19.79/2.99  --sup_fun_splitting                     false
% 19.79/2.99  --sup_smt_interval                      50000
% 19.79/2.99  
% 19.79/2.99  ------ Superposition Simplification Setup
% 19.79/2.99  
% 19.79/2.99  --sup_indices_passive                   []
% 19.79/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.79/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.79/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.79/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.79/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.79/2.99  --sup_full_bw                           [BwDemod]
% 19.79/2.99  --sup_immed_triv                        [TrivRules]
% 19.79/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.79/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.79/2.99  --sup_immed_bw_main                     []
% 19.79/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.79/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.79/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.79/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.79/2.99  
% 19.79/2.99  ------ Combination Options
% 19.79/2.99  
% 19.79/2.99  --comb_res_mult                         3
% 19.79/2.99  --comb_sup_mult                         2
% 19.79/2.99  --comb_inst_mult                        10
% 19.79/2.99  
% 19.79/2.99  ------ Debug Options
% 19.79/2.99  
% 19.79/2.99  --dbg_backtrace                         false
% 19.79/2.99  --dbg_dump_prop_clauses                 false
% 19.79/2.99  --dbg_dump_prop_clauses_file            -
% 19.79/2.99  --dbg_out_stat                          false
% 19.79/2.99  ------ Parsing...
% 19.79/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.79/2.99  
% 19.79/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.79/2.99  
% 19.79/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.79/2.99  
% 19.79/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.79/2.99  ------ Proving...
% 19.79/2.99  ------ Problem Properties 
% 19.79/2.99  
% 19.79/2.99  
% 19.79/2.99  clauses                                 37
% 19.79/2.99  conjectures                             4
% 19.79/2.99  EPR                                     5
% 19.79/2.99  Horn                                    26
% 19.79/2.99  unary                                   15
% 19.79/2.99  binary                                  14
% 19.79/2.99  lits                                    68
% 19.79/2.99  lits eq                                 31
% 19.79/2.99  fd_pure                                 0
% 19.79/2.99  fd_pseudo                               0
% 19.79/2.99  fd_cond                                 4
% 19.79/2.99  fd_pseudo_cond                          4
% 19.79/2.99  AC symbols                              0
% 19.79/2.99  
% 19.79/2.99  ------ Input Options Time Limit: Unbounded
% 19.79/2.99  
% 19.79/2.99  
% 19.79/2.99  ------ 
% 19.79/2.99  Current options:
% 19.79/2.99  ------ 
% 19.79/2.99  
% 19.79/2.99  ------ Input Options
% 19.79/2.99  
% 19.79/2.99  --out_options                           all
% 19.79/2.99  --tptp_safe_out                         true
% 19.79/2.99  --problem_path                          ""
% 19.79/2.99  --include_path                          ""
% 19.79/2.99  --clausifier                            res/vclausify_rel
% 19.79/2.99  --clausifier_options                    --mode clausify
% 19.79/2.99  --stdin                                 false
% 19.79/2.99  --stats_out                             sel
% 19.79/2.99  
% 19.79/2.99  ------ General Options
% 19.79/2.99  
% 19.79/2.99  --fof                                   false
% 19.79/2.99  --time_out_real                         604.99
% 19.79/2.99  --time_out_virtual                      -1.
% 19.79/2.99  --symbol_type_check                     false
% 19.79/2.99  --clausify_out                          false
% 19.79/2.99  --sig_cnt_out                           false
% 19.79/2.99  --trig_cnt_out                          false
% 19.79/2.99  --trig_cnt_out_tolerance                1.
% 19.79/2.99  --trig_cnt_out_sk_spl                   false
% 19.79/2.99  --abstr_cl_out                          false
% 19.79/2.99  
% 19.79/2.99  ------ Global Options
% 19.79/2.99  
% 19.79/2.99  --schedule                              none
% 19.79/2.99  --add_important_lit                     false
% 19.79/2.99  --prop_solver_per_cl                    1000
% 19.79/2.99  --min_unsat_core                        false
% 19.79/2.99  --soft_assumptions                      false
% 19.79/2.99  --soft_lemma_size                       3
% 19.79/2.99  --prop_impl_unit_size                   0
% 19.79/2.99  --prop_impl_unit                        []
% 19.79/2.99  --share_sel_clauses                     true
% 19.79/2.99  --reset_solvers                         false
% 19.79/2.99  --bc_imp_inh                            [conj_cone]
% 19.79/2.99  --conj_cone_tolerance                   3.
% 19.79/2.99  --extra_neg_conj                        none
% 19.79/2.99  --large_theory_mode                     true
% 19.79/2.99  --prolific_symb_bound                   200
% 19.79/2.99  --lt_threshold                          2000
% 19.79/2.99  --clause_weak_htbl                      true
% 19.79/2.99  --gc_record_bc_elim                     false
% 19.79/2.99  
% 19.79/2.99  ------ Preprocessing Options
% 19.79/2.99  
% 19.79/2.99  --preprocessing_flag                    true
% 19.79/2.99  --time_out_prep_mult                    0.1
% 19.79/2.99  --splitting_mode                        input
% 19.79/2.99  --splitting_grd                         true
% 19.79/2.99  --splitting_cvd                         false
% 19.79/2.99  --splitting_cvd_svl                     false
% 19.79/2.99  --splitting_nvd                         32
% 19.79/2.99  --sub_typing                            true
% 19.79/2.99  --prep_gs_sim                           false
% 19.79/2.99  --prep_unflatten                        true
% 19.79/2.99  --prep_res_sim                          true
% 19.79/2.99  --prep_upred                            true
% 19.79/2.99  --prep_sem_filter                       exhaustive
% 19.79/2.99  --prep_sem_filter_out                   false
% 19.79/2.99  --pred_elim                             false
% 19.79/2.99  --res_sim_input                         true
% 19.79/2.99  --eq_ax_congr_red                       true
% 19.79/2.99  --pure_diseq_elim                       true
% 19.79/2.99  --brand_transform                       false
% 19.79/2.99  --non_eq_to_eq                          false
% 19.79/2.99  --prep_def_merge                        true
% 19.79/2.99  --prep_def_merge_prop_impl              false
% 19.79/2.99  --prep_def_merge_mbd                    true
% 19.79/2.99  --prep_def_merge_tr_red                 false
% 19.79/2.99  --prep_def_merge_tr_cl                  false
% 19.79/2.99  --smt_preprocessing                     true
% 19.79/2.99  --smt_ac_axioms                         fast
% 19.79/2.99  --preprocessed_out                      false
% 19.79/2.99  --preprocessed_stats                    false
% 19.79/2.99  
% 19.79/2.99  ------ Abstraction refinement Options
% 19.79/2.99  
% 19.79/2.99  --abstr_ref                             []
% 19.79/2.99  --abstr_ref_prep                        false
% 19.79/2.99  --abstr_ref_until_sat                   false
% 19.79/2.99  --abstr_ref_sig_restrict                funpre
% 19.79/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.79/2.99  --abstr_ref_under                       []
% 19.79/2.99  
% 19.79/2.99  ------ SAT Options
% 19.79/2.99  
% 19.79/2.99  --sat_mode                              false
% 19.79/2.99  --sat_fm_restart_options                ""
% 19.79/2.99  --sat_gr_def                            false
% 19.79/2.99  --sat_epr_types                         true
% 19.79/2.99  --sat_non_cyclic_types                  false
% 19.79/2.99  --sat_finite_models                     false
% 19.79/2.99  --sat_fm_lemmas                         false
% 19.79/2.99  --sat_fm_prep                           false
% 19.79/2.99  --sat_fm_uc_incr                        true
% 19.79/2.99  --sat_out_model                         small
% 19.79/2.99  --sat_out_clauses                       false
% 19.79/2.99  
% 19.79/2.99  ------ QBF Options
% 19.79/2.99  
% 19.79/2.99  --qbf_mode                              false
% 19.79/2.99  --qbf_elim_univ                         false
% 19.79/2.99  --qbf_dom_inst                          none
% 19.79/2.99  --qbf_dom_pre_inst                      false
% 19.79/2.99  --qbf_sk_in                             false
% 19.79/2.99  --qbf_pred_elim                         true
% 19.79/2.99  --qbf_split                             512
% 19.79/2.99  
% 19.79/2.99  ------ BMC1 Options
% 19.79/2.99  
% 19.79/2.99  --bmc1_incremental                      false
% 19.79/2.99  --bmc1_axioms                           reachable_all
% 19.79/2.99  --bmc1_min_bound                        0
% 19.79/2.99  --bmc1_max_bound                        -1
% 19.79/2.99  --bmc1_max_bound_default                -1
% 19.79/2.99  --bmc1_symbol_reachability              true
% 19.79/2.99  --bmc1_property_lemmas                  false
% 19.79/2.99  --bmc1_k_induction                      false
% 19.79/2.99  --bmc1_non_equiv_states                 false
% 19.79/2.99  --bmc1_deadlock                         false
% 19.79/2.99  --bmc1_ucm                              false
% 19.79/2.99  --bmc1_add_unsat_core                   none
% 19.79/2.99  --bmc1_unsat_core_children              false
% 19.79/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.79/2.99  --bmc1_out_stat                         full
% 19.79/2.99  --bmc1_ground_init                      false
% 19.79/2.99  --bmc1_pre_inst_next_state              false
% 19.79/2.99  --bmc1_pre_inst_state                   false
% 19.79/2.99  --bmc1_pre_inst_reach_state             false
% 19.79/2.99  --bmc1_out_unsat_core                   false
% 19.79/2.99  --bmc1_aig_witness_out                  false
% 19.79/2.99  --bmc1_verbose                          false
% 19.79/2.99  --bmc1_dump_clauses_tptp                false
% 19.79/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.79/2.99  --bmc1_dump_file                        -
% 19.79/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.79/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.79/2.99  --bmc1_ucm_extend_mode                  1
% 19.79/2.99  --bmc1_ucm_init_mode                    2
% 19.79/2.99  --bmc1_ucm_cone_mode                    none
% 19.79/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.79/2.99  --bmc1_ucm_relax_model                  4
% 19.79/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.79/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.79/2.99  --bmc1_ucm_layered_model                none
% 19.79/2.99  --bmc1_ucm_max_lemma_size               10
% 19.79/2.99  
% 19.79/2.99  ------ AIG Options
% 19.79/2.99  
% 19.79/2.99  --aig_mode                              false
% 19.79/2.99  
% 19.79/2.99  ------ Instantiation Options
% 19.79/2.99  
% 19.79/2.99  --instantiation_flag                    true
% 19.79/2.99  --inst_sos_flag                         false
% 19.79/2.99  --inst_sos_phase                        true
% 19.79/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.79/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.79/2.99  --inst_lit_sel_side                     num_symb
% 19.79/2.99  --inst_solver_per_active                1400
% 19.79/2.99  --inst_solver_calls_frac                1.
% 19.79/2.99  --inst_passive_queue_type               priority_queues
% 19.79/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.79/2.99  --inst_passive_queues_freq              [25;2]
% 19.79/2.99  --inst_dismatching                      true
% 19.79/2.99  --inst_eager_unprocessed_to_passive     true
% 19.79/2.99  --inst_prop_sim_given                   true
% 19.79/2.99  --inst_prop_sim_new                     false
% 19.79/2.99  --inst_subs_new                         false
% 19.79/2.99  --inst_eq_res_simp                      false
% 19.79/2.99  --inst_subs_given                       false
% 19.79/2.99  --inst_orphan_elimination               true
% 19.79/2.99  --inst_learning_loop_flag               true
% 19.79/2.99  --inst_learning_start                   3000
% 19.79/2.99  --inst_learning_factor                  2
% 19.79/2.99  --inst_start_prop_sim_after_learn       3
% 19.79/2.99  --inst_sel_renew                        solver
% 19.79/2.99  --inst_lit_activity_flag                true
% 19.79/2.99  --inst_restr_to_given                   false
% 19.79/2.99  --inst_activity_threshold               500
% 19.79/2.99  --inst_out_proof                        true
% 19.79/2.99  
% 19.79/2.99  ------ Resolution Options
% 19.79/2.99  
% 19.79/2.99  --resolution_flag                       true
% 19.79/2.99  --res_lit_sel                           adaptive
% 19.79/2.99  --res_lit_sel_side                      none
% 19.79/2.99  --res_ordering                          kbo
% 19.79/2.99  --res_to_prop_solver                    active
% 19.79/2.99  --res_prop_simpl_new                    false
% 19.79/2.99  --res_prop_simpl_given                  true
% 19.79/2.99  --res_passive_queue_type                priority_queues
% 19.79/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.79/2.99  --res_passive_queues_freq               [15;5]
% 19.79/2.99  --res_forward_subs                      full
% 19.79/2.99  --res_backward_subs                     full
% 19.79/2.99  --res_forward_subs_resolution           true
% 19.79/2.99  --res_backward_subs_resolution          true
% 19.79/2.99  --res_orphan_elimination                true
% 19.79/2.99  --res_time_limit                        2.
% 19.79/2.99  --res_out_proof                         true
% 19.79/2.99  
% 19.79/2.99  ------ Superposition Options
% 19.79/2.99  
% 19.79/2.99  --superposition_flag                    true
% 19.79/2.99  --sup_passive_queue_type                priority_queues
% 19.79/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.79/2.99  --sup_passive_queues_freq               [1;4]
% 19.79/2.99  --demod_completeness_check              fast
% 19.79/2.99  --demod_use_ground                      true
% 19.79/2.99  --sup_to_prop_solver                    passive
% 19.79/2.99  --sup_prop_simpl_new                    true
% 19.79/2.99  --sup_prop_simpl_given                  true
% 19.79/2.99  --sup_fun_splitting                     false
% 19.79/2.99  --sup_smt_interval                      50000
% 19.79/2.99  
% 19.79/2.99  ------ Superposition Simplification Setup
% 19.79/2.99  
% 19.79/2.99  --sup_indices_passive                   []
% 19.79/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.79/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.79/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.79/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.79/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.79/2.99  --sup_full_bw                           [BwDemod]
% 19.79/2.99  --sup_immed_triv                        [TrivRules]
% 19.79/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.79/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.79/2.99  --sup_immed_bw_main                     []
% 19.79/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.79/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.79/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.79/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.79/2.99  
% 19.79/2.99  ------ Combination Options
% 19.79/2.99  
% 19.79/2.99  --comb_res_mult                         3
% 19.79/2.99  --comb_sup_mult                         2
% 19.79/2.99  --comb_inst_mult                        10
% 19.79/2.99  
% 19.79/2.99  ------ Debug Options
% 19.79/2.99  
% 19.79/2.99  --dbg_backtrace                         false
% 19.79/2.99  --dbg_dump_prop_clauses                 false
% 19.79/2.99  --dbg_dump_prop_clauses_file            -
% 19.79/2.99  --dbg_out_stat                          false
% 19.79/2.99  
% 19.79/2.99  
% 19.79/2.99  
% 19.79/2.99  
% 19.79/2.99  ------ Proving...
% 19.79/2.99  
% 19.79/2.99  
% 19.79/2.99  % SZS status Theorem for theBenchmark.p
% 19.79/2.99  
% 19.79/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.79/2.99  
% 19.79/2.99  fof(f1,axiom,(
% 19.79/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f54,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f1])).
% 19.79/2.99  
% 19.79/2.99  fof(f14,axiom,(
% 19.79/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f76,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.79/2.99    inference(cnf_transformation,[],[f14])).
% 19.79/2.99  
% 19.79/2.99  fof(f97,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 19.79/2.99    inference(definition_unfolding,[],[f54,f76,f76])).
% 19.79/2.99  
% 19.79/2.99  fof(f24,conjecture,(
% 19.79/2.99    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f25,negated_conjecture,(
% 19.79/2.99    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.79/2.99    inference(negated_conjecture,[],[f24])).
% 19.79/2.99  
% 19.79/2.99  fof(f35,plain,(
% 19.79/2.99    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 19.79/2.99    inference(ennf_transformation,[],[f25])).
% 19.79/2.99  
% 19.79/2.99  fof(f36,plain,(
% 19.79/2.99    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 19.79/2.99    inference(flattening,[],[f35])).
% 19.79/2.99  
% 19.79/2.99  fof(f52,plain,(
% 19.79/2.99    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK5 != sK7 | sK4 != sK6) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7))),
% 19.79/2.99    introduced(choice_axiom,[])).
% 19.79/2.99  
% 19.79/2.99  fof(f53,plain,(
% 19.79/2.99    (sK5 != sK7 | sK4 != sK6) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7)),
% 19.79/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f36,f52])).
% 19.79/2.99  
% 19.79/2.99  fof(f91,plain,(
% 19.79/2.99    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7)),
% 19.79/2.99    inference(cnf_transformation,[],[f53])).
% 19.79/2.99  
% 19.79/2.99  fof(f23,axiom,(
% 19.79/2.99    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f90,plain,(
% 19.79/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 19.79/2.99    inference(cnf_transformation,[],[f23])).
% 19.79/2.99  
% 19.79/2.99  fof(f89,plain,(
% 19.79/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f23])).
% 19.79/2.99  
% 19.79/2.99  fof(f3,axiom,(
% 19.79/2.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f26,plain,(
% 19.79/2.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 19.79/2.99    inference(rectify,[],[f3])).
% 19.79/2.99  
% 19.79/2.99  fof(f61,plain,(
% 19.79/2.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 19.79/2.99    inference(cnf_transformation,[],[f26])).
% 19.79/2.99  
% 19.79/2.99  fof(f19,axiom,(
% 19.79/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f82,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.79/2.99    inference(cnf_transformation,[],[f19])).
% 19.79/2.99  
% 19.79/2.99  fof(f17,axiom,(
% 19.79/2.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f80,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f17])).
% 19.79/2.99  
% 19.79/2.99  fof(f18,axiom,(
% 19.79/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f81,plain,(
% 19.79/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f18])).
% 19.79/2.99  
% 19.79/2.99  fof(f95,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.79/2.99    inference(definition_unfolding,[],[f80,f81])).
% 19.79/2.99  
% 19.79/2.99  fof(f96,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 19.79/2.99    inference(definition_unfolding,[],[f82,f95])).
% 19.79/2.99  
% 19.79/2.99  fof(f98,plain,(
% 19.79/2.99    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 19.79/2.99    inference(definition_unfolding,[],[f61,f96])).
% 19.79/2.99  
% 19.79/2.99  fof(f13,axiom,(
% 19.79/2.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f75,plain,(
% 19.79/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f13])).
% 19.79/2.99  
% 19.79/2.99  fof(f102,plain,(
% 19.79/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 19.79/2.99    inference(definition_unfolding,[],[f75,f96])).
% 19.79/2.99  
% 19.79/2.99  fof(f20,axiom,(
% 19.79/2.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f50,plain,(
% 19.79/2.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.79/2.99    inference(nnf_transformation,[],[f20])).
% 19.79/2.99  
% 19.79/2.99  fof(f51,plain,(
% 19.79/2.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.79/2.99    inference(flattening,[],[f50])).
% 19.79/2.99  
% 19.79/2.99  fof(f85,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 19.79/2.99    inference(cnf_transformation,[],[f51])).
% 19.79/2.99  
% 19.79/2.99  fof(f107,plain,(
% 19.79/2.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 19.79/2.99    inference(equality_resolution,[],[f85])).
% 19.79/2.99  
% 19.79/2.99  fof(f9,axiom,(
% 19.79/2.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f71,plain,(
% 19.79/2.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 19.79/2.99    inference(cnf_transformation,[],[f9])).
% 19.79/2.99  
% 19.79/2.99  fof(f101,plain,(
% 19.79/2.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 19.79/2.99    inference(definition_unfolding,[],[f71,f76])).
% 19.79/2.99  
% 19.79/2.99  fof(f12,axiom,(
% 19.79/2.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f74,plain,(
% 19.79/2.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.79/2.99    inference(cnf_transformation,[],[f12])).
% 19.79/2.99  
% 19.79/2.99  fof(f22,axiom,(
% 19.79/2.99    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f88,plain,(
% 19.79/2.99    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 19.79/2.99    inference(cnf_transformation,[],[f22])).
% 19.79/2.99  
% 19.79/2.99  fof(f103,plain,(
% 19.79/2.99    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 19.79/2.99    inference(definition_unfolding,[],[f88,f76,f76,f76])).
% 19.79/2.99  
% 19.79/2.99  fof(f83,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f51])).
% 19.79/2.99  
% 19.79/2.99  fof(f92,plain,(
% 19.79/2.99    k1_xboole_0 != sK4),
% 19.79/2.99    inference(cnf_transformation,[],[f53])).
% 19.79/2.99  
% 19.79/2.99  fof(f84,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 19.79/2.99    inference(cnf_transformation,[],[f51])).
% 19.79/2.99  
% 19.79/2.99  fof(f108,plain,(
% 19.79/2.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 19.79/2.99    inference(equality_resolution,[],[f84])).
% 19.79/2.99  
% 19.79/2.99  fof(f93,plain,(
% 19.79/2.99    k1_xboole_0 != sK5),
% 19.79/2.99    inference(cnf_transformation,[],[f53])).
% 19.79/2.99  
% 19.79/2.99  fof(f94,plain,(
% 19.79/2.99    sK5 != sK7 | sK4 != sK6),
% 19.79/2.99    inference(cnf_transformation,[],[f53])).
% 19.79/2.99  
% 19.79/2.99  fof(f16,axiom,(
% 19.79/2.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f49,plain,(
% 19.79/2.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 19.79/2.99    inference(nnf_transformation,[],[f16])).
% 19.79/2.99  
% 19.79/2.99  fof(f79,plain,(
% 19.79/2.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 19.79/2.99    inference(cnf_transformation,[],[f49])).
% 19.79/2.99  
% 19.79/2.99  fof(f15,axiom,(
% 19.79/2.99    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f77,plain,(
% 19.79/2.99    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 19.79/2.99    inference(cnf_transformation,[],[f15])).
% 19.79/2.99  
% 19.79/2.99  fof(f8,axiom,(
% 19.79/2.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f48,plain,(
% 19.79/2.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 19.79/2.99    inference(nnf_transformation,[],[f8])).
% 19.79/2.99  
% 19.79/2.99  fof(f69,plain,(
% 19.79/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.79/2.99    inference(cnf_transformation,[],[f48])).
% 19.79/2.99  
% 19.79/2.99  fof(f10,axiom,(
% 19.79/2.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f33,plain,(
% 19.79/2.99    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 19.79/2.99    inference(ennf_transformation,[],[f10])).
% 19.79/2.99  
% 19.79/2.99  fof(f72,plain,(
% 19.79/2.99    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f33])).
% 19.79/2.99  
% 19.79/2.99  fof(f2,axiom,(
% 19.79/2.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f37,plain,(
% 19.79/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.79/2.99    inference(nnf_transformation,[],[f2])).
% 19.79/2.99  
% 19.79/2.99  fof(f38,plain,(
% 19.79/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.79/2.99    inference(flattening,[],[f37])).
% 19.79/2.99  
% 19.79/2.99  fof(f39,plain,(
% 19.79/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.79/2.99    inference(rectify,[],[f38])).
% 19.79/2.99  
% 19.79/2.99  fof(f40,plain,(
% 19.79/2.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.79/2.99    introduced(choice_axiom,[])).
% 19.79/2.99  
% 19.79/2.99  fof(f41,plain,(
% 19.79/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.79/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 19.79/2.99  
% 19.79/2.99  fof(f58,plain,(
% 19.79/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f41])).
% 19.79/2.99  
% 19.79/2.99  fof(f70,plain,(
% 19.79/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f48])).
% 19.79/2.99  
% 19.79/2.99  fof(f5,axiom,(
% 19.79/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f27,plain,(
% 19.79/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.79/2.99    inference(rectify,[],[f5])).
% 19.79/2.99  
% 19.79/2.99  fof(f30,plain,(
% 19.79/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.79/2.99    inference(ennf_transformation,[],[f27])).
% 19.79/2.99  
% 19.79/2.99  fof(f42,plain,(
% 19.79/2.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 19.79/2.99    introduced(choice_axiom,[])).
% 19.79/2.99  
% 19.79/2.99  fof(f43,plain,(
% 19.79/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.79/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f42])).
% 19.79/2.99  
% 19.79/2.99  fof(f65,plain,(
% 19.79/2.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.79/2.99    inference(cnf_transformation,[],[f43])).
% 19.79/2.99  
% 19.79/2.99  fof(f21,axiom,(
% 19.79/2.99    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 19.79/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.79/2.99  
% 19.79/2.99  fof(f34,plain,(
% 19.79/2.99    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 19.79/2.99    inference(ennf_transformation,[],[f21])).
% 19.79/2.99  
% 19.79/2.99  fof(f87,plain,(
% 19.79/2.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0) )),
% 19.79/2.99    inference(cnf_transformation,[],[f34])).
% 19.79/2.99  
% 19.79/2.99  cnf(c_0,plain,
% 19.79/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.79/2.99      inference(cnf_transformation,[],[f97]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_36,negated_conjecture,
% 19.79/2.99      ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
% 19.79/2.99      inference(cnf_transformation,[],[f91]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_31,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
% 19.79/2.99      inference(cnf_transformation,[],[f90]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1413,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK6,X0)) = k2_zfmisc_1(sK6,k4_xboole_0(sK7,X0)) ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_36,c_31]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_32,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
% 19.79/2.99      inference(cnf_transformation,[],[f89]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_5499,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,sK6),sK5) ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_1413,c_32]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_7,plain,
% 19.79/2.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 19.79/2.99      inference(cnf_transformation,[],[f98]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_21,plain,
% 19.79/2.99      ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 19.79/2.99      inference(cnf_transformation,[],[f102]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1818,plain,
% 19.79/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_7,c_21]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1778,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_32,c_0]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1782,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
% 19.79/2.99      inference(light_normalisation,[status(thm)],[c_1778,c_32]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_12186,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_1818,c_1782]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_25,plain,
% 19.79/2.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.79/2.99      inference(cnf_transformation,[],[f107]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_17,plain,
% 19.79/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.79/2.99      inference(cnf_transformation,[],[f101]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_20,plain,
% 19.79/2.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.79/2.99      inference(cnf_transformation,[],[f74]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_794,plain,
% 19.79/2.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.79/2.99      inference(light_normalisation,[status(thm)],[c_17,c_20]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_12355,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X2,X0)),X1)) = k1_xboole_0 ),
% 19.79/2.99      inference(demodulation,
% 19.79/2.99                [status(thm)],
% 19.79/2.99                [c_12186,c_25,c_31,c_32,c_794]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_12855,plain,
% 19.79/2.99      ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),X2) = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_12355,c_32]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_30,plain,
% 19.79/2.99      ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
% 19.79/2.99      inference(cnf_transformation,[],[f103]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_13101,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X3))) = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_12855,c_30]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_52375,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(sK6,X0),k4_xboole_0(k2_zfmisc_1(sK6,X0),k2_zfmisc_1(sK6,k4_xboole_0(sK7,sK5)))) = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_5499,c_13101]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_52972,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK6,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK7,sK5)))) = k1_xboole_0 ),
% 19.79/2.99      inference(demodulation,[status(thm)],[c_52375,c_31]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_68628,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,k4_xboole_0(sK5,k4_xboole_0(sK5,sK7)))) = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_0,c_52972]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1770,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(X0,sK7)) = k2_zfmisc_1(k4_xboole_0(sK6,X0),sK7) ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_36,c_32]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_6689,plain,
% 19.79/2.99      ( k2_zfmisc_1(k4_xboole_0(sK6,sK4),sK7) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK7)) ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_1770,c_31]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_52377,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(sK4,X0),k4_xboole_0(k2_zfmisc_1(sK4,X0),k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK7)))) = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_6689,c_13101]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_52967,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK5,sK7)))) = k1_xboole_0 ),
% 19.79/2.99      inference(demodulation,[status(thm)],[c_52377,c_31]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_53145,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK4,k4_xboole_0(k4_xboole_0(sK5,sK7),k1_xboole_0)) = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_794,c_52967]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_53584,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK7)) = k1_xboole_0 ),
% 19.79/2.99      inference(demodulation,[status(thm)],[c_53145,c_20]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_27,plain,
% 19.79/2.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 19.79/2.99      | k1_xboole_0 = X0
% 19.79/2.99      | k1_xboole_0 = X1 ),
% 19.79/2.99      inference(cnf_transformation,[],[f83]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_53867,plain,
% 19.79/2.99      ( k4_xboole_0(sK5,sK7) = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_53584,c_27]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_35,negated_conjecture,
% 19.79/2.99      ( k1_xboole_0 != sK4 ),
% 19.79/2.99      inference(cnf_transformation,[],[f92]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_44,plain,
% 19.79/2.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.79/2.99      | k1_xboole_0 = k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_27]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_26,plain,
% 19.79/2.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.79/2.99      inference(cnf_transformation,[],[f108]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_45,plain,
% 19.79/2.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_26]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_280,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1001,plain,
% 19.79/2.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_280]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1002,plain,
% 19.79/2.99      ( sK4 != k1_xboole_0
% 19.79/2.99      | k1_xboole_0 = sK4
% 19.79/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_1001]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_55707,plain,
% 19.79/2.99      ( k4_xboole_0(sK5,sK7) = k1_xboole_0 ),
% 19.79/2.99      inference(global_propositional_subsumption,
% 19.79/2.99                [status(thm)],
% 19.79/2.99                [c_53867,c_35,c_44,c_45,c_1002]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_69151,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,k4_xboole_0(sK5,k1_xboole_0))) = k1_xboole_0 ),
% 19.79/2.99      inference(light_normalisation,[status(thm)],[c_68628,c_55707]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_69152,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,sK5)) = k1_xboole_0 ),
% 19.79/2.99      inference(demodulation,[status(thm)],[c_69151,c_20]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_69329,plain,
% 19.79/2.99      ( k4_xboole_0(sK7,sK5) = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_69152,c_27]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_73671,plain,
% 19.79/2.99      ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK7)) = k4_xboole_0(sK7,k1_xboole_0)
% 19.79/2.99      | sK6 = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_69329,c_0]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_73977,plain,
% 19.79/2.99      ( k4_xboole_0(sK7,k1_xboole_0) = k4_xboole_0(sK5,k1_xboole_0)
% 19.79/2.99      | sK6 = k1_xboole_0 ),
% 19.79/2.99      inference(light_normalisation,[status(thm)],[c_73671,c_55707]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_73978,plain,
% 19.79/2.99      ( sK6 = k1_xboole_0 | sK7 = sK5 ),
% 19.79/2.99      inference(demodulation,[status(thm)],[c_73977,c_20]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_75155,plain,
% 19.79/2.99      ( k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(sK4,sK5) | sK7 = sK5 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_73978,c_36]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_75158,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK4,sK5) = k1_xboole_0 | sK7 = sK5 ),
% 19.79/2.99      inference(demodulation,[status(thm)],[c_75155,c_26]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_34,negated_conjecture,
% 19.79/2.99      ( k1_xboole_0 != sK5 ),
% 19.79/2.99      inference(cnf_transformation,[],[f93]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_982,plain,
% 19.79/2.99      ( k2_zfmisc_1(X0,sK5) != k1_xboole_0
% 19.79/2.99      | k1_xboole_0 = X0
% 19.79/2.99      | k1_xboole_0 = sK5 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_27]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1204,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK4,sK5) != k1_xboole_0
% 19.79/2.99      | k1_xboole_0 = sK4
% 19.79/2.99      | k1_xboole_0 = sK5 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_982]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_76825,plain,
% 19.79/2.99      ( sK7 = sK5 ),
% 19.79/2.99      inference(global_propositional_subsumption,
% 19.79/2.99                [status(thm)],
% 19.79/2.99                [c_75158,c_35,c_34,c_1204]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_33,negated_conjecture,
% 19.79/2.99      ( sK4 != sK6 | sK5 != sK7 ),
% 19.79/2.99      inference(cnf_transformation,[],[f94]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_76867,plain,
% 19.79/2.99      ( sK6 != sK4 | sK5 != sK5 ),
% 19.79/2.99      inference(demodulation,[status(thm)],[c_76825,c_33]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_76869,plain,
% 19.79/2.99      ( sK6 != sK4 ),
% 19.79/2.99      inference(equality_resolution_simp,[status(thm)],[c_76867]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1416,plain,
% 19.79/2.99      ( k4_xboole_0(k2_zfmisc_1(sK6,X0),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK6,k4_xboole_0(X0,sK7)) ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_36,c_31]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_5913,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK6,k4_xboole_0(sK5,sK7)) = k2_zfmisc_1(k4_xboole_0(sK6,sK4),sK5) ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_1416,c_32]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_55716,plain,
% 19.79/2.99      ( k2_zfmisc_1(k4_xboole_0(sK6,sK4),sK5) = k2_zfmisc_1(sK6,k1_xboole_0) ),
% 19.79/2.99      inference(demodulation,[status(thm)],[c_55707,c_5913]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_55718,plain,
% 19.79/2.99      ( k2_zfmisc_1(k4_xboole_0(sK6,sK4),sK5) = k1_xboole_0 ),
% 19.79/2.99      inference(demodulation,[status(thm)],[c_55716,c_25]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_56271,plain,
% 19.79/2.99      ( k4_xboole_0(sK6,sK4) = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_55718,c_27]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_23,plain,
% 19.79/2.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 19.79/2.99      inference(cnf_transformation,[],[f79]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_50,plain,
% 19.79/2.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 19.79/2.99      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_23]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_22,plain,
% 19.79/2.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.79/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_52,plain,
% 19.79/2.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_22]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_16,plain,
% 19.79/2.99      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 19.79/2.99      inference(cnf_transformation,[],[f69]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_59,plain,
% 19.79/2.99      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 19.79/2.99      | r1_tarski(X0,X1) = iProver_top ),
% 19.79/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_61,plain,
% 19.79/2.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.79/2.99      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_59]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_999,plain,
% 19.79/2.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_280]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1000,plain,
% 19.79/2.99      ( sK5 != k1_xboole_0
% 19.79/2.99      | k1_xboole_0 = sK5
% 19.79/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_999]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_18,plain,
% 19.79/2.99      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 19.79/2.99      inference(cnf_transformation,[],[f72]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1207,plain,
% 19.79/2.99      ( k4_xboole_0(sK5,X0) != k4_xboole_0(X0,sK5) | sK5 = X0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_18]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1208,plain,
% 19.79/2.99      ( k4_xboole_0(sK5,k1_xboole_0) != k4_xboole_0(k1_xboole_0,sK5)
% 19.79/2.99      | sK5 = k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_1207]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1531,plain,
% 19.79/2.99      ( k4_xboole_0(X0,sK5) != X1
% 19.79/2.99      | k4_xboole_0(sK5,X0) != X1
% 19.79/2.99      | k4_xboole_0(sK5,X0) = k4_xboole_0(X0,sK5) ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_280]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1532,plain,
% 19.79/2.99      ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK5)
% 19.79/2.99      | k4_xboole_0(sK5,k1_xboole_0) != k1_xboole_0
% 19.79/2.99      | k4_xboole_0(k1_xboole_0,sK5) != k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_1531]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_3,plain,
% 19.79/2.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 19.79/2.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.79/2.99      | k4_xboole_0(X0,X1) = X2 ),
% 19.79/2.99      inference(cnf_transformation,[],[f58]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1639,plain,
% 19.79/2.99      ( r2_hidden(sK0(k1_xboole_0,sK5,X0),X0)
% 19.79/2.99      | r2_hidden(sK0(k1_xboole_0,sK5,X0),k1_xboole_0)
% 19.79/2.99      | k4_xboole_0(k1_xboole_0,sK5) = X0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_3]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1646,plain,
% 19.79/2.99      ( r2_hidden(sK0(k1_xboole_0,sK5,k1_xboole_0),k1_xboole_0)
% 19.79/2.99      | k4_xboole_0(k1_xboole_0,sK5) = k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_1639]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_15,plain,
% 19.79/2.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.79/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_2498,plain,
% 19.79/2.99      ( ~ r1_tarski(sK5,k1_xboole_0)
% 19.79/2.99      | k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0 ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_15]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_2499,plain,
% 19.79/2.99      ( k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0
% 19.79/2.99      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 19.79/2.99      inference(predicate_to_equality,[status(thm)],[c_2498]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_9,plain,
% 19.79/2.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 19.79/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_5765,plain,
% 19.79/2.99      ( ~ r1_xboole_0(k1_xboole_0,X0)
% 19.79/2.99      | ~ r2_hidden(sK0(k1_xboole_0,sK5,X1),X0)
% 19.79/2.99      | ~ r2_hidden(sK0(k1_xboole_0,sK5,X1),k1_xboole_0) ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_9]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_5767,plain,
% 19.79/2.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 19.79/2.99      | ~ r2_hidden(sK0(k1_xboole_0,sK5,k1_xboole_0),k1_xboole_0) ),
% 19.79/2.99      inference(instantiation,[status(thm)],[c_5765]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_28,plain,
% 19.79/2.99      ( r1_tarski(X0,X1)
% 19.79/2.99      | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
% 19.79/2.99      | k1_xboole_0 = X2 ),
% 19.79/2.99      inference(cnf_transformation,[],[f87]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_759,plain,
% 19.79/2.99      ( k1_xboole_0 = X0
% 19.79/2.99      | r1_tarski(X1,X2) = iProver_top
% 19.79/2.99      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
% 19.79/2.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_1016,plain,
% 19.79/2.99      ( k1_xboole_0 = X0
% 19.79/2.99      | r1_tarski(X1,k1_xboole_0) = iProver_top
% 19.79/2.99      | r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) != iProver_top ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_25,c_759]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_56270,plain,
% 19.79/2.99      ( k4_xboole_0(sK6,sK4) = k1_xboole_0
% 19.79/2.99      | r1_tarski(sK5,k1_xboole_0) = iProver_top
% 19.79/2.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_55718,c_1016]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_62693,plain,
% 19.79/2.99      ( k4_xboole_0(sK6,sK4) = k1_xboole_0 ),
% 19.79/2.99      inference(global_propositional_subsumption,
% 19.79/2.99                [status(thm)],
% 19.79/2.99                [c_56271,c_34,c_44,c_45,c_50,c_52,c_61,c_1000,c_1208,
% 19.79/2.99                 c_1532,c_1646,c_2499,c_5767,c_56270]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_62756,plain,
% 19.79/2.99      ( k4_xboole_0(sK4,sK6) != k1_xboole_0 | sK6 = sK4 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_62693,c_18]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(c_5800,plain,
% 19.79/2.99      ( k2_zfmisc_1(sK6,k4_xboole_0(sK7,sK5)) != k1_xboole_0
% 19.79/2.99      | k4_xboole_0(sK4,sK6) = k1_xboole_0
% 19.79/2.99      | sK5 = k1_xboole_0 ),
% 19.79/2.99      inference(superposition,[status(thm)],[c_5499,c_27]) ).
% 19.79/2.99  
% 19.79/2.99  cnf(contradiction,plain,
% 19.79/2.99      ( $false ),
% 19.79/2.99      inference(minisat,
% 19.79/2.99                [status(thm)],
% 19.79/2.99                [c_76869,c_69152,c_62756,c_5800,c_1000,c_45,c_44,c_34]) ).
% 19.79/2.99  
% 19.79/2.99  
% 19.79/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.79/2.99  
% 19.79/2.99  ------                               Statistics
% 19.79/2.99  
% 19.79/2.99  ------ Selected
% 19.79/2.99  
% 19.79/2.99  total_time:                             2.261
% 19.79/2.99  
%------------------------------------------------------------------------------
