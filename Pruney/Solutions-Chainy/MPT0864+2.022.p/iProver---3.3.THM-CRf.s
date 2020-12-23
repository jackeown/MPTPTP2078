%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:50 EST 2020

% Result     : Theorem 6.81s
% Output     : CNFRefutation 6.81s
% Verified   : 
% Statistics : Number of formulae       :  176 (2334 expanded)
%              Number of clauses        :   85 ( 674 expanded)
%              Number of leaves         :   23 ( 573 expanded)
%              Depth                    :   26
%              Number of atoms          :  559 (7708 expanded)
%              Number of equality atoms :  319 (5017 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f111,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f98])).

fof(f112,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f111])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f40])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f116,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f74])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f82,f90])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f81,f90])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f21,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK7,sK8) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK6) = sK6
        | k1_mcart_1(sK6) = sK6 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK6 ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( k2_mcart_1(sK6) = sK6
      | k1_mcart_1(sK6) = sK6 )
    & k4_tarski(sK7,sK8) = sK6 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f21,f49,f48])).

fof(f89,plain,
    ( k2_mcart_1(sK6) = sK6
    | k1_mcart_1(sK6) = sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    k4_tarski(sK7,sK8) = sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f43])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f46])).

fof(f85,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f90])).

fof(f110,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f87,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f65,f71])).

fof(f113,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f99])).

fof(f114,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f113])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f86,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f102,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) != k1_enumset1(X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f75,f90,f90,f90])).

fof(f118,plain,(
    ! [X1] : k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) != k1_enumset1(X1,X1,X1) ),
    inference(equality_resolution,[],[f102])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1177,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1192,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1173,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5095,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k2_mcart_1(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1173])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1172,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4571,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1172])).

cnf(c_5123,plain,
    ( k1_mcart_1(k2_mcart_1(X0)) = X1
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_4571])).

cnf(c_5465,plain,
    ( k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,X0))) = X1
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_5123])).

cnf(c_35,negated_conjecture,
    ( k1_mcart_1(sK6) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,negated_conjecture,
    ( k4_tarski(sK7,sK8) = sK6 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_31,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1449,plain,
    ( k1_mcart_1(sK6) = sK7 ),
    inference(superposition,[status(thm)],[c_36,c_31])).

cnf(c_1451,plain,
    ( k2_mcart_1(sK6) = sK6
    | sK7 = sK6 ),
    inference(superposition,[status(thm)],[c_35,c_1449])).

cnf(c_30,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1429,plain,
    ( k2_mcart_1(sK6) = sK8 ),
    inference(superposition,[status(thm)],[c_36,c_30])).

cnf(c_1453,plain,
    ( sK8 = sK6
    | sK7 = sK6 ),
    inference(demodulation,[status(thm)],[c_1451,c_1429])).

cnf(c_24,plain,
    ( m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_232,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_392,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != X2
    | sK4(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_233])).

cnf(c_393,plain,
    ( r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_1168,plain,
    ( r1_tarski(sK4(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1191,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6446,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_1191])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1174,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8872,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(X1,k2_mcart_1(X0)) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6446,c_1174])).

cnf(c_10257,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4(k1_zfmisc_1(k2_mcart_1(X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1168,c_8872])).

cnf(c_11737,plain,
    ( r2_hidden(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4(k1_zfmisc_1(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1429,c_10257])).

cnf(c_11761,plain,
    ( sK7 = sK6
    | r2_hidden(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4(k1_zfmisc_1(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_11737])).

cnf(c_16936,plain,
    ( k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6))))) = X0
    | sK7 = sK6
    | r2_hidden(sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5465,c_11761])).

cnf(c_34,plain,
    ( r2_hidden(sK5(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1169,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK5(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1181,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2719,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK5(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1169,c_1181])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X2,X0) != sK5(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1171,plain,
    ( k4_tarski(X0,X1) != sK5(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2520,plain,
    ( sK5(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_1171])).

cnf(c_16988,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(sK8,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2719,c_2520])).

cnf(c_18102,plain,
    ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0
    | r2_hidden(sK8,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_16988])).

cnf(c_18816,plain,
    ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0
    | sK7 = sK6
    | r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_18102])).

cnf(c_17,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1176,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19009,plain,
    ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0
    | sK7 = sK6 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18816,c_1176])).

cnf(c_19033,plain,
    ( sK7 = sK6
    | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19009,c_1176])).

cnf(c_19614,plain,
    ( sK7 = sK6
    | k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6))))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16936,c_19033])).

cnf(c_19615,plain,
    ( k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6))))) = X0
    | sK7 = sK6 ),
    inference(renaming,[status(thm)],[c_19614])).

cnf(c_19685,plain,
    ( sK7 = sK6
    | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19615,c_1176])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1186,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19710,plain,
    ( sK7 = sK6
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19615,c_1186])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1187,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19712,plain,
    ( sK7 = sK6
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19615,c_1187])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1185,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19713,plain,
    ( sK7 = sK6
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19615,c_1185])).

cnf(c_19811,plain,
    ( sK7 = sK6
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19712,c_19713])).

cnf(c_19818,plain,
    ( sK7 = sK6
    | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19710,c_19811])).

cnf(c_19905,plain,
    ( sK7 = sK6 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19685,c_19818])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X0,X2) != sK5(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1170,plain,
    ( k4_tarski(X0,X1) != sK5(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1677,plain,
    ( sK5(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_1170])).

cnf(c_16990,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(sK7,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2719,c_1677])).

cnf(c_20979,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(sK6,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19905,c_16990])).

cnf(c_13698,plain,
    ( ~ r2_hidden(sK6,k1_enumset1(X0,X0,X0))
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13699,plain,
    ( sK6 = X0
    | r2_hidden(sK6,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13698])).

cnf(c_22199,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | r2_hidden(sK6,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20979,c_13699])).

cnf(c_22207,plain,
    ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1177,c_22199])).

cnf(c_23,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)) != k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_22690,plain,
    ( k1_enumset1(sK6,sK6,sK6) != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22207,c_23])).

cnf(c_22760,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_22690,c_22207])).

cnf(c_3787,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK5(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1185])).

cnf(c_4809,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK5(k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1186])).

cnf(c_17142,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3787,c_4809])).

cnf(c_17320,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17142])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22760,c_17320])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:44:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 6.81/1.54  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.81/1.54  
% 6.81/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.81/1.54  
% 6.81/1.54  ------  iProver source info
% 6.81/1.54  
% 6.81/1.54  git: date: 2020-06-30 10:37:57 +0100
% 6.81/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.81/1.54  git: non_committed_changes: false
% 6.81/1.54  git: last_make_outside_of_git: false
% 6.81/1.54  
% 6.81/1.54  ------ 
% 6.81/1.54  
% 6.81/1.54  ------ Input Options
% 6.81/1.54  
% 6.81/1.54  --out_options                           all
% 6.81/1.54  --tptp_safe_out                         true
% 6.81/1.54  --problem_path                          ""
% 6.81/1.54  --include_path                          ""
% 6.81/1.54  --clausifier                            res/vclausify_rel
% 6.81/1.54  --clausifier_options                    --mode clausify
% 6.81/1.54  --stdin                                 false
% 6.81/1.54  --stats_out                             all
% 6.81/1.54  
% 6.81/1.54  ------ General Options
% 6.81/1.54  
% 6.81/1.54  --fof                                   false
% 6.81/1.54  --time_out_real                         305.
% 6.81/1.54  --time_out_virtual                      -1.
% 6.81/1.54  --symbol_type_check                     false
% 6.81/1.54  --clausify_out                          false
% 6.81/1.54  --sig_cnt_out                           false
% 6.81/1.54  --trig_cnt_out                          false
% 6.81/1.54  --trig_cnt_out_tolerance                1.
% 6.81/1.54  --trig_cnt_out_sk_spl                   false
% 6.81/1.54  --abstr_cl_out                          false
% 6.81/1.54  
% 6.81/1.54  ------ Global Options
% 6.81/1.54  
% 6.81/1.54  --schedule                              default
% 6.81/1.54  --add_important_lit                     false
% 6.81/1.54  --prop_solver_per_cl                    1000
% 6.81/1.54  --min_unsat_core                        false
% 6.81/1.54  --soft_assumptions                      false
% 6.81/1.54  --soft_lemma_size                       3
% 6.81/1.54  --prop_impl_unit_size                   0
% 6.81/1.54  --prop_impl_unit                        []
% 6.81/1.54  --share_sel_clauses                     true
% 6.81/1.54  --reset_solvers                         false
% 6.81/1.54  --bc_imp_inh                            [conj_cone]
% 6.81/1.54  --conj_cone_tolerance                   3.
% 6.81/1.54  --extra_neg_conj                        none
% 6.81/1.54  --large_theory_mode                     true
% 6.81/1.54  --prolific_symb_bound                   200
% 6.81/1.54  --lt_threshold                          2000
% 6.81/1.54  --clause_weak_htbl                      true
% 6.81/1.54  --gc_record_bc_elim                     false
% 6.81/1.54  
% 6.81/1.54  ------ Preprocessing Options
% 6.81/1.54  
% 6.81/1.54  --preprocessing_flag                    true
% 6.81/1.54  --time_out_prep_mult                    0.1
% 6.81/1.54  --splitting_mode                        input
% 6.81/1.54  --splitting_grd                         true
% 6.81/1.54  --splitting_cvd                         false
% 6.81/1.54  --splitting_cvd_svl                     false
% 6.81/1.54  --splitting_nvd                         32
% 6.81/1.54  --sub_typing                            true
% 6.81/1.54  --prep_gs_sim                           true
% 6.81/1.54  --prep_unflatten                        true
% 6.81/1.54  --prep_res_sim                          true
% 6.81/1.54  --prep_upred                            true
% 6.81/1.54  --prep_sem_filter                       exhaustive
% 6.81/1.54  --prep_sem_filter_out                   false
% 6.81/1.54  --pred_elim                             true
% 6.81/1.54  --res_sim_input                         true
% 6.81/1.54  --eq_ax_congr_red                       true
% 6.81/1.54  --pure_diseq_elim                       true
% 6.81/1.54  --brand_transform                       false
% 6.81/1.54  --non_eq_to_eq                          false
% 6.81/1.54  --prep_def_merge                        true
% 6.81/1.54  --prep_def_merge_prop_impl              false
% 6.81/1.54  --prep_def_merge_mbd                    true
% 6.81/1.54  --prep_def_merge_tr_red                 false
% 6.81/1.54  --prep_def_merge_tr_cl                  false
% 6.81/1.54  --smt_preprocessing                     true
% 6.81/1.54  --smt_ac_axioms                         fast
% 6.81/1.54  --preprocessed_out                      false
% 6.81/1.54  --preprocessed_stats                    false
% 6.81/1.54  
% 6.81/1.54  ------ Abstraction refinement Options
% 6.81/1.54  
% 6.81/1.54  --abstr_ref                             []
% 6.81/1.54  --abstr_ref_prep                        false
% 6.81/1.54  --abstr_ref_until_sat                   false
% 6.81/1.54  --abstr_ref_sig_restrict                funpre
% 6.81/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.81/1.54  --abstr_ref_under                       []
% 6.81/1.54  
% 6.81/1.54  ------ SAT Options
% 6.81/1.54  
% 6.81/1.54  --sat_mode                              false
% 6.81/1.54  --sat_fm_restart_options                ""
% 6.81/1.54  --sat_gr_def                            false
% 6.81/1.54  --sat_epr_types                         true
% 6.81/1.54  --sat_non_cyclic_types                  false
% 6.81/1.54  --sat_finite_models                     false
% 6.81/1.54  --sat_fm_lemmas                         false
% 6.81/1.54  --sat_fm_prep                           false
% 6.81/1.54  --sat_fm_uc_incr                        true
% 6.81/1.54  --sat_out_model                         small
% 6.81/1.54  --sat_out_clauses                       false
% 6.81/1.54  
% 6.81/1.54  ------ QBF Options
% 6.81/1.54  
% 6.81/1.54  --qbf_mode                              false
% 6.81/1.54  --qbf_elim_univ                         false
% 6.81/1.54  --qbf_dom_inst                          none
% 6.81/1.54  --qbf_dom_pre_inst                      false
% 6.81/1.54  --qbf_sk_in                             false
% 6.81/1.54  --qbf_pred_elim                         true
% 6.81/1.54  --qbf_split                             512
% 6.81/1.54  
% 6.81/1.54  ------ BMC1 Options
% 6.81/1.54  
% 6.81/1.54  --bmc1_incremental                      false
% 6.81/1.54  --bmc1_axioms                           reachable_all
% 6.81/1.54  --bmc1_min_bound                        0
% 6.81/1.54  --bmc1_max_bound                        -1
% 6.81/1.54  --bmc1_max_bound_default                -1
% 6.81/1.54  --bmc1_symbol_reachability              true
% 6.81/1.54  --bmc1_property_lemmas                  false
% 6.81/1.54  --bmc1_k_induction                      false
% 6.81/1.54  --bmc1_non_equiv_states                 false
% 6.81/1.54  --bmc1_deadlock                         false
% 6.81/1.54  --bmc1_ucm                              false
% 6.81/1.54  --bmc1_add_unsat_core                   none
% 6.81/1.54  --bmc1_unsat_core_children              false
% 6.81/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.81/1.54  --bmc1_out_stat                         full
% 6.81/1.54  --bmc1_ground_init                      false
% 6.81/1.54  --bmc1_pre_inst_next_state              false
% 6.81/1.54  --bmc1_pre_inst_state                   false
% 6.81/1.54  --bmc1_pre_inst_reach_state             false
% 6.81/1.54  --bmc1_out_unsat_core                   false
% 6.81/1.54  --bmc1_aig_witness_out                  false
% 6.81/1.54  --bmc1_verbose                          false
% 6.81/1.54  --bmc1_dump_clauses_tptp                false
% 6.81/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.81/1.54  --bmc1_dump_file                        -
% 6.81/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.81/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.81/1.54  --bmc1_ucm_extend_mode                  1
% 6.81/1.54  --bmc1_ucm_init_mode                    2
% 6.81/1.54  --bmc1_ucm_cone_mode                    none
% 6.81/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.81/1.54  --bmc1_ucm_relax_model                  4
% 6.81/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.81/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.81/1.54  --bmc1_ucm_layered_model                none
% 6.81/1.54  --bmc1_ucm_max_lemma_size               10
% 6.81/1.54  
% 6.81/1.54  ------ AIG Options
% 6.81/1.54  
% 6.81/1.54  --aig_mode                              false
% 6.81/1.54  
% 6.81/1.54  ------ Instantiation Options
% 6.81/1.54  
% 6.81/1.54  --instantiation_flag                    true
% 6.81/1.54  --inst_sos_flag                         false
% 6.81/1.54  --inst_sos_phase                        true
% 6.81/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.81/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.81/1.54  --inst_lit_sel_side                     num_symb
% 6.81/1.54  --inst_solver_per_active                1400
% 6.81/1.54  --inst_solver_calls_frac                1.
% 6.81/1.54  --inst_passive_queue_type               priority_queues
% 6.81/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.81/1.54  --inst_passive_queues_freq              [25;2]
% 6.81/1.54  --inst_dismatching                      true
% 6.81/1.54  --inst_eager_unprocessed_to_passive     true
% 6.81/1.54  --inst_prop_sim_given                   true
% 6.81/1.54  --inst_prop_sim_new                     false
% 6.81/1.54  --inst_subs_new                         false
% 6.81/1.54  --inst_eq_res_simp                      false
% 6.81/1.54  --inst_subs_given                       false
% 6.81/1.54  --inst_orphan_elimination               true
% 6.81/1.54  --inst_learning_loop_flag               true
% 6.81/1.54  --inst_learning_start                   3000
% 6.81/1.54  --inst_learning_factor                  2
% 6.81/1.54  --inst_start_prop_sim_after_learn       3
% 6.81/1.54  --inst_sel_renew                        solver
% 6.81/1.54  --inst_lit_activity_flag                true
% 6.81/1.54  --inst_restr_to_given                   false
% 6.81/1.54  --inst_activity_threshold               500
% 6.81/1.54  --inst_out_proof                        true
% 6.81/1.54  
% 6.81/1.54  ------ Resolution Options
% 6.81/1.54  
% 6.81/1.54  --resolution_flag                       true
% 6.81/1.54  --res_lit_sel                           adaptive
% 6.81/1.54  --res_lit_sel_side                      none
% 6.81/1.54  --res_ordering                          kbo
% 6.81/1.54  --res_to_prop_solver                    active
% 6.81/1.54  --res_prop_simpl_new                    false
% 6.81/1.54  --res_prop_simpl_given                  true
% 6.81/1.54  --res_passive_queue_type                priority_queues
% 6.81/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.81/1.54  --res_passive_queues_freq               [15;5]
% 6.81/1.54  --res_forward_subs                      full
% 6.81/1.54  --res_backward_subs                     full
% 6.81/1.54  --res_forward_subs_resolution           true
% 6.81/1.54  --res_backward_subs_resolution          true
% 6.81/1.54  --res_orphan_elimination                true
% 6.81/1.54  --res_time_limit                        2.
% 6.81/1.54  --res_out_proof                         true
% 6.81/1.54  
% 6.81/1.54  ------ Superposition Options
% 6.81/1.54  
% 6.81/1.54  --superposition_flag                    true
% 6.81/1.54  --sup_passive_queue_type                priority_queues
% 6.81/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.81/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.81/1.54  --demod_completeness_check              fast
% 6.81/1.54  --demod_use_ground                      true
% 6.81/1.54  --sup_to_prop_solver                    passive
% 6.81/1.54  --sup_prop_simpl_new                    true
% 6.81/1.54  --sup_prop_simpl_given                  true
% 6.81/1.54  --sup_fun_splitting                     false
% 6.81/1.54  --sup_smt_interval                      50000
% 6.81/1.54  
% 6.81/1.54  ------ Superposition Simplification Setup
% 6.81/1.54  
% 6.81/1.54  --sup_indices_passive                   []
% 6.81/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.81/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.54  --sup_full_bw                           [BwDemod]
% 6.81/1.54  --sup_immed_triv                        [TrivRules]
% 6.81/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.81/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.54  --sup_immed_bw_main                     []
% 6.81/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.81/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.54  
% 6.81/1.54  ------ Combination Options
% 6.81/1.54  
% 6.81/1.54  --comb_res_mult                         3
% 6.81/1.54  --comb_sup_mult                         2
% 6.81/1.54  --comb_inst_mult                        10
% 6.81/1.54  
% 6.81/1.54  ------ Debug Options
% 6.81/1.54  
% 6.81/1.54  --dbg_backtrace                         false
% 6.81/1.54  --dbg_dump_prop_clauses                 false
% 6.81/1.54  --dbg_dump_prop_clauses_file            -
% 6.81/1.54  --dbg_out_stat                          false
% 6.81/1.54  ------ Parsing...
% 6.81/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.81/1.54  
% 6.81/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.81/1.54  
% 6.81/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.81/1.54  
% 6.81/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.81/1.54  ------ Proving...
% 6.81/1.54  ------ Problem Properties 
% 6.81/1.54  
% 6.81/1.54  
% 6.81/1.54  clauses                                 35
% 6.81/1.54  conjectures                             2
% 6.81/1.54  EPR                                     2
% 6.81/1.54  Horn                                    23
% 6.81/1.54  unary                                   10
% 6.81/1.54  binary                                  11
% 6.81/1.54  lits                                    76
% 6.81/1.54  lits eq                                 36
% 6.81/1.54  fd_pure                                 0
% 6.81/1.54  fd_pseudo                               0
% 6.81/1.54  fd_cond                                 4
% 6.81/1.54  fd_pseudo_cond                          10
% 6.81/1.54  AC symbols                              0
% 6.81/1.54  
% 6.81/1.54  ------ Schedule dynamic 5 is on 
% 6.81/1.54  
% 6.81/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.81/1.54  
% 6.81/1.54  
% 6.81/1.54  ------ 
% 6.81/1.54  Current options:
% 6.81/1.54  ------ 
% 6.81/1.54  
% 6.81/1.54  ------ Input Options
% 6.81/1.54  
% 6.81/1.54  --out_options                           all
% 6.81/1.54  --tptp_safe_out                         true
% 6.81/1.54  --problem_path                          ""
% 6.81/1.54  --include_path                          ""
% 6.81/1.54  --clausifier                            res/vclausify_rel
% 6.81/1.54  --clausifier_options                    --mode clausify
% 6.81/1.54  --stdin                                 false
% 6.81/1.54  --stats_out                             all
% 6.81/1.54  
% 6.81/1.54  ------ General Options
% 6.81/1.54  
% 6.81/1.54  --fof                                   false
% 6.81/1.54  --time_out_real                         305.
% 6.81/1.54  --time_out_virtual                      -1.
% 6.81/1.54  --symbol_type_check                     false
% 6.81/1.54  --clausify_out                          false
% 6.81/1.54  --sig_cnt_out                           false
% 6.81/1.54  --trig_cnt_out                          false
% 6.81/1.54  --trig_cnt_out_tolerance                1.
% 6.81/1.54  --trig_cnt_out_sk_spl                   false
% 6.81/1.54  --abstr_cl_out                          false
% 6.81/1.54  
% 6.81/1.54  ------ Global Options
% 6.81/1.54  
% 6.81/1.54  --schedule                              default
% 6.81/1.54  --add_important_lit                     false
% 6.81/1.54  --prop_solver_per_cl                    1000
% 6.81/1.54  --min_unsat_core                        false
% 6.81/1.54  --soft_assumptions                      false
% 6.81/1.54  --soft_lemma_size                       3
% 6.81/1.54  --prop_impl_unit_size                   0
% 6.81/1.54  --prop_impl_unit                        []
% 6.81/1.54  --share_sel_clauses                     true
% 6.81/1.54  --reset_solvers                         false
% 6.81/1.54  --bc_imp_inh                            [conj_cone]
% 6.81/1.54  --conj_cone_tolerance                   3.
% 6.81/1.54  --extra_neg_conj                        none
% 6.81/1.54  --large_theory_mode                     true
% 6.81/1.54  --prolific_symb_bound                   200
% 6.81/1.54  --lt_threshold                          2000
% 6.81/1.54  --clause_weak_htbl                      true
% 6.81/1.54  --gc_record_bc_elim                     false
% 6.81/1.54  
% 6.81/1.54  ------ Preprocessing Options
% 6.81/1.54  
% 6.81/1.54  --preprocessing_flag                    true
% 6.81/1.54  --time_out_prep_mult                    0.1
% 6.81/1.54  --splitting_mode                        input
% 6.81/1.54  --splitting_grd                         true
% 6.81/1.54  --splitting_cvd                         false
% 6.81/1.54  --splitting_cvd_svl                     false
% 6.81/1.54  --splitting_nvd                         32
% 6.81/1.54  --sub_typing                            true
% 6.81/1.54  --prep_gs_sim                           true
% 6.81/1.54  --prep_unflatten                        true
% 6.81/1.54  --prep_res_sim                          true
% 6.81/1.54  --prep_upred                            true
% 6.81/1.54  --prep_sem_filter                       exhaustive
% 6.81/1.54  --prep_sem_filter_out                   false
% 6.81/1.54  --pred_elim                             true
% 6.81/1.54  --res_sim_input                         true
% 6.81/1.54  --eq_ax_congr_red                       true
% 6.81/1.54  --pure_diseq_elim                       true
% 6.81/1.54  --brand_transform                       false
% 6.81/1.54  --non_eq_to_eq                          false
% 6.81/1.54  --prep_def_merge                        true
% 6.81/1.54  --prep_def_merge_prop_impl              false
% 6.81/1.54  --prep_def_merge_mbd                    true
% 6.81/1.54  --prep_def_merge_tr_red                 false
% 6.81/1.54  --prep_def_merge_tr_cl                  false
% 6.81/1.54  --smt_preprocessing                     true
% 6.81/1.54  --smt_ac_axioms                         fast
% 6.81/1.54  --preprocessed_out                      false
% 6.81/1.54  --preprocessed_stats                    false
% 6.81/1.54  
% 6.81/1.54  ------ Abstraction refinement Options
% 6.81/1.54  
% 6.81/1.54  --abstr_ref                             []
% 6.81/1.54  --abstr_ref_prep                        false
% 6.81/1.54  --abstr_ref_until_sat                   false
% 6.81/1.54  --abstr_ref_sig_restrict                funpre
% 6.81/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.81/1.54  --abstr_ref_under                       []
% 6.81/1.54  
% 6.81/1.54  ------ SAT Options
% 6.81/1.54  
% 6.81/1.54  --sat_mode                              false
% 6.81/1.54  --sat_fm_restart_options                ""
% 6.81/1.54  --sat_gr_def                            false
% 6.81/1.54  --sat_epr_types                         true
% 6.81/1.54  --sat_non_cyclic_types                  false
% 6.81/1.54  --sat_finite_models                     false
% 6.81/1.54  --sat_fm_lemmas                         false
% 6.81/1.54  --sat_fm_prep                           false
% 6.81/1.54  --sat_fm_uc_incr                        true
% 6.81/1.54  --sat_out_model                         small
% 6.81/1.54  --sat_out_clauses                       false
% 6.81/1.54  
% 6.81/1.54  ------ QBF Options
% 6.81/1.54  
% 6.81/1.54  --qbf_mode                              false
% 6.81/1.54  --qbf_elim_univ                         false
% 6.81/1.54  --qbf_dom_inst                          none
% 6.81/1.54  --qbf_dom_pre_inst                      false
% 6.81/1.54  --qbf_sk_in                             false
% 6.81/1.54  --qbf_pred_elim                         true
% 6.81/1.54  --qbf_split                             512
% 6.81/1.54  
% 6.81/1.54  ------ BMC1 Options
% 6.81/1.54  
% 6.81/1.54  --bmc1_incremental                      false
% 6.81/1.54  --bmc1_axioms                           reachable_all
% 6.81/1.54  --bmc1_min_bound                        0
% 6.81/1.54  --bmc1_max_bound                        -1
% 6.81/1.54  --bmc1_max_bound_default                -1
% 6.81/1.54  --bmc1_symbol_reachability              true
% 6.81/1.54  --bmc1_property_lemmas                  false
% 6.81/1.54  --bmc1_k_induction                      false
% 6.81/1.54  --bmc1_non_equiv_states                 false
% 6.81/1.54  --bmc1_deadlock                         false
% 6.81/1.54  --bmc1_ucm                              false
% 6.81/1.54  --bmc1_add_unsat_core                   none
% 6.81/1.54  --bmc1_unsat_core_children              false
% 6.81/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.81/1.54  --bmc1_out_stat                         full
% 6.81/1.54  --bmc1_ground_init                      false
% 6.81/1.54  --bmc1_pre_inst_next_state              false
% 6.81/1.54  --bmc1_pre_inst_state                   false
% 6.81/1.54  --bmc1_pre_inst_reach_state             false
% 6.81/1.54  --bmc1_out_unsat_core                   false
% 6.81/1.54  --bmc1_aig_witness_out                  false
% 6.81/1.54  --bmc1_verbose                          false
% 6.81/1.54  --bmc1_dump_clauses_tptp                false
% 6.81/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.81/1.54  --bmc1_dump_file                        -
% 6.81/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.81/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.81/1.54  --bmc1_ucm_extend_mode                  1
% 6.81/1.54  --bmc1_ucm_init_mode                    2
% 6.81/1.54  --bmc1_ucm_cone_mode                    none
% 6.81/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.81/1.54  --bmc1_ucm_relax_model                  4
% 6.81/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.81/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.81/1.54  --bmc1_ucm_layered_model                none
% 6.81/1.54  --bmc1_ucm_max_lemma_size               10
% 6.81/1.54  
% 6.81/1.54  ------ AIG Options
% 6.81/1.54  
% 6.81/1.54  --aig_mode                              false
% 6.81/1.54  
% 6.81/1.54  ------ Instantiation Options
% 6.81/1.54  
% 6.81/1.54  --instantiation_flag                    true
% 6.81/1.54  --inst_sos_flag                         false
% 6.81/1.54  --inst_sos_phase                        true
% 6.81/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.81/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.81/1.54  --inst_lit_sel_side                     none
% 6.81/1.54  --inst_solver_per_active                1400
% 6.81/1.54  --inst_solver_calls_frac                1.
% 6.81/1.54  --inst_passive_queue_type               priority_queues
% 6.81/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.81/1.54  --inst_passive_queues_freq              [25;2]
% 6.81/1.54  --inst_dismatching                      true
% 6.81/1.54  --inst_eager_unprocessed_to_passive     true
% 6.81/1.54  --inst_prop_sim_given                   true
% 6.81/1.54  --inst_prop_sim_new                     false
% 6.81/1.54  --inst_subs_new                         false
% 6.81/1.54  --inst_eq_res_simp                      false
% 6.81/1.54  --inst_subs_given                       false
% 6.81/1.54  --inst_orphan_elimination               true
% 6.81/1.54  --inst_learning_loop_flag               true
% 6.81/1.54  --inst_learning_start                   3000
% 6.81/1.54  --inst_learning_factor                  2
% 6.81/1.54  --inst_start_prop_sim_after_learn       3
% 6.81/1.54  --inst_sel_renew                        solver
% 6.81/1.54  --inst_lit_activity_flag                true
% 6.81/1.54  --inst_restr_to_given                   false
% 6.81/1.54  --inst_activity_threshold               500
% 6.81/1.54  --inst_out_proof                        true
% 6.81/1.54  
% 6.81/1.54  ------ Resolution Options
% 6.81/1.54  
% 6.81/1.54  --resolution_flag                       false
% 6.81/1.54  --res_lit_sel                           adaptive
% 6.81/1.54  --res_lit_sel_side                      none
% 6.81/1.54  --res_ordering                          kbo
% 6.81/1.54  --res_to_prop_solver                    active
% 6.81/1.54  --res_prop_simpl_new                    false
% 6.81/1.54  --res_prop_simpl_given                  true
% 6.81/1.54  --res_passive_queue_type                priority_queues
% 6.81/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.81/1.54  --res_passive_queues_freq               [15;5]
% 6.81/1.54  --res_forward_subs                      full
% 6.81/1.54  --res_backward_subs                     full
% 6.81/1.54  --res_forward_subs_resolution           true
% 6.81/1.54  --res_backward_subs_resolution          true
% 6.81/1.54  --res_orphan_elimination                true
% 6.81/1.54  --res_time_limit                        2.
% 6.81/1.54  --res_out_proof                         true
% 6.81/1.54  
% 6.81/1.54  ------ Superposition Options
% 6.81/1.54  
% 6.81/1.54  --superposition_flag                    true
% 6.81/1.54  --sup_passive_queue_type                priority_queues
% 6.81/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.81/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.81/1.54  --demod_completeness_check              fast
% 6.81/1.54  --demod_use_ground                      true
% 6.81/1.54  --sup_to_prop_solver                    passive
% 6.81/1.54  --sup_prop_simpl_new                    true
% 6.81/1.54  --sup_prop_simpl_given                  true
% 6.81/1.54  --sup_fun_splitting                     false
% 6.81/1.54  --sup_smt_interval                      50000
% 6.81/1.54  
% 6.81/1.54  ------ Superposition Simplification Setup
% 6.81/1.54  
% 6.81/1.54  --sup_indices_passive                   []
% 6.81/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.81/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.54  --sup_full_bw                           [BwDemod]
% 6.81/1.54  --sup_immed_triv                        [TrivRules]
% 6.81/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.81/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.54  --sup_immed_bw_main                     []
% 6.81/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.81/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.54  
% 6.81/1.54  ------ Combination Options
% 6.81/1.54  
% 6.81/1.54  --comb_res_mult                         3
% 6.81/1.54  --comb_sup_mult                         2
% 6.81/1.54  --comb_inst_mult                        10
% 6.81/1.54  
% 6.81/1.54  ------ Debug Options
% 6.81/1.54  
% 6.81/1.54  --dbg_backtrace                         false
% 6.81/1.54  --dbg_dump_prop_clauses                 false
% 6.81/1.54  --dbg_dump_prop_clauses_file            -
% 6.81/1.54  --dbg_out_stat                          false
% 6.81/1.54  
% 6.81/1.54  
% 6.81/1.54  
% 6.81/1.54  
% 6.81/1.54  ------ Proving...
% 6.81/1.54  
% 6.81/1.54  
% 6.81/1.54  % SZS status Theorem for theBenchmark.p
% 6.81/1.54  
% 6.81/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 6.81/1.54  
% 6.81/1.54  fof(f4,axiom,(
% 6.81/1.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f35,plain,(
% 6.81/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.81/1.54    inference(nnf_transformation,[],[f4])).
% 6.81/1.54  
% 6.81/1.54  fof(f36,plain,(
% 6.81/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.81/1.54    inference(flattening,[],[f35])).
% 6.81/1.54  
% 6.81/1.54  fof(f37,plain,(
% 6.81/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.81/1.54    inference(rectify,[],[f36])).
% 6.81/1.54  
% 6.81/1.54  fof(f38,plain,(
% 6.81/1.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 6.81/1.54    introduced(choice_axiom,[])).
% 6.81/1.54  
% 6.81/1.54  fof(f39,plain,(
% 6.81/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.81/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 6.81/1.54  
% 6.81/1.54  fof(f66,plain,(
% 6.81/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 6.81/1.54    inference(cnf_transformation,[],[f39])).
% 6.81/1.54  
% 6.81/1.54  fof(f6,axiom,(
% 6.81/1.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f71,plain,(
% 6.81/1.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.81/1.54    inference(cnf_transformation,[],[f6])).
% 6.81/1.54  
% 6.81/1.54  fof(f98,plain,(
% 6.81/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 6.81/1.54    inference(definition_unfolding,[],[f66,f71])).
% 6.81/1.54  
% 6.81/1.54  fof(f111,plain,(
% 6.81/1.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 6.81/1.54    inference(equality_resolution,[],[f98])).
% 6.81/1.54  
% 6.81/1.54  fof(f112,plain,(
% 6.81/1.54    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 6.81/1.54    inference(equality_resolution,[],[f111])).
% 6.81/1.54  
% 6.81/1.54  fof(f1,axiom,(
% 6.81/1.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f17,plain,(
% 6.81/1.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.81/1.54    inference(ennf_transformation,[],[f1])).
% 6.81/1.54  
% 6.81/1.54  fof(f22,plain,(
% 6.81/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.81/1.54    inference(nnf_transformation,[],[f17])).
% 6.81/1.54  
% 6.81/1.54  fof(f23,plain,(
% 6.81/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.81/1.54    inference(rectify,[],[f22])).
% 6.81/1.54  
% 6.81/1.54  fof(f24,plain,(
% 6.81/1.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.81/1.54    introduced(choice_axiom,[])).
% 6.81/1.54  
% 6.81/1.54  fof(f25,plain,(
% 6.81/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.81/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 6.81/1.54  
% 6.81/1.54  fof(f52,plain,(
% 6.81/1.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 6.81/1.54    inference(cnf_transformation,[],[f25])).
% 6.81/1.54  
% 6.81/1.54  fof(f7,axiom,(
% 6.81/1.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f40,plain,(
% 6.81/1.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.81/1.54    inference(nnf_transformation,[],[f7])).
% 6.81/1.54  
% 6.81/1.54  fof(f41,plain,(
% 6.81/1.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.81/1.54    inference(flattening,[],[f40])).
% 6.81/1.54  
% 6.81/1.54  fof(f74,plain,(
% 6.81/1.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 6.81/1.54    inference(cnf_transformation,[],[f41])).
% 6.81/1.54  
% 6.81/1.54  fof(f116,plain,(
% 6.81/1.54    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 6.81/1.54    inference(equality_resolution,[],[f74])).
% 6.81/1.54  
% 6.81/1.54  fof(f12,axiom,(
% 6.81/1.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f19,plain,(
% 6.81/1.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 6.81/1.54    inference(ennf_transformation,[],[f12])).
% 6.81/1.54  
% 6.81/1.54  fof(f82,plain,(
% 6.81/1.54    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 6.81/1.54    inference(cnf_transformation,[],[f19])).
% 6.81/1.54  
% 6.81/1.54  fof(f5,axiom,(
% 6.81/1.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f70,plain,(
% 6.81/1.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.81/1.54    inference(cnf_transformation,[],[f5])).
% 6.81/1.54  
% 6.81/1.54  fof(f90,plain,(
% 6.81/1.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 6.81/1.54    inference(definition_unfolding,[],[f70,f71])).
% 6.81/1.54  
% 6.81/1.54  fof(f103,plain,(
% 6.81/1.54    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2))) )),
% 6.81/1.54    inference(definition_unfolding,[],[f82,f90])).
% 6.81/1.54  
% 6.81/1.54  fof(f81,plain,(
% 6.81/1.54    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 6.81/1.54    inference(cnf_transformation,[],[f19])).
% 6.81/1.54  
% 6.81/1.54  fof(f104,plain,(
% 6.81/1.54    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2))) )),
% 6.81/1.54    inference(definition_unfolding,[],[f81,f90])).
% 6.81/1.54  
% 6.81/1.54  fof(f15,conjecture,(
% 6.81/1.54    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f16,negated_conjecture,(
% 6.81/1.54    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 6.81/1.54    inference(negated_conjecture,[],[f15])).
% 6.81/1.54  
% 6.81/1.54  fof(f21,plain,(
% 6.81/1.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 6.81/1.54    inference(ennf_transformation,[],[f16])).
% 6.81/1.54  
% 6.81/1.54  fof(f49,plain,(
% 6.81/1.54    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK7,sK8) = X0) )),
% 6.81/1.54    introduced(choice_axiom,[])).
% 6.81/1.54  
% 6.81/1.54  fof(f48,plain,(
% 6.81/1.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK6) = sK6 | k1_mcart_1(sK6) = sK6) & ? [X2,X1] : k4_tarski(X1,X2) = sK6)),
% 6.81/1.54    introduced(choice_axiom,[])).
% 6.81/1.54  
% 6.81/1.54  fof(f50,plain,(
% 6.81/1.54    (k2_mcart_1(sK6) = sK6 | k1_mcart_1(sK6) = sK6) & k4_tarski(sK7,sK8) = sK6),
% 6.81/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f21,f49,f48])).
% 6.81/1.54  
% 6.81/1.54  fof(f89,plain,(
% 6.81/1.54    k2_mcart_1(sK6) = sK6 | k1_mcart_1(sK6) = sK6),
% 6.81/1.54    inference(cnf_transformation,[],[f50])).
% 6.81/1.54  
% 6.81/1.54  fof(f88,plain,(
% 6.81/1.54    k4_tarski(sK7,sK8) = sK6),
% 6.81/1.54    inference(cnf_transformation,[],[f50])).
% 6.81/1.54  
% 6.81/1.54  fof(f13,axiom,(
% 6.81/1.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f83,plain,(
% 6.81/1.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 6.81/1.54    inference(cnf_transformation,[],[f13])).
% 6.81/1.54  
% 6.81/1.54  fof(f84,plain,(
% 6.81/1.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 6.81/1.54    inference(cnf_transformation,[],[f13])).
% 6.81/1.54  
% 6.81/1.54  fof(f9,axiom,(
% 6.81/1.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f43,plain,(
% 6.81/1.54    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 6.81/1.54    introduced(choice_axiom,[])).
% 6.81/1.54  
% 6.81/1.54  fof(f44,plain,(
% 6.81/1.54    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 6.81/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f43])).
% 6.81/1.54  
% 6.81/1.54  fof(f77,plain,(
% 6.81/1.54    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 6.81/1.54    inference(cnf_transformation,[],[f44])).
% 6.81/1.54  
% 6.81/1.54  fof(f10,axiom,(
% 6.81/1.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f45,plain,(
% 6.81/1.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.81/1.54    inference(nnf_transformation,[],[f10])).
% 6.81/1.54  
% 6.81/1.54  fof(f78,plain,(
% 6.81/1.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.81/1.54    inference(cnf_transformation,[],[f45])).
% 6.81/1.54  
% 6.81/1.54  fof(f51,plain,(
% 6.81/1.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.81/1.54    inference(cnf_transformation,[],[f25])).
% 6.81/1.54  
% 6.81/1.54  fof(f11,axiom,(
% 6.81/1.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f18,plain,(
% 6.81/1.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 6.81/1.54    inference(ennf_transformation,[],[f11])).
% 6.81/1.54  
% 6.81/1.54  fof(f80,plain,(
% 6.81/1.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 6.81/1.54    inference(cnf_transformation,[],[f18])).
% 6.81/1.54  
% 6.81/1.54  fof(f14,axiom,(
% 6.81/1.54    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f20,plain,(
% 6.81/1.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 6.81/1.54    inference(ennf_transformation,[],[f14])).
% 6.81/1.54  
% 6.81/1.54  fof(f46,plain,(
% 6.81/1.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 6.81/1.54    introduced(choice_axiom,[])).
% 6.81/1.54  
% 6.81/1.54  fof(f47,plain,(
% 6.81/1.54    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 6.81/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f46])).
% 6.81/1.54  
% 6.81/1.54  fof(f85,plain,(
% 6.81/1.54    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 6.81/1.54    inference(cnf_transformation,[],[f47])).
% 6.81/1.54  
% 6.81/1.54  fof(f3,axiom,(
% 6.81/1.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f31,plain,(
% 6.81/1.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.81/1.54    inference(nnf_transformation,[],[f3])).
% 6.81/1.54  
% 6.81/1.54  fof(f32,plain,(
% 6.81/1.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.81/1.54    inference(rectify,[],[f31])).
% 6.81/1.54  
% 6.81/1.54  fof(f33,plain,(
% 6.81/1.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 6.81/1.54    introduced(choice_axiom,[])).
% 6.81/1.54  
% 6.81/1.54  fof(f34,plain,(
% 6.81/1.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.81/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 6.81/1.54  
% 6.81/1.54  fof(f60,plain,(
% 6.81/1.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.81/1.54    inference(cnf_transformation,[],[f34])).
% 6.81/1.54  
% 6.81/1.54  fof(f94,plain,(
% 6.81/1.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 6.81/1.54    inference(definition_unfolding,[],[f60,f90])).
% 6.81/1.54  
% 6.81/1.54  fof(f110,plain,(
% 6.81/1.54    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 6.81/1.54    inference(equality_resolution,[],[f94])).
% 6.81/1.54  
% 6.81/1.54  fof(f87,plain,(
% 6.81/1.54    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 6.81/1.54    inference(cnf_transformation,[],[f47])).
% 6.81/1.54  
% 6.81/1.54  fof(f65,plain,(
% 6.81/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 6.81/1.54    inference(cnf_transformation,[],[f39])).
% 6.81/1.54  
% 6.81/1.54  fof(f99,plain,(
% 6.81/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 6.81/1.54    inference(definition_unfolding,[],[f65,f71])).
% 6.81/1.54  
% 6.81/1.54  fof(f113,plain,(
% 6.81/1.54    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 6.81/1.54    inference(equality_resolution,[],[f99])).
% 6.81/1.54  
% 6.81/1.54  fof(f114,plain,(
% 6.81/1.54    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 6.81/1.54    inference(equality_resolution,[],[f113])).
% 6.81/1.54  
% 6.81/1.54  fof(f2,axiom,(
% 6.81/1.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f26,plain,(
% 6.81/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.81/1.54    inference(nnf_transformation,[],[f2])).
% 6.81/1.54  
% 6.81/1.54  fof(f27,plain,(
% 6.81/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.81/1.54    inference(flattening,[],[f26])).
% 6.81/1.54  
% 6.81/1.54  fof(f28,plain,(
% 6.81/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.81/1.54    inference(rectify,[],[f27])).
% 6.81/1.54  
% 6.81/1.54  fof(f29,plain,(
% 6.81/1.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 6.81/1.54    introduced(choice_axiom,[])).
% 6.81/1.54  
% 6.81/1.54  fof(f30,plain,(
% 6.81/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.81/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 6.81/1.54  
% 6.81/1.54  fof(f55,plain,(
% 6.81/1.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.81/1.54    inference(cnf_transformation,[],[f30])).
% 6.81/1.54  
% 6.81/1.54  fof(f106,plain,(
% 6.81/1.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 6.81/1.54    inference(equality_resolution,[],[f55])).
% 6.81/1.54  
% 6.81/1.54  fof(f56,plain,(
% 6.81/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 6.81/1.54    inference(cnf_transformation,[],[f30])).
% 6.81/1.54  
% 6.81/1.54  fof(f105,plain,(
% 6.81/1.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 6.81/1.54    inference(equality_resolution,[],[f56])).
% 6.81/1.54  
% 6.81/1.54  fof(f54,plain,(
% 6.81/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.81/1.54    inference(cnf_transformation,[],[f30])).
% 6.81/1.54  
% 6.81/1.54  fof(f107,plain,(
% 6.81/1.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 6.81/1.54    inference(equality_resolution,[],[f54])).
% 6.81/1.54  
% 6.81/1.54  fof(f86,plain,(
% 6.81/1.54    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 6.81/1.54    inference(cnf_transformation,[],[f47])).
% 6.81/1.54  
% 6.81/1.54  fof(f8,axiom,(
% 6.81/1.54    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 6.81/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.81/1.54  
% 6.81/1.54  fof(f42,plain,(
% 6.81/1.54    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 6.81/1.54    inference(nnf_transformation,[],[f8])).
% 6.81/1.54  
% 6.81/1.54  fof(f75,plain,(
% 6.81/1.54    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 6.81/1.54    inference(cnf_transformation,[],[f42])).
% 6.81/1.54  
% 6.81/1.54  fof(f102,plain,(
% 6.81/1.54    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) != k1_enumset1(X0,X0,X0)) )),
% 6.81/1.54    inference(definition_unfolding,[],[f75,f90,f90,f90])).
% 6.81/1.54  
% 6.81/1.54  fof(f118,plain,(
% 6.81/1.54    ( ! [X1] : (k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) != k1_enumset1(X1,X1,X1)) )),
% 6.81/1.54    inference(equality_resolution,[],[f102])).
% 6.81/1.54  
% 6.81/1.54  cnf(c_16,plain,
% 6.81/1.54      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 6.81/1.54      inference(cnf_transformation,[],[f112]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1177,plain,
% 6.81/1.54      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1,plain,
% 6.81/1.54      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 6.81/1.54      inference(cnf_transformation,[],[f52]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1192,plain,
% 6.81/1.54      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 6.81/1.54      | r1_tarski(X0,X1) = iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_19,plain,
% 6.81/1.54      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.81/1.54      inference(cnf_transformation,[],[f116]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_28,plain,
% 6.81/1.54      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2))
% 6.81/1.54      | r2_hidden(k2_mcart_1(X0),X2) ),
% 6.81/1.54      inference(cnf_transformation,[],[f103]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1173,plain,
% 6.81/1.54      ( r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2)) != iProver_top
% 6.81/1.54      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_5095,plain,
% 6.81/1.54      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 6.81/1.54      | r2_hidden(k2_mcart_1(X0),k1_xboole_0) = iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_19,c_1173]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_29,plain,
% 6.81/1.54      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2))
% 6.81/1.54      | k1_mcart_1(X0) = X1 ),
% 6.81/1.54      inference(cnf_transformation,[],[f104]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1172,plain,
% 6.81/1.54      ( k1_mcart_1(X0) = X1
% 6.81/1.54      | r2_hidden(X0,k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2)) != iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_4571,plain,
% 6.81/1.54      ( k1_mcart_1(X0) = X1 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_19,c_1172]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_5123,plain,
% 6.81/1.54      ( k1_mcart_1(k2_mcart_1(X0)) = X1
% 6.81/1.54      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_5095,c_4571]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_5465,plain,
% 6.81/1.54      ( k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,X0))) = X1
% 6.81/1.54      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_1192,c_5123]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_35,negated_conjecture,
% 6.81/1.54      ( k1_mcart_1(sK6) = sK6 | k2_mcart_1(sK6) = sK6 ),
% 6.81/1.54      inference(cnf_transformation,[],[f89]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_36,negated_conjecture,
% 6.81/1.54      ( k4_tarski(sK7,sK8) = sK6 ),
% 6.81/1.54      inference(cnf_transformation,[],[f88]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_31,plain,
% 6.81/1.54      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 6.81/1.54      inference(cnf_transformation,[],[f83]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1449,plain,
% 6.81/1.54      ( k1_mcart_1(sK6) = sK7 ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_36,c_31]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1451,plain,
% 6.81/1.54      ( k2_mcart_1(sK6) = sK6 | sK7 = sK6 ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_35,c_1449]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_30,plain,
% 6.81/1.54      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 6.81/1.54      inference(cnf_transformation,[],[f84]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1429,plain,
% 6.81/1.54      ( k2_mcart_1(sK6) = sK8 ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_36,c_30]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1453,plain,
% 6.81/1.54      ( sK8 = sK6 | sK7 = sK6 ),
% 6.81/1.54      inference(demodulation,[status(thm)],[c_1451,c_1429]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_24,plain,
% 6.81/1.54      ( m1_subset_1(sK4(X0),X0) ),
% 6.81/1.54      inference(cnf_transformation,[],[f77]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_26,plain,
% 6.81/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.81/1.54      inference(cnf_transformation,[],[f78]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_232,plain,
% 6.81/1.54      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.81/1.54      inference(prop_impl,[status(thm)],[c_26]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_233,plain,
% 6.81/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.81/1.54      inference(renaming,[status(thm)],[c_232]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_392,plain,
% 6.81/1.54      ( r1_tarski(X0,X1) | k1_zfmisc_1(X1) != X2 | sK4(X2) != X0 ),
% 6.81/1.54      inference(resolution_lifted,[status(thm)],[c_24,c_233]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_393,plain,
% 6.81/1.54      ( r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
% 6.81/1.54      inference(unflattening,[status(thm)],[c_392]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1168,plain,
% 6.81/1.54      ( r1_tarski(sK4(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_2,plain,
% 6.81/1.54      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 6.81/1.54      inference(cnf_transformation,[],[f51]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1191,plain,
% 6.81/1.54      ( r2_hidden(X0,X1) != iProver_top
% 6.81/1.54      | r2_hidden(X0,X2) = iProver_top
% 6.81/1.54      | r1_tarski(X1,X2) != iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_6446,plain,
% 6.81/1.54      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 6.81/1.54      | r2_hidden(k2_mcart_1(X0),X1) = iProver_top
% 6.81/1.54      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_5095,c_1191]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_27,plain,
% 6.81/1.54      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 6.81/1.54      inference(cnf_transformation,[],[f80]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1174,plain,
% 6.81/1.54      ( r2_hidden(X0,X1) != iProver_top
% 6.81/1.54      | r1_tarski(X1,X0) != iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_8872,plain,
% 6.81/1.54      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 6.81/1.54      | r1_tarski(X1,k2_mcart_1(X0)) != iProver_top
% 6.81/1.54      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_6446,c_1174]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_10257,plain,
% 6.81/1.54      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 6.81/1.54      | r1_tarski(k1_xboole_0,sK4(k1_zfmisc_1(k2_mcart_1(X0)))) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_1168,c_8872]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_11737,plain,
% 6.81/1.54      ( r2_hidden(sK6,k1_xboole_0) != iProver_top
% 6.81/1.54      | r1_tarski(k1_xboole_0,sK4(k1_zfmisc_1(sK8))) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_1429,c_10257]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_11761,plain,
% 6.81/1.54      ( sK7 = sK6
% 6.81/1.54      | r2_hidden(sK6,k1_xboole_0) != iProver_top
% 6.81/1.54      | r1_tarski(k1_xboole_0,sK4(k1_zfmisc_1(sK6))) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_1453,c_11737]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_16936,plain,
% 6.81/1.54      ( k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6))))) = X0
% 6.81/1.54      | sK7 = sK6
% 6.81/1.54      | r2_hidden(sK6,k1_xboole_0) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_5465,c_11761]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_34,plain,
% 6.81/1.54      ( r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0 ),
% 6.81/1.54      inference(cnf_transformation,[],[f85]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1169,plain,
% 6.81/1.54      ( k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0) = iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_12,plain,
% 6.81/1.54      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 6.81/1.54      inference(cnf_transformation,[],[f110]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1181,plain,
% 6.81/1.54      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_2719,plain,
% 6.81/1.54      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 6.81/1.54      | sK5(k1_enumset1(X0,X0,X0)) = X0 ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_1169,c_1181]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_32,plain,
% 6.81/1.54      ( ~ r2_hidden(X0,X1)
% 6.81/1.54      | k4_tarski(X2,X0) != sK5(X1)
% 6.81/1.54      | k1_xboole_0 = X1 ),
% 6.81/1.54      inference(cnf_transformation,[],[f87]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1171,plain,
% 6.81/1.54      ( k4_tarski(X0,X1) != sK5(X2)
% 6.81/1.54      | k1_xboole_0 = X2
% 6.81/1.54      | r2_hidden(X1,X2) != iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_2520,plain,
% 6.81/1.54      ( sK5(X0) != sK6
% 6.81/1.54      | k1_xboole_0 = X0
% 6.81/1.54      | r2_hidden(sK8,X0) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_36,c_1171]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_16988,plain,
% 6.81/1.54      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 6.81/1.54      | sK6 != X0
% 6.81/1.54      | r2_hidden(sK8,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_2719,c_2520]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_18102,plain,
% 6.81/1.54      ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0
% 6.81/1.54      | r2_hidden(sK8,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
% 6.81/1.54      inference(equality_resolution,[status(thm)],[c_16988]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_18816,plain,
% 6.81/1.54      ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0
% 6.81/1.54      | sK7 = sK6
% 6.81/1.54      | r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_1453,c_18102]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_17,plain,
% 6.81/1.54      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 6.81/1.54      inference(cnf_transformation,[],[f114]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_1176,plain,
% 6.81/1.54      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 6.81/1.54      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_19009,plain,
% 6.81/1.54      ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0 | sK7 = sK6 ),
% 6.81/1.54      inference(forward_subsumption_resolution,
% 6.81/1.54                [status(thm)],
% 6.81/1.54                [c_18816,c_1176]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_19033,plain,
% 6.81/1.54      ( sK7 = sK6 | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 6.81/1.54      inference(superposition,[status(thm)],[c_19009,c_1176]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_19614,plain,
% 6.81/1.54      ( sK7 = sK6
% 6.81/1.54      | k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6))))) = X0 ),
% 6.81/1.54      inference(global_propositional_subsumption,
% 6.81/1.54                [status(thm)],
% 6.81/1.54                [c_16936,c_19033]) ).
% 6.81/1.54  
% 6.81/1.54  cnf(c_19615,plain,
% 6.81/1.54      ( k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6))))) = X0
% 6.81/1.54      | sK7 = sK6 ),
% 6.81/1.54      inference(renaming,[status(thm)],[c_19614]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_19685,plain,
% 6.81/1.55      ( sK7 = sK6
% 6.81/1.55      | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) = iProver_top ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_19615,c_1176]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_7,plain,
% 6.81/1.55      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 6.81/1.55      inference(cnf_transformation,[],[f106]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_1186,plain,
% 6.81/1.55      ( r2_hidden(X0,X1) != iProver_top
% 6.81/1.55      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 6.81/1.55      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_19710,plain,
% 6.81/1.55      ( sK7 = sK6
% 6.81/1.55      | r2_hidden(X0,X1) != iProver_top
% 6.81/1.55      | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) != iProver_top ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_19615,c_1186]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_6,plain,
% 6.81/1.55      ( ~ r2_hidden(X0,X1)
% 6.81/1.55      | r2_hidden(X0,X2)
% 6.81/1.55      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 6.81/1.55      inference(cnf_transformation,[],[f105]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_1187,plain,
% 6.81/1.55      ( r2_hidden(X0,X1) != iProver_top
% 6.81/1.55      | r2_hidden(X0,X2) = iProver_top
% 6.81/1.55      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 6.81/1.55      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_19712,plain,
% 6.81/1.55      ( sK7 = sK6
% 6.81/1.55      | r2_hidden(X0,X1) != iProver_top
% 6.81/1.55      | r2_hidden(X0,X2) = iProver_top
% 6.81/1.55      | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) = iProver_top ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_19615,c_1187]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_8,plain,
% 6.81/1.55      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 6.81/1.55      inference(cnf_transformation,[],[f107]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_1185,plain,
% 6.81/1.55      ( r2_hidden(X0,X1) = iProver_top
% 6.81/1.55      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 6.81/1.55      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_19713,plain,
% 6.81/1.55      ( sK7 = sK6
% 6.81/1.55      | r2_hidden(X0,X1) = iProver_top
% 6.81/1.55      | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) != iProver_top ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_19615,c_1185]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_19811,plain,
% 6.81/1.55      ( sK7 = sK6
% 6.81/1.55      | r2_hidden(X0,X1) != iProver_top
% 6.81/1.55      | r2_hidden(X0,X2) = iProver_top ),
% 6.81/1.55      inference(forward_subsumption_resolution,
% 6.81/1.55                [status(thm)],
% 6.81/1.55                [c_19712,c_19713]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_19818,plain,
% 6.81/1.55      ( sK7 = sK6
% 6.81/1.55      | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK0(k1_xboole_0,sK4(k1_zfmisc_1(sK6)))))) != iProver_top ),
% 6.81/1.55      inference(forward_subsumption_resolution,
% 6.81/1.55                [status(thm)],
% 6.81/1.55                [c_19710,c_19811]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_19905,plain,
% 6.81/1.55      ( sK7 = sK6 ),
% 6.81/1.55      inference(forward_subsumption_resolution,
% 6.81/1.55                [status(thm)],
% 6.81/1.55                [c_19685,c_19818]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_33,plain,
% 6.81/1.55      ( ~ r2_hidden(X0,X1)
% 6.81/1.55      | k4_tarski(X0,X2) != sK5(X1)
% 6.81/1.55      | k1_xboole_0 = X1 ),
% 6.81/1.55      inference(cnf_transformation,[],[f86]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_1170,plain,
% 6.81/1.55      ( k4_tarski(X0,X1) != sK5(X2)
% 6.81/1.55      | k1_xboole_0 = X2
% 6.81/1.55      | r2_hidden(X0,X2) != iProver_top ),
% 6.81/1.55      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_1677,plain,
% 6.81/1.55      ( sK5(X0) != sK6
% 6.81/1.55      | k1_xboole_0 = X0
% 6.81/1.55      | r2_hidden(sK7,X0) != iProver_top ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_36,c_1170]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_16990,plain,
% 6.81/1.55      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 6.81/1.55      | sK6 != X0
% 6.81/1.55      | r2_hidden(sK7,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_2719,c_1677]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_20979,plain,
% 6.81/1.55      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 6.81/1.55      | sK6 != X0
% 6.81/1.55      | r2_hidden(sK6,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 6.81/1.55      inference(demodulation,[status(thm)],[c_19905,c_16990]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_13698,plain,
% 6.81/1.55      ( ~ r2_hidden(sK6,k1_enumset1(X0,X0,X0)) | sK6 = X0 ),
% 6.81/1.55      inference(instantiation,[status(thm)],[c_12]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_13699,plain,
% 6.81/1.55      ( sK6 = X0 | r2_hidden(sK6,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 6.81/1.55      inference(predicate_to_equality,[status(thm)],[c_13698]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_22199,plain,
% 6.81/1.55      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 6.81/1.55      | r2_hidden(sK6,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 6.81/1.55      inference(global_propositional_subsumption,
% 6.81/1.55                [status(thm)],
% 6.81/1.55                [c_20979,c_13699]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_22207,plain,
% 6.81/1.55      ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0 ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_1177,c_22199]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_23,plain,
% 6.81/1.55      ( k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)) != k1_enumset1(X0,X0,X0) ),
% 6.81/1.55      inference(cnf_transformation,[],[f118]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_22690,plain,
% 6.81/1.55      ( k1_enumset1(sK6,sK6,sK6) != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_22207,c_23]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_22760,plain,
% 6.81/1.55      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 6.81/1.55      inference(light_normalisation,[status(thm)],[c_22690,c_22207]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_3787,plain,
% 6.81/1.55      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 6.81/1.55      | r2_hidden(sK5(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_1169,c_1185]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_4809,plain,
% 6.81/1.55      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 6.81/1.55      | r2_hidden(sK5(k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_1169,c_1186]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_17142,plain,
% 6.81/1.55      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.81/1.55      inference(superposition,[status(thm)],[c_3787,c_4809]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(c_17320,plain,
% 6.81/1.55      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 6.81/1.55      inference(instantiation,[status(thm)],[c_17142]) ).
% 6.81/1.55  
% 6.81/1.55  cnf(contradiction,plain,
% 6.81/1.55      ( $false ),
% 6.81/1.55      inference(minisat,[status(thm)],[c_22760,c_17320]) ).
% 6.81/1.55  
% 6.81/1.55  
% 6.81/1.55  % SZS output end CNFRefutation for theBenchmark.p
% 6.81/1.55  
% 6.81/1.55  ------                               Statistics
% 6.81/1.55  
% 6.81/1.55  ------ General
% 6.81/1.55  
% 6.81/1.55  abstr_ref_over_cycles:                  0
% 6.81/1.55  abstr_ref_under_cycles:                 0
% 6.81/1.55  gc_basic_clause_elim:                   0
% 6.81/1.55  forced_gc_time:                         0
% 6.81/1.55  parsing_time:                           0.017
% 6.81/1.55  unif_index_cands_time:                  0.
% 6.81/1.55  unif_index_add_time:                    0.
% 6.81/1.55  orderings_time:                         0.
% 6.81/1.55  out_proof_time:                         0.015
% 6.81/1.55  total_time:                             0.645
% 6.81/1.55  num_of_symbols:                         51
% 6.81/1.55  num_of_terms:                           31645
% 6.81/1.55  
% 6.81/1.55  ------ Preprocessing
% 6.81/1.55  
% 6.81/1.55  num_of_splits:                          0
% 6.81/1.55  num_of_split_atoms:                     0
% 6.81/1.55  num_of_reused_defs:                     0
% 6.81/1.55  num_eq_ax_congr_red:                    50
% 6.81/1.55  num_of_sem_filtered_clauses:            1
% 6.81/1.55  num_of_subtypes:                        0
% 6.81/1.55  monotx_restored_types:                  0
% 6.81/1.55  sat_num_of_epr_types:                   0
% 6.81/1.55  sat_num_of_non_cyclic_types:            0
% 6.81/1.55  sat_guarded_non_collapsed_types:        0
% 6.81/1.55  num_pure_diseq_elim:                    0
% 6.81/1.55  simp_replaced_by:                       0
% 6.81/1.55  res_preprocessed:                       163
% 6.81/1.55  prep_upred:                             0
% 6.81/1.55  prep_unflattend:                        26
% 6.81/1.55  smt_new_axioms:                         0
% 6.81/1.55  pred_elim_cands:                        2
% 6.81/1.55  pred_elim:                              1
% 6.81/1.55  pred_elim_cl:                           2
% 6.81/1.55  pred_elim_cycles:                       3
% 6.81/1.55  merged_defs:                            2
% 6.81/1.55  merged_defs_ncl:                        0
% 6.81/1.55  bin_hyper_res:                          2
% 6.81/1.55  prep_cycles:                            4
% 6.81/1.55  pred_elim_time:                         0.003
% 6.81/1.55  splitting_time:                         0.
% 6.81/1.55  sem_filter_time:                        0.
% 6.81/1.55  monotx_time:                            0.
% 6.81/1.55  subtype_inf_time:                       0.
% 6.81/1.55  
% 6.81/1.55  ------ Problem properties
% 6.81/1.55  
% 6.81/1.55  clauses:                                35
% 6.81/1.55  conjectures:                            2
% 6.81/1.55  epr:                                    2
% 6.81/1.55  horn:                                   23
% 6.81/1.55  ground:                                 2
% 6.81/1.55  unary:                                  10
% 6.81/1.55  binary:                                 11
% 6.81/1.55  lits:                                   76
% 6.81/1.55  lits_eq:                                36
% 6.81/1.55  fd_pure:                                0
% 6.81/1.55  fd_pseudo:                              0
% 6.81/1.55  fd_cond:                                4
% 6.81/1.55  fd_pseudo_cond:                         10
% 6.81/1.55  ac_symbols:                             0
% 6.81/1.55  
% 6.81/1.55  ------ Propositional Solver
% 6.81/1.55  
% 6.81/1.55  prop_solver_calls:                      29
% 6.81/1.55  prop_fast_solver_calls:                 1103
% 6.81/1.55  smt_solver_calls:                       0
% 6.81/1.55  smt_fast_solver_calls:                  0
% 6.81/1.55  prop_num_of_clauses:                    8592
% 6.81/1.55  prop_preprocess_simplified:             26712
% 6.81/1.55  prop_fo_subsumed:                       23
% 6.81/1.55  prop_solver_time:                       0.
% 6.81/1.55  smt_solver_time:                        0.
% 6.81/1.55  smt_fast_solver_time:                   0.
% 6.81/1.55  prop_fast_solver_time:                  0.
% 6.81/1.55  prop_unsat_core_time:                   0.
% 6.81/1.55  
% 6.81/1.55  ------ QBF
% 6.81/1.55  
% 6.81/1.55  qbf_q_res:                              0
% 6.81/1.55  qbf_num_tautologies:                    0
% 6.81/1.55  qbf_prep_cycles:                        0
% 6.81/1.55  
% 6.81/1.55  ------ BMC1
% 6.81/1.55  
% 6.81/1.55  bmc1_current_bound:                     -1
% 6.81/1.55  bmc1_last_solved_bound:                 -1
% 6.81/1.55  bmc1_unsat_core_size:                   -1
% 6.81/1.55  bmc1_unsat_core_parents_size:           -1
% 6.81/1.55  bmc1_merge_next_fun:                    0
% 6.81/1.55  bmc1_unsat_core_clauses_time:           0.
% 6.81/1.55  
% 6.81/1.55  ------ Instantiation
% 6.81/1.55  
% 6.81/1.55  inst_num_of_clauses:                    3298
% 6.81/1.55  inst_num_in_passive:                    1302
% 6.81/1.55  inst_num_in_active:                     642
% 6.81/1.55  inst_num_in_unprocessed:                1354
% 6.81/1.55  inst_num_of_loops:                      700
% 6.81/1.55  inst_num_of_learning_restarts:          0
% 6.81/1.55  inst_num_moves_active_passive:          57
% 6.81/1.55  inst_lit_activity:                      0
% 6.81/1.55  inst_lit_activity_moves:                0
% 6.81/1.55  inst_num_tautologies:                   0
% 6.81/1.55  inst_num_prop_implied:                  0
% 6.81/1.55  inst_num_existing_simplified:           0
% 6.81/1.55  inst_num_eq_res_simplified:             0
% 6.81/1.55  inst_num_child_elim:                    0
% 6.81/1.55  inst_num_of_dismatching_blockings:      1094
% 6.81/1.55  inst_num_of_non_proper_insts:           2101
% 6.81/1.55  inst_num_of_duplicates:                 0
% 6.81/1.55  inst_inst_num_from_inst_to_res:         0
% 6.81/1.55  inst_dismatching_checking_time:         0.
% 6.81/1.55  
% 6.81/1.55  ------ Resolution
% 6.81/1.55  
% 6.81/1.55  res_num_of_clauses:                     0
% 6.81/1.55  res_num_in_passive:                     0
% 6.81/1.55  res_num_in_active:                      0
% 6.81/1.55  res_num_of_loops:                       167
% 6.81/1.55  res_forward_subset_subsumed:            223
% 6.81/1.55  res_backward_subset_subsumed:           0
% 6.81/1.55  res_forward_subsumed:                   0
% 6.81/1.55  res_backward_subsumed:                  0
% 6.81/1.55  res_forward_subsumption_resolution:     0
% 6.81/1.55  res_backward_subsumption_resolution:    0
% 6.81/1.55  res_clause_to_clause_subsumption:       2143
% 6.81/1.55  res_orphan_elimination:                 0
% 6.81/1.55  res_tautology_del:                      106
% 6.81/1.55  res_num_eq_res_simplified:              0
% 6.81/1.55  res_num_sel_changes:                    0
% 6.81/1.55  res_moves_from_active_to_pass:          0
% 6.81/1.55  
% 6.81/1.55  ------ Superposition
% 6.81/1.55  
% 6.81/1.55  sup_time_total:                         0.
% 6.81/1.55  sup_time_generating:                    0.
% 6.81/1.55  sup_time_sim_full:                      0.
% 6.81/1.55  sup_time_sim_immed:                     0.
% 6.81/1.55  
% 6.81/1.55  sup_num_of_clauses:                     374
% 6.81/1.55  sup_num_in_active:                      120
% 6.81/1.55  sup_num_in_passive:                     254
% 6.81/1.55  sup_num_of_loops:                       138
% 6.81/1.55  sup_fw_superposition:                   295
% 6.81/1.55  sup_bw_superposition:                   567
% 6.81/1.55  sup_immediate_simplified:               346
% 6.81/1.55  sup_given_eliminated:                   1
% 6.81/1.55  comparisons_done:                       0
% 6.81/1.55  comparisons_avoided:                    40
% 6.81/1.55  
% 6.81/1.55  ------ Simplifications
% 6.81/1.55  
% 6.81/1.55  
% 6.81/1.55  sim_fw_subset_subsumed:                 186
% 6.81/1.55  sim_bw_subset_subsumed:                 82
% 6.81/1.55  sim_fw_subsumed:                        51
% 6.81/1.55  sim_bw_subsumed:                        35
% 6.81/1.55  sim_fw_subsumption_res:                 11
% 6.81/1.55  sim_bw_subsumption_res:                 0
% 6.81/1.55  sim_tautology_del:                      8
% 6.81/1.55  sim_eq_tautology_del:                   69
% 6.81/1.55  sim_eq_res_simp:                        1
% 6.81/1.55  sim_fw_demodulated:                     57
% 6.81/1.55  sim_bw_demodulated:                     11
% 6.81/1.55  sim_light_normalised:                   23
% 6.81/1.55  sim_joinable_taut:                      0
% 6.81/1.55  sim_joinable_simp:                      0
% 6.81/1.55  sim_ac_normalised:                      0
% 6.81/1.55  sim_smt_subsumption:                    0
% 6.81/1.55  
%------------------------------------------------------------------------------
