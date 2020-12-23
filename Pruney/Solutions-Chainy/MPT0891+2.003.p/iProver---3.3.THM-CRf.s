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
% DateTime   : Thu Dec  3 11:58:32 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  164 (32438 expanded)
%              Number of clauses        :   86 (8492 expanded)
%              Number of leaves         :   20 (9681 expanded)
%              Depth                    :   28
%              Number of atoms          :  584 (148681 expanded)
%              Number of equality atoms :  466 (116790 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( k7_mcart_1(X0,X1,X2,sK7) = sK7
          | k6_mcart_1(X0,X1,X2,sK7) = sK7
          | k5_mcart_1(X0,X1,X2,sK7) = sK7 )
        & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK4,sK5,sK6,X3) = X3
            | k6_mcart_1(sK4,sK5,sK6,X3) = X3
            | k5_mcart_1(sK4,sK5,sK6,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK4,sK5,sK6)) )
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( k7_mcart_1(sK4,sK5,sK6,sK7) = sK7
      | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
      | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7 )
    & m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f23,f43,f42])).

fof(f87,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7 ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f80,f71])).

fof(f86,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f44])).

fof(f108,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f86,f71])).

fof(f83,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f88,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f88])).

fof(f121,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f88])).

fof(f119,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f97])).

fof(f120,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f119])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f79,f71])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f78,f71])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f77,f70,f71])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f73])).

fof(f82,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f40])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f75,f70])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f116,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f54])).

fof(f117,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f116])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f66,f66])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f70])).

cnf(c_33,negated_conjecture,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_366,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | sK7 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_34])).

cnf(c_367,plain,
    ( k7_mcart_1(X0,X1,X2,sK7) = k2_mcart_1(sK7)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_1349,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7)
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_367])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_70,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_73,plain,
    ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_586,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1273,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_1274,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_1275,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_1276,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_1277,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_1278,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1277])).

cnf(c_1553,plain,
    ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1349,c_37,c_36,c_35,c_70,c_73,c_1274,c_1276,c_1278])).

cnf(c_1556,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k2_mcart_1(sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_33,c_1553])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_348,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | sK7 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_349,plain,
    ( k6_mcart_1(X0,X1,X2,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_1361,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_349])).

cnf(c_1899,plain,
    ( k6_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1361,c_37,c_36,c_35,c_70,c_73,c_1274,c_1276,c_1278])).

cnf(c_1902,plain,
    ( k5_mcart_1(sK4,sK5,sK6,sK7) = sK7
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | k2_mcart_1(sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_1556,c_1899])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_330,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | sK7 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_331,plain,
    ( k5_mcart_1(X0,X1,X2,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_1355,plain,
    ( k5_mcart_1(sK4,sK5,sK6,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_331])).

cnf(c_1605,plain,
    ( k5_mcart_1(sK4,sK5,sK6,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1355,c_37,c_36,c_35,c_70,c_73,c_1274,c_1276,c_1278])).

cnf(c_1904,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = sK7
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | k2_mcart_1(sK7) = sK7 ),
    inference(demodulation,[status(thm)],[c_1902,c_1605])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_384,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | sK7 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_385,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK7),k6_mcart_1(X0,X1,X2,sK7)),k7_mcart_1(X0,X1,X2,sK7)) = sK7
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_1367,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_385])).

cnf(c_1905,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1367,c_37,c_36,c_35,c_70,c_73,c_1274,c_1276,c_1278])).

cnf(c_1907,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))),k2_mcart_1(sK7)) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_1905,c_1553,c_1605,c_1899])).

cnf(c_32,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1910,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
    inference(superposition,[status(thm)],[c_1907,c_32])).

cnf(c_2636,plain,
    ( k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | k2_mcart_1(sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_1904,c_1910])).

cnf(c_1912,plain,
    ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
    inference(demodulation,[status(thm)],[c_1910,c_1907])).

cnf(c_22,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_31,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1015,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_22,c_31])).

cnf(c_2293,plain,
    ( k2_mcart_1(sK7) != sK7 ),
    inference(superposition,[status(thm)],[c_1912,c_1015])).

cnf(c_2657,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2636,c_2293])).

cnf(c_2658,plain,
    ( k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
    inference(renaming,[status(thm)],[c_2657])).

cnf(c_26,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_968,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_974,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3026,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK3(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_968,c_974])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK3(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_969,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK3(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2230,plain,
    ( k4_tarski(sK7,X0) != sK3(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k1_mcart_1(sK7),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_969])).

cnf(c_3409,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | k4_tarski(sK7,X1) != X0
    | r2_hidden(k1_mcart_1(sK7),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3026,c_2230])).

cnf(c_3763,plain,
    ( k1_enumset1(k4_tarski(sK7,X0),k4_tarski(sK7,X0),k4_tarski(sK7,X0)) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK7),k1_enumset1(k4_tarski(sK7,X0),k4_tarski(sK7,X0),k4_tarski(sK7,X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3409])).

cnf(c_5050,plain,
    ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k1_mcart_1(sK7),k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2658,c_3763])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_979,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5058,plain,
    ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5050,c_979])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_enumset1(X2,X2,X0),X1) != k1_enumset1(X2,X2,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_972,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5070,plain,
    ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) != k4_xboole_0(k1_xboole_0,X0)
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5058,c_972])).

cnf(c_6559,plain,
    ( k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7)) != k4_xboole_0(k1_xboole_0,X0)
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2658,c_5070])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_93,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5062,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5058,c_979])).

cnf(c_6558,plain,
    ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5058,c_5070])).

cnf(c_6575,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK7
    | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6558])).

cnf(c_6677,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6559,c_93,c_5062,c_6575])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK3(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_970,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK3(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2906,plain,
    ( k4_tarski(k1_mcart_1(sK7),X0) != sK3(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1910,c_970])).

cnf(c_3162,plain,
    ( sK3(X0) != sK7
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_2906])).

cnf(c_3402,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK7 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3026,c_3162])).

cnf(c_3693,plain,
    ( k1_enumset1(sK7,sK7,sK7) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_enumset1(sK7,sK7,sK7)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3402])).

cnf(c_6683,plain,
    ( k1_enumset1(sK7,sK7,sK7) = k1_xboole_0
    | r2_hidden(sK7,k1_enumset1(sK7,sK7,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6677,c_3693])).

cnf(c_6885,plain,
    ( k1_enumset1(sK7,sK7,sK7) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6683,c_979])).

cnf(c_6892,plain,
    ( k1_enumset1(sK7,sK7,sK7) != k4_xboole_0(k1_xboole_0,X0)
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6885,c_972])).

cnf(c_6894,plain,
    ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6892,c_6885])).

cnf(c_6903,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6894])).

cnf(c_6886,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6885,c_979])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6903,c_6886,c_93])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:09:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.41/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/0.98  
% 3.41/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/0.98  
% 3.41/0.98  ------  iProver source info
% 3.41/0.98  
% 3.41/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.41/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/0.98  git: non_committed_changes: false
% 3.41/0.98  git: last_make_outside_of_git: false
% 3.41/0.98  
% 3.41/0.98  ------ 
% 3.41/0.98  
% 3.41/0.98  ------ Input Options
% 3.41/0.98  
% 3.41/0.98  --out_options                           all
% 3.41/0.98  --tptp_safe_out                         true
% 3.41/0.98  --problem_path                          ""
% 3.41/0.98  --include_path                          ""
% 3.41/0.98  --clausifier                            res/vclausify_rel
% 3.41/0.98  --clausifier_options                    --mode clausify
% 3.41/0.98  --stdin                                 false
% 3.41/0.98  --stats_out                             all
% 3.41/0.98  
% 3.41/0.98  ------ General Options
% 3.41/0.98  
% 3.41/0.98  --fof                                   false
% 3.41/0.98  --time_out_real                         305.
% 3.41/0.98  --time_out_virtual                      -1.
% 3.41/0.98  --symbol_type_check                     false
% 3.41/0.98  --clausify_out                          false
% 3.41/0.98  --sig_cnt_out                           false
% 3.41/0.98  --trig_cnt_out                          false
% 3.41/0.98  --trig_cnt_out_tolerance                1.
% 3.41/0.98  --trig_cnt_out_sk_spl                   false
% 3.41/0.98  --abstr_cl_out                          false
% 3.41/0.98  
% 3.41/0.98  ------ Global Options
% 3.41/0.98  
% 3.41/0.98  --schedule                              default
% 3.41/0.98  --add_important_lit                     false
% 3.41/0.98  --prop_solver_per_cl                    1000
% 3.41/0.98  --min_unsat_core                        false
% 3.41/0.98  --soft_assumptions                      false
% 3.41/0.98  --soft_lemma_size                       3
% 3.41/0.98  --prop_impl_unit_size                   0
% 3.41/0.98  --prop_impl_unit                        []
% 3.41/0.98  --share_sel_clauses                     true
% 3.41/0.98  --reset_solvers                         false
% 3.41/0.98  --bc_imp_inh                            [conj_cone]
% 3.41/0.98  --conj_cone_tolerance                   3.
% 3.41/0.98  --extra_neg_conj                        none
% 3.41/0.98  --large_theory_mode                     true
% 3.41/0.98  --prolific_symb_bound                   200
% 3.41/0.98  --lt_threshold                          2000
% 3.41/0.98  --clause_weak_htbl                      true
% 3.41/0.98  --gc_record_bc_elim                     false
% 3.41/0.98  
% 3.41/0.98  ------ Preprocessing Options
% 3.41/0.98  
% 3.41/0.98  --preprocessing_flag                    true
% 3.41/0.98  --time_out_prep_mult                    0.1
% 3.41/0.98  --splitting_mode                        input
% 3.41/0.98  --splitting_grd                         true
% 3.41/0.98  --splitting_cvd                         false
% 3.41/0.98  --splitting_cvd_svl                     false
% 3.41/0.98  --splitting_nvd                         32
% 3.41/0.98  --sub_typing                            true
% 3.41/0.98  --prep_gs_sim                           true
% 3.41/0.98  --prep_unflatten                        true
% 3.41/0.98  --prep_res_sim                          true
% 3.41/0.98  --prep_upred                            true
% 3.41/0.98  --prep_sem_filter                       exhaustive
% 3.41/0.98  --prep_sem_filter_out                   false
% 3.41/0.98  --pred_elim                             true
% 3.41/0.98  --res_sim_input                         true
% 3.41/0.98  --eq_ax_congr_red                       true
% 3.41/0.98  --pure_diseq_elim                       true
% 3.41/0.98  --brand_transform                       false
% 3.41/0.98  --non_eq_to_eq                          false
% 3.41/0.98  --prep_def_merge                        true
% 3.41/0.98  --prep_def_merge_prop_impl              false
% 3.41/0.98  --prep_def_merge_mbd                    true
% 3.41/0.98  --prep_def_merge_tr_red                 false
% 3.41/0.98  --prep_def_merge_tr_cl                  false
% 3.41/0.98  --smt_preprocessing                     true
% 3.41/0.98  --smt_ac_axioms                         fast
% 3.41/0.98  --preprocessed_out                      false
% 3.41/0.98  --preprocessed_stats                    false
% 3.41/0.98  
% 3.41/0.98  ------ Abstraction refinement Options
% 3.41/0.98  
% 3.41/0.98  --abstr_ref                             []
% 3.41/0.98  --abstr_ref_prep                        false
% 3.41/0.98  --abstr_ref_until_sat                   false
% 3.41/0.98  --abstr_ref_sig_restrict                funpre
% 3.41/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.98  --abstr_ref_under                       []
% 3.41/0.98  
% 3.41/0.98  ------ SAT Options
% 3.41/0.98  
% 3.41/0.98  --sat_mode                              false
% 3.41/0.98  --sat_fm_restart_options                ""
% 3.41/0.98  --sat_gr_def                            false
% 3.41/0.98  --sat_epr_types                         true
% 3.41/0.98  --sat_non_cyclic_types                  false
% 3.41/0.98  --sat_finite_models                     false
% 3.41/0.98  --sat_fm_lemmas                         false
% 3.41/0.98  --sat_fm_prep                           false
% 3.41/0.98  --sat_fm_uc_incr                        true
% 3.41/0.98  --sat_out_model                         small
% 3.41/0.98  --sat_out_clauses                       false
% 3.41/0.98  
% 3.41/0.98  ------ QBF Options
% 3.41/0.98  
% 3.41/0.98  --qbf_mode                              false
% 3.41/0.98  --qbf_elim_univ                         false
% 3.41/0.98  --qbf_dom_inst                          none
% 3.41/0.98  --qbf_dom_pre_inst                      false
% 3.41/0.98  --qbf_sk_in                             false
% 3.41/0.98  --qbf_pred_elim                         true
% 3.41/0.98  --qbf_split                             512
% 3.41/0.98  
% 3.41/0.98  ------ BMC1 Options
% 3.41/0.98  
% 3.41/0.98  --bmc1_incremental                      false
% 3.41/0.98  --bmc1_axioms                           reachable_all
% 3.41/0.98  --bmc1_min_bound                        0
% 3.41/0.98  --bmc1_max_bound                        -1
% 3.41/0.98  --bmc1_max_bound_default                -1
% 3.41/0.98  --bmc1_symbol_reachability              true
% 3.41/0.98  --bmc1_property_lemmas                  false
% 3.41/0.98  --bmc1_k_induction                      false
% 3.41/0.98  --bmc1_non_equiv_states                 false
% 3.41/0.98  --bmc1_deadlock                         false
% 3.41/0.98  --bmc1_ucm                              false
% 3.41/0.98  --bmc1_add_unsat_core                   none
% 3.41/0.98  --bmc1_unsat_core_children              false
% 3.41/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.98  --bmc1_out_stat                         full
% 3.41/0.98  --bmc1_ground_init                      false
% 3.41/0.98  --bmc1_pre_inst_next_state              false
% 3.41/0.98  --bmc1_pre_inst_state                   false
% 3.41/0.98  --bmc1_pre_inst_reach_state             false
% 3.41/0.98  --bmc1_out_unsat_core                   false
% 3.41/0.98  --bmc1_aig_witness_out                  false
% 3.41/0.98  --bmc1_verbose                          false
% 3.41/0.98  --bmc1_dump_clauses_tptp                false
% 3.41/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.98  --bmc1_dump_file                        -
% 3.41/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.98  --bmc1_ucm_extend_mode                  1
% 3.41/0.98  --bmc1_ucm_init_mode                    2
% 3.41/0.98  --bmc1_ucm_cone_mode                    none
% 3.41/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.98  --bmc1_ucm_relax_model                  4
% 3.41/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.98  --bmc1_ucm_layered_model                none
% 3.41/0.98  --bmc1_ucm_max_lemma_size               10
% 3.41/0.98  
% 3.41/0.98  ------ AIG Options
% 3.41/0.98  
% 3.41/0.98  --aig_mode                              false
% 3.41/0.98  
% 3.41/0.98  ------ Instantiation Options
% 3.41/0.98  
% 3.41/0.98  --instantiation_flag                    true
% 3.41/0.98  --inst_sos_flag                         false
% 3.41/0.98  --inst_sos_phase                        true
% 3.41/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.98  --inst_lit_sel_side                     num_symb
% 3.41/0.98  --inst_solver_per_active                1400
% 3.41/0.98  --inst_solver_calls_frac                1.
% 3.41/0.98  --inst_passive_queue_type               priority_queues
% 3.41/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.98  --inst_passive_queues_freq              [25;2]
% 3.41/0.98  --inst_dismatching                      true
% 3.41/0.98  --inst_eager_unprocessed_to_passive     true
% 3.41/0.98  --inst_prop_sim_given                   true
% 3.41/0.98  --inst_prop_sim_new                     false
% 3.41/0.98  --inst_subs_new                         false
% 3.41/0.98  --inst_eq_res_simp                      false
% 3.41/0.98  --inst_subs_given                       false
% 3.41/0.98  --inst_orphan_elimination               true
% 3.41/0.98  --inst_learning_loop_flag               true
% 3.41/0.98  --inst_learning_start                   3000
% 3.41/0.98  --inst_learning_factor                  2
% 3.41/0.98  --inst_start_prop_sim_after_learn       3
% 3.41/0.98  --inst_sel_renew                        solver
% 3.41/0.98  --inst_lit_activity_flag                true
% 3.41/0.98  --inst_restr_to_given                   false
% 3.41/0.98  --inst_activity_threshold               500
% 3.41/0.98  --inst_out_proof                        true
% 3.41/0.98  
% 3.41/0.98  ------ Resolution Options
% 3.41/0.98  
% 3.41/0.98  --resolution_flag                       true
% 3.41/0.98  --res_lit_sel                           adaptive
% 3.41/0.98  --res_lit_sel_side                      none
% 3.41/0.98  --res_ordering                          kbo
% 3.41/0.98  --res_to_prop_solver                    active
% 3.41/0.98  --res_prop_simpl_new                    false
% 3.41/0.98  --res_prop_simpl_given                  true
% 3.41/0.98  --res_passive_queue_type                priority_queues
% 3.41/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.98  --res_passive_queues_freq               [15;5]
% 3.41/0.98  --res_forward_subs                      full
% 3.41/0.98  --res_backward_subs                     full
% 3.41/0.98  --res_forward_subs_resolution           true
% 3.41/0.98  --res_backward_subs_resolution          true
% 3.41/0.98  --res_orphan_elimination                true
% 3.41/0.98  --res_time_limit                        2.
% 3.41/0.98  --res_out_proof                         true
% 3.41/0.98  
% 3.41/0.98  ------ Superposition Options
% 3.41/0.98  
% 3.41/0.98  --superposition_flag                    true
% 3.41/0.98  --sup_passive_queue_type                priority_queues
% 3.41/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.98  --demod_completeness_check              fast
% 3.41/0.98  --demod_use_ground                      true
% 3.41/0.98  --sup_to_prop_solver                    passive
% 3.41/0.98  --sup_prop_simpl_new                    true
% 3.41/0.98  --sup_prop_simpl_given                  true
% 3.41/0.98  --sup_fun_splitting                     false
% 3.41/0.98  --sup_smt_interval                      50000
% 3.41/0.98  
% 3.41/0.98  ------ Superposition Simplification Setup
% 3.41/0.98  
% 3.41/0.98  --sup_indices_passive                   []
% 3.41/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.98  --sup_full_bw                           [BwDemod]
% 3.41/0.98  --sup_immed_triv                        [TrivRules]
% 3.41/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.98  --sup_immed_bw_main                     []
% 3.41/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  
% 3.41/0.99  ------ Combination Options
% 3.41/0.99  
% 3.41/0.99  --comb_res_mult                         3
% 3.41/0.99  --comb_sup_mult                         2
% 3.41/0.99  --comb_inst_mult                        10
% 3.41/0.99  
% 3.41/0.99  ------ Debug Options
% 3.41/0.99  
% 3.41/0.99  --dbg_backtrace                         false
% 3.41/0.99  --dbg_dump_prop_clauses                 false
% 3.41/0.99  --dbg_dump_prop_clauses_file            -
% 3.41/0.99  --dbg_out_stat                          false
% 3.41/0.99  ------ Parsing...
% 3.41/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/0.99  ------ Proving...
% 3.41/0.99  ------ Problem Properties 
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  clauses                                 37
% 3.41/0.99  conjectures                             4
% 3.41/0.99  EPR                                     3
% 3.41/0.99  Horn                                    25
% 3.41/0.99  unary                                   12
% 3.41/0.99  binary                                  6
% 3.41/0.99  lits                                    93
% 3.41/0.99  lits eq                                 60
% 3.41/0.99  fd_pure                                 0
% 3.41/0.99  fd_pseudo                               0
% 3.41/0.99  fd_cond                                 7
% 3.41/0.99  fd_pseudo_cond                          9
% 3.41/0.99  AC symbols                              0
% 3.41/0.99  
% 3.41/0.99  ------ Schedule dynamic 5 is on 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  Current options:
% 3.41/0.99  ------ 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options
% 3.41/0.99  
% 3.41/0.99  --out_options                           all
% 3.41/0.99  --tptp_safe_out                         true
% 3.41/0.99  --problem_path                          ""
% 3.41/0.99  --include_path                          ""
% 3.41/0.99  --clausifier                            res/vclausify_rel
% 3.41/0.99  --clausifier_options                    --mode clausify
% 3.41/0.99  --stdin                                 false
% 3.41/0.99  --stats_out                             all
% 3.41/0.99  
% 3.41/0.99  ------ General Options
% 3.41/0.99  
% 3.41/0.99  --fof                                   false
% 3.41/0.99  --time_out_real                         305.
% 3.41/0.99  --time_out_virtual                      -1.
% 3.41/0.99  --symbol_type_check                     false
% 3.41/0.99  --clausify_out                          false
% 3.41/0.99  --sig_cnt_out                           false
% 3.41/0.99  --trig_cnt_out                          false
% 3.41/0.99  --trig_cnt_out_tolerance                1.
% 3.41/0.99  --trig_cnt_out_sk_spl                   false
% 3.41/0.99  --abstr_cl_out                          false
% 3.41/0.99  
% 3.41/0.99  ------ Global Options
% 3.41/0.99  
% 3.41/0.99  --schedule                              default
% 3.41/0.99  --add_important_lit                     false
% 3.41/0.99  --prop_solver_per_cl                    1000
% 3.41/0.99  --min_unsat_core                        false
% 3.41/0.99  --soft_assumptions                      false
% 3.41/0.99  --soft_lemma_size                       3
% 3.41/0.99  --prop_impl_unit_size                   0
% 3.41/0.99  --prop_impl_unit                        []
% 3.41/0.99  --share_sel_clauses                     true
% 3.41/0.99  --reset_solvers                         false
% 3.41/0.99  --bc_imp_inh                            [conj_cone]
% 3.41/0.99  --conj_cone_tolerance                   3.
% 3.41/0.99  --extra_neg_conj                        none
% 3.41/0.99  --large_theory_mode                     true
% 3.41/0.99  --prolific_symb_bound                   200
% 3.41/0.99  --lt_threshold                          2000
% 3.41/0.99  --clause_weak_htbl                      true
% 3.41/0.99  --gc_record_bc_elim                     false
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing Options
% 3.41/0.99  
% 3.41/0.99  --preprocessing_flag                    true
% 3.41/0.99  --time_out_prep_mult                    0.1
% 3.41/0.99  --splitting_mode                        input
% 3.41/0.99  --splitting_grd                         true
% 3.41/0.99  --splitting_cvd                         false
% 3.41/0.99  --splitting_cvd_svl                     false
% 3.41/0.99  --splitting_nvd                         32
% 3.41/0.99  --sub_typing                            true
% 3.41/0.99  --prep_gs_sim                           true
% 3.41/0.99  --prep_unflatten                        true
% 3.41/0.99  --prep_res_sim                          true
% 3.41/0.99  --prep_upred                            true
% 3.41/0.99  --prep_sem_filter                       exhaustive
% 3.41/0.99  --prep_sem_filter_out                   false
% 3.41/0.99  --pred_elim                             true
% 3.41/0.99  --res_sim_input                         true
% 3.41/0.99  --eq_ax_congr_red                       true
% 3.41/0.99  --pure_diseq_elim                       true
% 3.41/0.99  --brand_transform                       false
% 3.41/0.99  --non_eq_to_eq                          false
% 3.41/0.99  --prep_def_merge                        true
% 3.41/0.99  --prep_def_merge_prop_impl              false
% 3.41/0.99  --prep_def_merge_mbd                    true
% 3.41/0.99  --prep_def_merge_tr_red                 false
% 3.41/0.99  --prep_def_merge_tr_cl                  false
% 3.41/0.99  --smt_preprocessing                     true
% 3.41/0.99  --smt_ac_axioms                         fast
% 3.41/0.99  --preprocessed_out                      false
% 3.41/0.99  --preprocessed_stats                    false
% 3.41/0.99  
% 3.41/0.99  ------ Abstraction refinement Options
% 3.41/0.99  
% 3.41/0.99  --abstr_ref                             []
% 3.41/0.99  --abstr_ref_prep                        false
% 3.41/0.99  --abstr_ref_until_sat                   false
% 3.41/0.99  --abstr_ref_sig_restrict                funpre
% 3.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.99  --abstr_ref_under                       []
% 3.41/0.99  
% 3.41/0.99  ------ SAT Options
% 3.41/0.99  
% 3.41/0.99  --sat_mode                              false
% 3.41/0.99  --sat_fm_restart_options                ""
% 3.41/0.99  --sat_gr_def                            false
% 3.41/0.99  --sat_epr_types                         true
% 3.41/0.99  --sat_non_cyclic_types                  false
% 3.41/0.99  --sat_finite_models                     false
% 3.41/0.99  --sat_fm_lemmas                         false
% 3.41/0.99  --sat_fm_prep                           false
% 3.41/0.99  --sat_fm_uc_incr                        true
% 3.41/0.99  --sat_out_model                         small
% 3.41/0.99  --sat_out_clauses                       false
% 3.41/0.99  
% 3.41/0.99  ------ QBF Options
% 3.41/0.99  
% 3.41/0.99  --qbf_mode                              false
% 3.41/0.99  --qbf_elim_univ                         false
% 3.41/0.99  --qbf_dom_inst                          none
% 3.41/0.99  --qbf_dom_pre_inst                      false
% 3.41/0.99  --qbf_sk_in                             false
% 3.41/0.99  --qbf_pred_elim                         true
% 3.41/0.99  --qbf_split                             512
% 3.41/0.99  
% 3.41/0.99  ------ BMC1 Options
% 3.41/0.99  
% 3.41/0.99  --bmc1_incremental                      false
% 3.41/0.99  --bmc1_axioms                           reachable_all
% 3.41/0.99  --bmc1_min_bound                        0
% 3.41/0.99  --bmc1_max_bound                        -1
% 3.41/0.99  --bmc1_max_bound_default                -1
% 3.41/0.99  --bmc1_symbol_reachability              true
% 3.41/0.99  --bmc1_property_lemmas                  false
% 3.41/0.99  --bmc1_k_induction                      false
% 3.41/0.99  --bmc1_non_equiv_states                 false
% 3.41/0.99  --bmc1_deadlock                         false
% 3.41/0.99  --bmc1_ucm                              false
% 3.41/0.99  --bmc1_add_unsat_core                   none
% 3.41/0.99  --bmc1_unsat_core_children              false
% 3.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.99  --bmc1_out_stat                         full
% 3.41/0.99  --bmc1_ground_init                      false
% 3.41/0.99  --bmc1_pre_inst_next_state              false
% 3.41/0.99  --bmc1_pre_inst_state                   false
% 3.41/0.99  --bmc1_pre_inst_reach_state             false
% 3.41/0.99  --bmc1_out_unsat_core                   false
% 3.41/0.99  --bmc1_aig_witness_out                  false
% 3.41/0.99  --bmc1_verbose                          false
% 3.41/0.99  --bmc1_dump_clauses_tptp                false
% 3.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.99  --bmc1_dump_file                        -
% 3.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.99  --bmc1_ucm_extend_mode                  1
% 3.41/0.99  --bmc1_ucm_init_mode                    2
% 3.41/0.99  --bmc1_ucm_cone_mode                    none
% 3.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.99  --bmc1_ucm_relax_model                  4
% 3.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.99  --bmc1_ucm_layered_model                none
% 3.41/0.99  --bmc1_ucm_max_lemma_size               10
% 3.41/0.99  
% 3.41/0.99  ------ AIG Options
% 3.41/0.99  
% 3.41/0.99  --aig_mode                              false
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation Options
% 3.41/0.99  
% 3.41/0.99  --instantiation_flag                    true
% 3.41/0.99  --inst_sos_flag                         false
% 3.41/0.99  --inst_sos_phase                        true
% 3.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel_side                     none
% 3.41/0.99  --inst_solver_per_active                1400
% 3.41/0.99  --inst_solver_calls_frac                1.
% 3.41/0.99  --inst_passive_queue_type               priority_queues
% 3.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.99  --inst_passive_queues_freq              [25;2]
% 3.41/0.99  --inst_dismatching                      true
% 3.41/0.99  --inst_eager_unprocessed_to_passive     true
% 3.41/0.99  --inst_prop_sim_given                   true
% 3.41/0.99  --inst_prop_sim_new                     false
% 3.41/0.99  --inst_subs_new                         false
% 3.41/0.99  --inst_eq_res_simp                      false
% 3.41/0.99  --inst_subs_given                       false
% 3.41/0.99  --inst_orphan_elimination               true
% 3.41/0.99  --inst_learning_loop_flag               true
% 3.41/0.99  --inst_learning_start                   3000
% 3.41/0.99  --inst_learning_factor                  2
% 3.41/0.99  --inst_start_prop_sim_after_learn       3
% 3.41/0.99  --inst_sel_renew                        solver
% 3.41/0.99  --inst_lit_activity_flag                true
% 3.41/0.99  --inst_restr_to_given                   false
% 3.41/0.99  --inst_activity_threshold               500
% 3.41/0.99  --inst_out_proof                        true
% 3.41/0.99  
% 3.41/0.99  ------ Resolution Options
% 3.41/0.99  
% 3.41/0.99  --resolution_flag                       false
% 3.41/0.99  --res_lit_sel                           adaptive
% 3.41/0.99  --res_lit_sel_side                      none
% 3.41/0.99  --res_ordering                          kbo
% 3.41/0.99  --res_to_prop_solver                    active
% 3.41/0.99  --res_prop_simpl_new                    false
% 3.41/0.99  --res_prop_simpl_given                  true
% 3.41/0.99  --res_passive_queue_type                priority_queues
% 3.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.99  --res_passive_queues_freq               [15;5]
% 3.41/0.99  --res_forward_subs                      full
% 3.41/0.99  --res_backward_subs                     full
% 3.41/0.99  --res_forward_subs_resolution           true
% 3.41/0.99  --res_backward_subs_resolution          true
% 3.41/0.99  --res_orphan_elimination                true
% 3.41/0.99  --res_time_limit                        2.
% 3.41/0.99  --res_out_proof                         true
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Options
% 3.41/0.99  
% 3.41/0.99  --superposition_flag                    true
% 3.41/0.99  --sup_passive_queue_type                priority_queues
% 3.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.99  --demod_completeness_check              fast
% 3.41/0.99  --demod_use_ground                      true
% 3.41/0.99  --sup_to_prop_solver                    passive
% 3.41/0.99  --sup_prop_simpl_new                    true
% 3.41/0.99  --sup_prop_simpl_given                  true
% 3.41/0.99  --sup_fun_splitting                     false
% 3.41/0.99  --sup_smt_interval                      50000
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Simplification Setup
% 3.41/0.99  
% 3.41/0.99  --sup_indices_passive                   []
% 3.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_full_bw                           [BwDemod]
% 3.41/0.99  --sup_immed_triv                        [TrivRules]
% 3.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_immed_bw_main                     []
% 3.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  
% 3.41/0.99  ------ Combination Options
% 3.41/0.99  
% 3.41/0.99  --comb_res_mult                         3
% 3.41/0.99  --comb_sup_mult                         2
% 3.41/0.99  --comb_inst_mult                        10
% 3.41/0.99  
% 3.41/0.99  ------ Debug Options
% 3.41/0.99  
% 3.41/0.99  --dbg_backtrace                         false
% 3.41/0.99  --dbg_dump_prop_clauses                 false
% 3.41/0.99  --dbg_dump_prop_clauses_file            -
% 3.41/0.99  --dbg_out_stat                          false
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ Proving...
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS status Theorem for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  fof(f16,conjecture,(
% 3.41/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f17,negated_conjecture,(
% 3.41/0.99    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.41/0.99    inference(negated_conjecture,[],[f16])).
% 3.41/0.99  
% 3.41/0.99  fof(f23,plain,(
% 3.41/0.99    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.41/0.99    inference(ennf_transformation,[],[f17])).
% 3.41/0.99  
% 3.41/0.99  fof(f43,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK7) = sK7 | k6_mcart_1(X0,X1,X2,sK7) = sK7 | k5_mcart_1(X0,X1,X2,sK7) = sK7) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f42,plain,(
% 3.41/0.99    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK4,sK5,sK6,X3) = X3 | k6_mcart_1(sK4,sK5,sK6,X3) = X3 | k5_mcart_1(sK4,sK5,sK6,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK4,sK5,sK6))) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4)),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f44,plain,(
% 3.41/0.99    ((k7_mcart_1(sK4,sK5,sK6,sK7) = sK7 | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7 | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7) & m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f23,f43,f42])).
% 3.41/0.99  
% 3.41/0.99  fof(f87,plain,(
% 3.41/0.99    k7_mcart_1(sK4,sK5,sK6,sK7) = sK7 | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7 | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7),
% 3.41/0.99    inference(cnf_transformation,[],[f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f14,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f22,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.41/0.99    inference(ennf_transformation,[],[f14])).
% 3.41/0.99  
% 3.41/0.99  fof(f80,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f22])).
% 3.41/0.99  
% 3.41/0.99  fof(f10,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f71,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f10])).
% 3.41/0.99  
% 3.41/0.99  fof(f105,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(definition_unfolding,[],[f80,f71])).
% 3.41/0.99  
% 3.41/0.99  fof(f86,plain,(
% 3.41/0.99    m1_subset_1(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 3.41/0.99    inference(cnf_transformation,[],[f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f108,plain,(
% 3.41/0.99    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 3.41/0.99    inference(definition_unfolding,[],[f86,f71])).
% 3.41/0.99  
% 3.41/0.99  fof(f83,plain,(
% 3.41/0.99    k1_xboole_0 != sK4),
% 3.41/0.99    inference(cnf_transformation,[],[f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f84,plain,(
% 3.41/0.99    k1_xboole_0 != sK5),
% 3.41/0.99    inference(cnf_transformation,[],[f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f85,plain,(
% 3.41/0.99    k1_xboole_0 != sK6),
% 3.41/0.99    inference(cnf_transformation,[],[f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f5,axiom,(
% 3.41/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f34,plain,(
% 3.41/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.41/0.99    inference(nnf_transformation,[],[f5])).
% 3.41/0.99  
% 3.41/0.99  fof(f35,plain,(
% 3.41/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.41/0.99    inference(rectify,[],[f34])).
% 3.41/0.99  
% 3.41/0.99  fof(f36,plain,(
% 3.41/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f37,plain,(
% 3.41/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 3.41/0.99  
% 3.41/0.99  fof(f61,plain,(
% 3.41/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.41/0.99    inference(cnf_transformation,[],[f37])).
% 3.41/0.99  
% 3.41/0.99  fof(f6,axiom,(
% 3.41/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f65,plain,(
% 3.41/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f6])).
% 3.41/0.99  
% 3.41/0.99  fof(f7,axiom,(
% 3.41/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f66,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f7])).
% 3.41/0.99  
% 3.41/0.99  fof(f88,plain,(
% 3.41/0.99    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f65,f66])).
% 3.41/0.99  
% 3.41/0.99  fof(f98,plain,(
% 3.41/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.41/0.99    inference(definition_unfolding,[],[f61,f88])).
% 3.41/0.99  
% 3.41/0.99  fof(f121,plain,(
% 3.41/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.41/0.99    inference(equality_resolution,[],[f98])).
% 3.41/0.99  
% 3.41/0.99  fof(f62,plain,(
% 3.41/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.41/0.99    inference(cnf_transformation,[],[f37])).
% 3.41/0.99  
% 3.41/0.99  fof(f97,plain,(
% 3.41/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 3.41/0.99    inference(definition_unfolding,[],[f62,f88])).
% 3.41/0.99  
% 3.41/0.99  fof(f119,plain,(
% 3.41/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 3.41/0.99    inference(equality_resolution,[],[f97])).
% 3.41/0.99  
% 3.41/0.99  fof(f120,plain,(
% 3.41/0.99    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 3.41/0.99    inference(equality_resolution,[],[f119])).
% 3.41/0.99  
% 3.41/0.99  fof(f79,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f22])).
% 3.41/0.99  
% 3.41/0.99  fof(f106,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(definition_unfolding,[],[f79,f71])).
% 3.41/0.99  
% 3.41/0.99  fof(f78,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f22])).
% 3.41/0.99  
% 3.41/0.99  fof(f107,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(definition_unfolding,[],[f78,f71])).
% 3.41/0.99  
% 3.41/0.99  fof(f13,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f21,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.41/0.99    inference(ennf_transformation,[],[f13])).
% 3.41/0.99  
% 3.41/0.99  fof(f77,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f21])).
% 3.41/0.99  
% 3.41/0.99  fof(f9,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f70,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f9])).
% 3.41/0.99  
% 3.41/0.99  fof(f104,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(definition_unfolding,[],[f77,f70,f71])).
% 3.41/0.99  
% 3.41/0.99  fof(f15,axiom,(
% 3.41/0.99    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f81,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f15])).
% 3.41/0.99  
% 3.41/0.99  fof(f11,axiom,(
% 3.41/0.99    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f19,plain,(
% 3.41/0.99    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 3.41/0.99    inference(ennf_transformation,[],[f11])).
% 3.41/0.99  
% 3.41/0.99  fof(f73,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f19])).
% 3.41/0.99  
% 3.41/0.99  fof(f122,plain,(
% 3.41/0.99    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 3.41/0.99    inference(equality_resolution,[],[f73])).
% 3.41/0.99  
% 3.41/0.99  fof(f82,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.41/0.99    inference(cnf_transformation,[],[f15])).
% 3.41/0.99  
% 3.41/0.99  fof(f12,axiom,(
% 3.41/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f20,plain,(
% 3.41/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.41/0.99    inference(ennf_transformation,[],[f12])).
% 3.41/0.99  
% 3.41/0.99  fof(f40,plain,(
% 3.41/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f41,plain,(
% 3.41/0.99    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f40])).
% 3.41/0.99  
% 3.41/0.99  fof(f74,plain,(
% 3.41/0.99    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f41])).
% 3.41/0.99  
% 3.41/0.99  fof(f75,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f41])).
% 3.41/0.99  
% 3.41/0.99  fof(f103,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(definition_unfolding,[],[f75,f70])).
% 3.41/0.99  
% 3.41/0.99  fof(f4,axiom,(
% 3.41/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f18,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.41/0.99    inference(ennf_transformation,[],[f4])).
% 3.41/0.99  
% 3.41/0.99  fof(f29,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.41/0.99    inference(nnf_transformation,[],[f18])).
% 3.41/0.99  
% 3.41/0.99  fof(f30,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.41/0.99    inference(flattening,[],[f29])).
% 3.41/0.99  
% 3.41/0.99  fof(f31,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.41/0.99    inference(rectify,[],[f30])).
% 3.41/0.99  
% 3.41/0.99  fof(f32,plain,(
% 3.41/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f33,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.41/0.99  
% 3.41/0.99  fof(f54,plain,(
% 3.41/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.41/0.99    inference(cnf_transformation,[],[f33])).
% 3.41/0.99  
% 3.41/0.99  fof(f116,plain,(
% 3.41/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 3.41/0.99    inference(equality_resolution,[],[f54])).
% 3.41/0.99  
% 3.41/0.99  fof(f117,plain,(
% 3.41/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 3.41/0.99    inference(equality_resolution,[],[f116])).
% 3.41/0.99  
% 3.41/0.99  fof(f8,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f38,plain,(
% 3.41/0.99    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.41/0.99    inference(nnf_transformation,[],[f8])).
% 3.41/0.99  
% 3.41/0.99  fof(f39,plain,(
% 3.41/0.99    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 3.41/0.99    inference(flattening,[],[f38])).
% 3.41/0.99  
% 3.41/0.99  fof(f68,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f39])).
% 3.41/0.99  
% 3.41/0.99  fof(f100,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f68,f66,f66])).
% 3.41/0.99  
% 3.41/0.99  fof(f2,axiom,(
% 3.41/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f51,plain,(
% 3.41/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f2])).
% 3.41/0.99  
% 3.41/0.99  fof(f76,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f41])).
% 3.41/0.99  
% 3.41/0.99  fof(f102,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(definition_unfolding,[],[f76,f70])).
% 3.41/0.99  
% 3.41/0.99  cnf(c_33,negated_conjecture,
% 3.41/0.99      ( k7_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.41/0.99      | k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.41/0.99      | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7 ),
% 3.41/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_28,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.41/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2
% 3.41/0.99      | k1_xboole_0 = X3 ),
% 3.41/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_34,negated_conjecture,
% 3.41/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 3.41/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_366,plain,
% 3.41/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.41/0.99      | sK7 != X3
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_34]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_367,plain,
% 3.41/0.99      ( k7_mcart_1(X0,X1,X2,sK7) = k2_mcart_1(sK7)
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_366]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1349,plain,
% 3.41/0.99      ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7)
% 3.41/0.99      | sK6 = k1_xboole_0
% 3.41/0.99      | sK5 = k1_xboole_0
% 3.41/0.99      | sK4 = k1_xboole_0 ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_367]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_37,negated_conjecture,
% 3.41/0.99      ( k1_xboole_0 != sK4 ),
% 3.41/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_36,negated_conjecture,
% 3.41/0.99      ( k1_xboole_0 != sK5 ),
% 3.41/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_35,negated_conjecture,
% 3.41/0.99      ( k1_xboole_0 != sK6 ),
% 3.41/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_18,plain,
% 3.41/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.41/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_70,plain,
% 3.41/0.99      ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.41/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_17,plain,
% 3.41/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 3.41/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_73,plain,
% 3.41/0.99      ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_586,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1273,plain,
% 3.41/0.99      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_586]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1274,plain,
% 3.41/0.99      ( sK6 != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = sK6
% 3.41/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1273]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1275,plain,
% 3.41/0.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_586]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1276,plain,
% 3.41/0.99      ( sK5 != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = sK5
% 3.41/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1275]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1277,plain,
% 3.41/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_586]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1278,plain,
% 3.41/0.99      ( sK4 != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = sK4
% 3.41/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1277]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1553,plain,
% 3.41/0.99      ( k7_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(sK7) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_1349,c_37,c_36,c_35,c_70,c_73,c_1274,c_1276,c_1278]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1556,plain,
% 3.41/0.99      ( k6_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.41/0.99      | k5_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.41/0.99      | k2_mcart_1(sK7) = sK7 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_33,c_1553]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_29,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.41/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2
% 3.41/0.99      | k1_xboole_0 = X3 ),
% 3.41/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_348,plain,
% 3.41/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.41/0.99      | sK7 != X3
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_349,plain,
% 3.41/0.99      ( k6_mcart_1(X0,X1,X2,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_348]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1361,plain,
% 3.41/0.99      ( k6_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 3.41/0.99      | sK6 = k1_xboole_0
% 3.41/0.99      | sK5 = k1_xboole_0
% 3.41/0.99      | sK4 = k1_xboole_0 ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_349]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1899,plain,
% 3.41/0.99      ( k6_mcart_1(sK4,sK5,sK6,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_1361,c_37,c_36,c_35,c_70,c_73,c_1274,c_1276,c_1278]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1902,plain,
% 3.41/0.99      ( k5_mcart_1(sK4,sK5,sK6,sK7) = sK7
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | k2_mcart_1(sK7) = sK7 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1556,c_1899]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_30,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.41/0.99      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2
% 3.41/0.99      | k1_xboole_0 = X3 ),
% 3.41/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_330,plain,
% 3.41/0.99      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.41/0.99      | sK7 != X3
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_331,plain,
% 3.41/0.99      ( k5_mcart_1(X0,X1,X2,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_330]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1355,plain,
% 3.41/0.99      ( k5_mcart_1(sK4,sK5,sK6,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.41/0.99      | sK6 = k1_xboole_0
% 3.41/0.99      | sK5 = k1_xboole_0
% 3.41/0.99      | sK4 = k1_xboole_0 ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_331]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1605,plain,
% 3.41/0.99      ( k5_mcart_1(sK4,sK5,sK6,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_1355,c_37,c_36,c_35,c_70,c_73,c_1274,c_1276,c_1278]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1904,plain,
% 3.41/0.99      ( k1_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | k2_mcart_1(sK7) = sK7 ),
% 3.41/0.99      inference(demodulation,[status(thm)],[c_1902,c_1605]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_27,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.41/0.99      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2
% 3.41/0.99      | k1_xboole_0 = X3 ),
% 3.41/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_384,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.41/0.99      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 3.41/0.99      | sK7 != X3
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_385,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.41/0.99      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK7),k6_mcart_1(X0,X1,X2,sK7)),k7_mcart_1(X0,X1,X2,sK7)) = sK7
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_384]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1367,plain,
% 3.41/0.99      ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7
% 3.41/0.99      | sK6 = k1_xboole_0
% 3.41/0.99      | sK5 = k1_xboole_0
% 3.41/0.99      | sK4 = k1_xboole_0 ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_385]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1905,plain,
% 3.41/0.99      ( k4_tarski(k4_tarski(k5_mcart_1(sK4,sK5,sK6,sK7),k6_mcart_1(sK4,sK5,sK6,sK7)),k7_mcart_1(sK4,sK5,sK6,sK7)) = sK7 ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_1367,c_37,c_36,c_35,c_70,c_73,c_1274,c_1276,c_1278]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1907,plain,
% 3.41/0.99      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))),k2_mcart_1(sK7)) = sK7 ),
% 3.41/0.99      inference(light_normalisation,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_1905,c_1553,c_1605,c_1899]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_32,plain,
% 3.41/0.99      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1910,plain,
% 3.41/0.99      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1907,c_32]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2636,plain,
% 3.41/0.99      ( k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | k2_mcart_1(sK7) = sK7 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1904,c_1910]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1912,plain,
% 3.41/0.99      ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
% 3.41/0.99      inference(demodulation,[status(thm)],[c_1910,c_1907]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_22,plain,
% 3.41/0.99      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_31,plain,
% 3.41/0.99      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.41/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1015,plain,
% 3.41/0.99      ( k4_tarski(X0,X1) != X1 ),
% 3.41/0.99      inference(light_normalisation,[status(thm)],[c_22,c_31]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2293,plain,
% 3.41/0.99      ( k2_mcart_1(sK7) != sK7 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1912,c_1015]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2657,plain,
% 3.41/0.99      ( k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_2636,c_2293]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2658,plain,
% 3.41/0.99      ( k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_2657]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_26,plain,
% 3.41/0.99      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_968,plain,
% 3.41/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_974,plain,
% 3.41/0.99      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3026,plain,
% 3.41/0.99      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.41/0.99      | sK3(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_968,c_974]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_25,plain,
% 3.41/0.99      ( ~ r2_hidden(X0,X1)
% 3.41/0.99      | k4_tarski(k4_tarski(X0,X2),X3) != sK3(X1)
% 3.41/0.99      | k1_xboole_0 = X1 ),
% 3.41/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_969,plain,
% 3.41/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) != sK3(X3)
% 3.41/0.99      | k1_xboole_0 = X3
% 3.41/0.99      | r2_hidden(X0,X3) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2230,plain,
% 3.41/0.99      ( k4_tarski(sK7,X0) != sK3(X1)
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | r2_hidden(k1_mcart_1(sK7),X1) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1912,c_969]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3409,plain,
% 3.41/0.99      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.41/0.99      | k4_tarski(sK7,X1) != X0
% 3.41/0.99      | r2_hidden(k1_mcart_1(sK7),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_3026,c_2230]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3763,plain,
% 3.41/0.99      ( k1_enumset1(k4_tarski(sK7,X0),k4_tarski(sK7,X0),k4_tarski(sK7,X0)) = k1_xboole_0
% 3.41/0.99      | r2_hidden(k1_mcart_1(sK7),k1_enumset1(k4_tarski(sK7,X0),k4_tarski(sK7,X0),k4_tarski(sK7,X0))) != iProver_top ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_3409]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5050,plain,
% 3.41/0.99      ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) = k1_xboole_0
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | r2_hidden(k1_mcart_1(sK7),k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7))) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_2658,c_3763]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_13,plain,
% 3.41/0.99      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 3.41/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_979,plain,
% 3.41/0.99      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5058,plain,
% 3.41/0.99      ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) = k1_xboole_0
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
% 3.41/0.99      inference(forward_subsumption_resolution,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_5050,c_979]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_20,plain,
% 3.41/0.99      ( ~ r2_hidden(X0,X1)
% 3.41/0.99      | k4_xboole_0(k1_enumset1(X2,X2,X0),X1) != k1_enumset1(X2,X2,X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_972,plain,
% 3.41/0.99      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
% 3.41/0.99      | r2_hidden(X1,X2) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5070,plain,
% 3.41/0.99      ( k1_enumset1(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7)))) != k4_xboole_0(k1_xboole_0,X0)
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),X0) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5058,c_972]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6559,plain,
% 3.41/0.99      ( k1_enumset1(k1_mcart_1(sK7),k1_mcart_1(sK7),k1_mcart_1(sK7)) != k4_xboole_0(k1_xboole_0,X0)
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),X0) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_2658,c_5070]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6,plain,
% 3.41/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_93,plain,
% 3.41/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5062,plain,
% 3.41/0.99      ( k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k1_xboole_0) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5058,c_979]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6558,plain,
% 3.41/0.99      ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),X0) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5058,c_5070]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6575,plain,
% 3.41/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.41/0.99      | k2_mcart_1(k1_mcart_1(sK7)) = sK7
% 3.41/0.99      | r2_hidden(k4_tarski(sK7,k2_mcart_1(k1_mcart_1(sK7))),k1_xboole_0) != iProver_top ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_6558]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6677,plain,
% 3.41/0.99      ( k2_mcart_1(k1_mcart_1(sK7)) = sK7 ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_6559,c_93,c_5062,c_6575]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_24,plain,
% 3.41/0.99      ( ~ r2_hidden(X0,X1)
% 3.41/0.99      | k4_tarski(k4_tarski(X2,X0),X3) != sK3(X1)
% 3.41/0.99      | k1_xboole_0 = X1 ),
% 3.41/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_970,plain,
% 3.41/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) != sK3(X3)
% 3.41/0.99      | k1_xboole_0 = X3
% 3.41/0.99      | r2_hidden(X1,X3) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2906,plain,
% 3.41/0.99      ( k4_tarski(k1_mcart_1(sK7),X0) != sK3(X1)
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X1) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1910,c_970]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3162,plain,
% 3.41/0.99      ( sK3(X0) != sK7
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),X0) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1912,c_2906]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3402,plain,
% 3.41/0.99      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.41/0.99      | sK7 != X0
% 3.41/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_3026,c_3162]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3693,plain,
% 3.41/0.99      ( k1_enumset1(sK7,sK7,sK7) = k1_xboole_0
% 3.41/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),k1_enumset1(sK7,sK7,sK7)) != iProver_top ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_3402]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6683,plain,
% 3.41/0.99      ( k1_enumset1(sK7,sK7,sK7) = k1_xboole_0
% 3.41/0.99      | r2_hidden(sK7,k1_enumset1(sK7,sK7,sK7)) != iProver_top ),
% 3.41/0.99      inference(demodulation,[status(thm)],[c_6677,c_3693]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6885,plain,
% 3.41/0.99      ( k1_enumset1(sK7,sK7,sK7) = k1_xboole_0 ),
% 3.41/0.99      inference(forward_subsumption_resolution,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_6683,c_979]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6892,plain,
% 3.41/0.99      ( k1_enumset1(sK7,sK7,sK7) != k4_xboole_0(k1_xboole_0,X0)
% 3.41/0.99      | r2_hidden(sK7,X0) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_6885,c_972]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6894,plain,
% 3.41/0.99      ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
% 3.41/0.99      | r2_hidden(sK7,X0) != iProver_top ),
% 3.41/0.99      inference(light_normalisation,[status(thm)],[c_6892,c_6885]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6903,plain,
% 3.41/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.41/0.99      | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_6894]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6886,plain,
% 3.41/0.99      ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_6885,c_979]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(contradiction,plain,
% 3.41/0.99      ( $false ),
% 3.41/0.99      inference(minisat,[status(thm)],[c_6903,c_6886,c_93]) ).
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  ------                               Statistics
% 3.41/0.99  
% 3.41/0.99  ------ General
% 3.41/0.99  
% 3.41/0.99  abstr_ref_over_cycles:                  0
% 3.41/0.99  abstr_ref_under_cycles:                 0
% 3.41/0.99  gc_basic_clause_elim:                   0
% 3.41/0.99  forced_gc_time:                         0
% 3.41/0.99  parsing_time:                           0.011
% 3.41/0.99  unif_index_cands_time:                  0.
% 3.41/0.99  unif_index_add_time:                    0.
% 3.41/0.99  orderings_time:                         0.
% 3.41/0.99  out_proof_time:                         0.011
% 3.41/0.99  total_time:                             0.236
% 3.41/0.99  num_of_symbols:                         51
% 3.41/0.99  num_of_terms:                           8794
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing
% 3.41/0.99  
% 3.41/0.99  num_of_splits:                          0
% 3.41/0.99  num_of_split_atoms:                     0
% 3.41/0.99  num_of_reused_defs:                     0
% 3.41/0.99  num_eq_ax_congr_red:                    39
% 3.41/0.99  num_of_sem_filtered_clauses:            1
% 3.41/0.99  num_of_subtypes:                        0
% 3.41/0.99  monotx_restored_types:                  0
% 3.41/0.99  sat_num_of_epr_types:                   0
% 3.41/0.99  sat_num_of_non_cyclic_types:            0
% 3.41/0.99  sat_guarded_non_collapsed_types:        0
% 3.41/0.99  num_pure_diseq_elim:                    0
% 3.41/0.99  simp_replaced_by:                       0
% 3.41/0.99  res_preprocessed:                       172
% 3.41/0.99  prep_upred:                             0
% 3.41/0.99  prep_unflattend:                        4
% 3.41/0.99  smt_new_axioms:                         0
% 3.41/0.99  pred_elim_cands:                        1
% 3.41/0.99  pred_elim:                              1
% 3.41/0.99  pred_elim_cl:                           1
% 3.41/0.99  pred_elim_cycles:                       3
% 3.41/0.99  merged_defs:                            0
% 3.41/0.99  merged_defs_ncl:                        0
% 3.41/0.99  bin_hyper_res:                          0
% 3.41/0.99  prep_cycles:                            4
% 3.41/0.99  pred_elim_time:                         0.003
% 3.41/0.99  splitting_time:                         0.
% 3.41/0.99  sem_filter_time:                        0.
% 3.41/0.99  monotx_time:                            0.
% 3.41/0.99  subtype_inf_time:                       0.
% 3.41/0.99  
% 3.41/0.99  ------ Problem properties
% 3.41/0.99  
% 3.41/0.99  clauses:                                37
% 3.41/0.99  conjectures:                            4
% 3.41/0.99  epr:                                    3
% 3.41/0.99  horn:                                   25
% 3.41/0.99  ground:                                 4
% 3.41/0.99  unary:                                  12
% 3.41/0.99  binary:                                 6
% 3.41/0.99  lits:                                   93
% 3.41/0.99  lits_eq:                                60
% 3.41/0.99  fd_pure:                                0
% 3.41/0.99  fd_pseudo:                              0
% 3.41/0.99  fd_cond:                                7
% 3.41/0.99  fd_pseudo_cond:                         9
% 3.41/0.99  ac_symbols:                             0
% 3.41/0.99  
% 3.41/0.99  ------ Propositional Solver
% 3.41/0.99  
% 3.41/0.99  prop_solver_calls:                      27
% 3.41/0.99  prop_fast_solver_calls:                 1152
% 3.41/0.99  smt_solver_calls:                       0
% 3.41/0.99  smt_fast_solver_calls:                  0
% 3.41/0.99  prop_num_of_clauses:                    2603
% 3.41/0.99  prop_preprocess_simplified:             9114
% 3.41/0.99  prop_fo_subsumed:                       16
% 3.41/0.99  prop_solver_time:                       0.
% 3.41/0.99  smt_solver_time:                        0.
% 3.41/0.99  smt_fast_solver_time:                   0.
% 3.41/0.99  prop_fast_solver_time:                  0.
% 3.41/0.99  prop_unsat_core_time:                   0.
% 3.41/0.99  
% 3.41/0.99  ------ QBF
% 3.41/0.99  
% 3.41/0.99  qbf_q_res:                              0
% 3.41/0.99  qbf_num_tautologies:                    0
% 3.41/0.99  qbf_prep_cycles:                        0
% 3.41/0.99  
% 3.41/0.99  ------ BMC1
% 3.41/0.99  
% 3.41/0.99  bmc1_current_bound:                     -1
% 3.41/0.99  bmc1_last_solved_bound:                 -1
% 3.41/0.99  bmc1_unsat_core_size:                   -1
% 3.41/0.99  bmc1_unsat_core_parents_size:           -1
% 3.41/0.99  bmc1_merge_next_fun:                    0
% 3.41/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation
% 3.41/0.99  
% 3.41/0.99  inst_num_of_clauses:                    953
% 3.41/0.99  inst_num_in_passive:                    491
% 3.41/0.99  inst_num_in_active:                     423
% 3.41/0.99  inst_num_in_unprocessed:                39
% 3.41/0.99  inst_num_of_loops:                      430
% 3.41/0.99  inst_num_of_learning_restarts:          0
% 3.41/0.99  inst_num_moves_active_passive:          6
% 3.41/0.99  inst_lit_activity:                      0
% 3.41/0.99  inst_lit_activity_moves:                0
% 3.41/0.99  inst_num_tautologies:                   0
% 3.41/0.99  inst_num_prop_implied:                  0
% 3.41/0.99  inst_num_existing_simplified:           0
% 3.41/0.99  inst_num_eq_res_simplified:             0
% 3.41/0.99  inst_num_child_elim:                    0
% 3.41/0.99  inst_num_of_dismatching_blockings:      83
% 3.41/0.99  inst_num_of_non_proper_insts:           968
% 3.41/0.99  inst_num_of_duplicates:                 0
% 3.41/0.99  inst_inst_num_from_inst_to_res:         0
% 3.41/0.99  inst_dismatching_checking_time:         0.
% 3.41/0.99  
% 3.41/0.99  ------ Resolution
% 3.41/0.99  
% 3.41/0.99  res_num_of_clauses:                     0
% 3.41/0.99  res_num_in_passive:                     0
% 3.41/0.99  res_num_in_active:                      0
% 3.41/0.99  res_num_of_loops:                       176
% 3.41/0.99  res_forward_subset_subsumed:            42
% 3.41/0.99  res_backward_subset_subsumed:           0
% 3.41/0.99  res_forward_subsumed:                   0
% 3.41/0.99  res_backward_subsumed:                  0
% 3.41/0.99  res_forward_subsumption_resolution:     0
% 3.41/0.99  res_backward_subsumption_resolution:    0
% 3.41/0.99  res_clause_to_clause_subsumption:       1028
% 3.41/0.99  res_orphan_elimination:                 0
% 3.41/0.99  res_tautology_del:                      0
% 3.41/0.99  res_num_eq_res_simplified:              0
% 3.41/0.99  res_num_sel_changes:                    0
% 3.41/0.99  res_moves_from_active_to_pass:          0
% 3.41/0.99  
% 3.41/0.99  ------ Superposition
% 3.41/0.99  
% 3.41/0.99  sup_time_total:                         0.
% 3.41/0.99  sup_time_generating:                    0.
% 3.41/0.99  sup_time_sim_full:                      0.
% 3.41/0.99  sup_time_sim_immed:                     0.
% 3.41/0.99  
% 3.41/0.99  sup_num_of_clauses:                     154
% 3.41/0.99  sup_num_in_active:                      59
% 3.41/0.99  sup_num_in_passive:                     95
% 3.41/0.99  sup_num_of_loops:                       84
% 3.41/0.99  sup_fw_superposition:                   74
% 3.41/0.99  sup_bw_superposition:                   127
% 3.41/0.99  sup_immediate_simplified:               27
% 3.41/0.99  sup_given_eliminated:                   1
% 3.41/0.99  comparisons_done:                       0
% 3.41/0.99  comparisons_avoided:                    14
% 3.41/0.99  
% 3.41/0.99  ------ Simplifications
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  sim_fw_subset_subsumed:                 12
% 3.41/0.99  sim_bw_subset_subsumed:                 11
% 3.41/0.99  sim_fw_subsumed:                        5
% 3.41/0.99  sim_bw_subsumed:                        2
% 3.41/0.99  sim_fw_subsumption_res:                 4
% 3.41/0.99  sim_bw_subsumption_res:                 0
% 3.41/0.99  sim_tautology_del:                      4
% 3.41/0.99  sim_eq_tautology_del:                   15
% 3.41/0.99  sim_eq_res_simp:                        3
% 3.41/0.99  sim_fw_demodulated:                     4
% 3.41/0.99  sim_bw_demodulated:                     22
% 3.41/0.99  sim_light_normalised:                   8
% 3.41/0.99  sim_joinable_taut:                      0
% 3.41/0.99  sim_joinable_simp:                      0
% 3.41/0.99  sim_ac_normalised:                      0
% 3.41/0.99  sim_smt_subsumption:                    0
% 3.41/0.99  
%------------------------------------------------------------------------------
