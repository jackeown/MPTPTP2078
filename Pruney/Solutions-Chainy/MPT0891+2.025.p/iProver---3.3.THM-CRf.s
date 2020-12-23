%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:36 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  141 (3003 expanded)
%              Number of clauses        :   76 ( 984 expanded)
%              Number of leaves         :   16 ( 855 expanded)
%              Depth                    :   29
%              Number of atoms          :  420 (13327 expanded)
%              Number of equality atoms :  342 (11433 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f67,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f59])).

fof(f68,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f24])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f40,f41])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( k7_mcart_1(X0,X1,X2,sK5) = sK5
          | k6_mcart_1(X0,X1,X2,sK5) = sK5
          | k5_mcart_1(X0,X1,X2,sK5) = sK5 )
        & m1_subset_1(sK5,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
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
          ( ( k7_mcart_1(sK2,sK3,sK4,X3) = X3
            | k6_mcart_1(sK2,sK3,sK4,X3) = X3
            | k5_mcart_1(sK2,sK3,sK4,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4)) )
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
      | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
      | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 )
    & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f27,f26])).

fof(f53,plain,(
    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f53,f41])).

fof(f50,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f7,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f43])).

fof(f54,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f65,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f66,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f65])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18933,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18928,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_18932,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19531,plain,
    ( k1_enumset1(X0,X0,X1) = k1_xboole_0
    | sK1(k1_enumset1(X0,X0,X1)) = X0
    | sK1(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_18928,c_18932])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_154,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | sK5 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_155,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK5),k6_mcart_1(X0,X1,X2,sK5)),k7_mcart_1(X0,X1,X2,sK5)) = sK5
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_154])).

cnf(c_19085,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_155])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_41,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_869,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5828,plain,
    ( X0 = X1
    | X1 != k1_xboole_0
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_6298,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5828])).

cnf(c_6299,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5828])).

cnf(c_6300,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5828])).

cnf(c_19111,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19085,c_22,c_21,c_20,c_41,c_42,c_6298,c_6299,c_6300])).

cnf(c_17,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19115,plain,
    ( k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)) = k1_mcart_1(sK5) ),
    inference(superposition,[status(thm)],[c_19111,c_17])).

cnf(c_16,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19213,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(superposition,[status(thm)],[c_19115,c_16])).

cnf(c_19222,plain,
    ( k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
    inference(demodulation,[status(thm)],[c_19213,c_19115])).

cnf(c_19212,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) ),
    inference(superposition,[status(thm)],[c_19115,c_17])).

cnf(c_19444,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_19222,c_19212])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18930,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_19495,plain,
    ( k4_tarski(k1_mcart_1(sK5),X0) != sK1(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_19444,c_18930])).

cnf(c_20246,plain,
    ( k1_enumset1(X0,X0,X1) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK5),X2) != X1
    | sK1(k1_enumset1(X0,X0,X1)) = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19531,c_19495])).

cnf(c_10,negated_conjecture,
    ( k4_tarski(X0,X1) != k2_mcart_1(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_18961,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_10,c_16])).

cnf(c_19117,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) != sK5 ),
    inference(superposition,[status(thm)],[c_19111,c_18961])).

cnf(c_19116,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) ),
    inference(superposition,[status(thm)],[c_19111,c_16])).

cnf(c_19142,plain,
    ( k2_mcart_1(sK5) != sK5 ),
    inference(light_normalisation,[status(thm)],[c_19117,c_19116])).

cnf(c_18,negated_conjecture,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19132,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_18,c_19116])).

cnf(c_19145,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_19142,c_19132])).

cnf(c_19408,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_19145,c_19213])).

cnf(c_19410,plain,
    ( k1_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_19408,c_19212])).

cnf(c_19125,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_19116,c_19111])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_18929,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19255,plain,
    ( sK1(X0) != sK5
    | k1_xboole_0 = X0
    | r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19125,c_18929])).

cnf(c_19309,plain,
    ( sK1(X0) != sK5
    | k1_xboole_0 = X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19255,c_19212])).

cnf(c_20244,plain,
    ( k1_enumset1(X0,X0,X1) = k1_xboole_0
    | sK1(k1_enumset1(X0,X0,X1)) = X0
    | sK5 != X1
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19531,c_19309])).

cnf(c_20834,plain,
    ( k1_enumset1(X0,X0,sK5) = k1_xboole_0
    | sK1(k1_enumset1(X0,X0,sK5)) = X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,sK5)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_20244])).

cnf(c_21234,plain,
    ( k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_xboole_0
    | sK1(k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5)) = k1_mcart_1(k1_mcart_1(sK5)) ),
    inference(superposition,[status(thm)],[c_18933,c_20834])).

cnf(c_21476,plain,
    ( k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_xboole_0
    | k1_mcart_1(k1_mcart_1(sK5)) != sK5
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21234,c_19309])).

cnf(c_21898,plain,
    ( k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_xboole_0
    | k1_mcart_1(k1_mcart_1(sK5)) != sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21476,c_18933])).

cnf(c_21899,plain,
    ( k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_19410,c_21898])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_18934,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21923,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_21899,c_18934])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18931,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19092,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_18931])).

cnf(c_22010,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21923,c_19092])).

cnf(c_22087,plain,
    ( k1_enumset1(X0,X0,X1) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK5),X2) != X1
    | sK1(k1_enumset1(X0,X0,X1)) = X0
    | r2_hidden(sK5,k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20246,c_22010])).

cnf(c_22096,plain,
    ( k1_enumset1(X0,X0,k4_tarski(k1_mcart_1(sK5),X1)) = k1_xboole_0
    | sK1(k1_enumset1(X0,X0,k4_tarski(k1_mcart_1(sK5),X1))) = X0
    | r2_hidden(sK5,k1_enumset1(X0,X0,k4_tarski(k1_mcart_1(sK5),X1))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_22087])).

cnf(c_23343,plain,
    ( k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0)) = k1_xboole_0
    | sK1(k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0))) = sK5 ),
    inference(superposition,[status(thm)],[c_18933,c_22096])).

cnf(c_19281,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_19212,c_19125])).

cnf(c_19465,plain,
    ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_19281,c_19213,c_19444])).

cnf(c_20161,plain,
    ( sK1(X0) != sK5
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19465,c_19495])).

cnf(c_22018,plain,
    ( sK1(X0) != sK5
    | k1_xboole_0 = X0
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22010,c_20161])).

cnf(c_23412,plain,
    ( k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0)) = k1_xboole_0
    | r2_hidden(sK5,k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23343,c_22018])).

cnf(c_23536,plain,
    ( k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23412,c_18933])).

cnf(c_23544,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_23536,c_18933])).

cnf(c_23781,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23544,c_19092])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:48:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.70/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.70/1.50  
% 7.70/1.50  ------  iProver source info
% 7.70/1.50  
% 7.70/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.70/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.70/1.50  git: non_committed_changes: false
% 7.70/1.50  git: last_make_outside_of_git: false
% 7.70/1.50  
% 7.70/1.50  ------ 
% 7.70/1.50  ------ Parsing...
% 7.70/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  ------ Proving...
% 7.70/1.50  ------ Problem Properties 
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  clauses                                 22
% 7.70/1.50  conjectures                             7
% 7.70/1.50  EPR                                     3
% 7.70/1.50  Horn                                    16
% 7.70/1.50  unary                                   12
% 7.70/1.50  binary                                  1
% 7.70/1.50  lits                                    44
% 7.70/1.50  lits eq                                 34
% 7.70/1.50  fd_pure                                 0
% 7.70/1.50  fd_pseudo                               0
% 7.70/1.50  fd_cond                                 5
% 7.70/1.50  fd_pseudo_cond                          3
% 7.70/1.50  AC symbols                              0
% 7.70/1.50  
% 7.70/1.50  ------ Input Options Time Limit: Unbounded
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.70/1.50  Current options:
% 7.70/1.50  ------ 
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  % SZS status Theorem for theBenchmark.p
% 7.70/1.50  
% 7.70/1.50   Resolution empty clause
% 7.70/1.50  
% 7.70/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  fof(f1,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f17,plain,(
% 7.70/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.70/1.50    inference(nnf_transformation,[],[f1])).
% 7.70/1.50  
% 7.70/1.50  fof(f18,plain,(
% 7.70/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.70/1.50    inference(flattening,[],[f17])).
% 7.70/1.50  
% 7.70/1.50  fof(f19,plain,(
% 7.70/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.70/1.50    inference(rectify,[],[f18])).
% 7.70/1.50  
% 7.70/1.50  fof(f20,plain,(
% 7.70/1.50    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f21,plain,(
% 7.70/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.70/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 7.70/1.50  
% 7.70/1.50  fof(f30,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.70/1.50    inference(cnf_transformation,[],[f21])).
% 7.70/1.50  
% 7.70/1.50  fof(f2,axiom,(
% 7.70/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f35,plain,(
% 7.70/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f2])).
% 7.70/1.50  
% 7.70/1.50  fof(f59,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 7.70/1.50    inference(definition_unfolding,[],[f30,f35])).
% 7.70/1.50  
% 7.70/1.50  fof(f67,plain,(
% 7.70/1.50    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 7.70/1.50    inference(equality_resolution,[],[f59])).
% 7.70/1.50  
% 7.70/1.50  fof(f68,plain,(
% 7.70/1.50    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 7.70/1.50    inference(equality_resolution,[],[f67])).
% 7.70/1.50  
% 7.70/1.50  fof(f8,axiom,(
% 7.70/1.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f14,plain,(
% 7.70/1.50    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 7.70/1.50    inference(ennf_transformation,[],[f8])).
% 7.70/1.50  
% 7.70/1.50  fof(f24,plain,(
% 7.70/1.50    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f25,plain,(
% 7.70/1.50    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 7.70/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f24])).
% 7.70/1.50  
% 7.70/1.50  fof(f44,plain,(
% 7.70/1.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.70/1.50    inference(cnf_transformation,[],[f25])).
% 7.70/1.50  
% 7.70/1.50  fof(f29,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.70/1.50    inference(cnf_transformation,[],[f21])).
% 7.70/1.50  
% 7.70/1.50  fof(f60,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 7.70/1.50    inference(definition_unfolding,[],[f29,f35])).
% 7.70/1.50  
% 7.70/1.50  fof(f69,plain,(
% 7.70/1.50    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 7.70/1.50    inference(equality_resolution,[],[f60])).
% 7.70/1.50  
% 7.70/1.50  fof(f9,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f15,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.70/1.50    inference(ennf_transformation,[],[f9])).
% 7.70/1.50  
% 7.70/1.50  fof(f47,plain,(
% 7.70/1.50    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.70/1.50    inference(cnf_transformation,[],[f15])).
% 7.70/1.50  
% 7.70/1.50  fof(f5,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f40,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f5])).
% 7.70/1.50  
% 7.70/1.50  fof(f6,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f41,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f6])).
% 7.70/1.50  
% 7.70/1.50  fof(f63,plain,(
% 7.70/1.50    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.70/1.50    inference(definition_unfolding,[],[f47,f40,f41])).
% 7.70/1.50  
% 7.70/1.50  fof(f11,conjecture,(
% 7.70/1.50    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f12,negated_conjecture,(
% 7.70/1.50    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.70/1.50    inference(negated_conjecture,[],[f11])).
% 7.70/1.50  
% 7.70/1.50  fof(f16,plain,(
% 7.70/1.50    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.70/1.50    inference(ennf_transformation,[],[f12])).
% 7.70/1.50  
% 7.70/1.50  fof(f27,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK5) = sK5 | k6_mcart_1(X0,X1,X2,sK5) = sK5 | k5_mcart_1(X0,X1,X2,sK5) = sK5) & m1_subset_1(sK5,k3_zfmisc_1(X0,X1,X2)))) )),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f26,plain,(
% 7.70/1.50    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK2,sK3,sK4,X3) = X3 | k6_mcart_1(sK2,sK3,sK4,X3) = X3 | k5_mcart_1(sK2,sK3,sK4,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2)),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f28,plain,(
% 7.70/1.50    ((k7_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5) & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2),
% 7.70/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f27,f26])).
% 7.70/1.50  
% 7.70/1.50  fof(f53,plain,(
% 7.70/1.50    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))),
% 7.70/1.50    inference(cnf_transformation,[],[f28])).
% 7.70/1.50  
% 7.70/1.50  fof(f64,plain,(
% 7.70/1.50    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 7.70/1.50    inference(definition_unfolding,[],[f53,f41])).
% 7.70/1.50  
% 7.70/1.50  fof(f50,plain,(
% 7.70/1.50    k1_xboole_0 != sK2),
% 7.70/1.50    inference(cnf_transformation,[],[f28])).
% 7.70/1.50  
% 7.70/1.50  fof(f51,plain,(
% 7.70/1.50    k1_xboole_0 != sK3),
% 7.70/1.50    inference(cnf_transformation,[],[f28])).
% 7.70/1.50  
% 7.70/1.50  fof(f52,plain,(
% 7.70/1.50    k1_xboole_0 != sK4),
% 7.70/1.50    inference(cnf_transformation,[],[f28])).
% 7.70/1.50  
% 7.70/1.50  fof(f3,axiom,(
% 7.70/1.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f22,plain,(
% 7.70/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.70/1.50    inference(nnf_transformation,[],[f3])).
% 7.70/1.50  
% 7.70/1.50  fof(f23,plain,(
% 7.70/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.70/1.50    inference(flattening,[],[f22])).
% 7.70/1.50  
% 7.70/1.50  fof(f36,plain,(
% 7.70/1.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 7.70/1.50    inference(cnf_transformation,[],[f23])).
% 7.70/1.50  
% 7.70/1.50  fof(f37,plain,(
% 7.70/1.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 7.70/1.50    inference(cnf_transformation,[],[f23])).
% 7.70/1.50  
% 7.70/1.50  fof(f71,plain,(
% 7.70/1.50    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 7.70/1.50    inference(equality_resolution,[],[f37])).
% 7.70/1.50  
% 7.70/1.50  fof(f10,axiom,(
% 7.70/1.50    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f48,plain,(
% 7.70/1.50    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 7.70/1.50    inference(cnf_transformation,[],[f10])).
% 7.70/1.50  
% 7.70/1.50  fof(f49,plain,(
% 7.70/1.50    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 7.70/1.50    inference(cnf_transformation,[],[f10])).
% 7.70/1.50  
% 7.70/1.50  fof(f46,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 7.70/1.50    inference(cnf_transformation,[],[f25])).
% 7.70/1.50  
% 7.70/1.50  fof(f61,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 7.70/1.50    inference(definition_unfolding,[],[f46,f40])).
% 7.70/1.50  
% 7.70/1.50  fof(f7,axiom,(
% 7.70/1.50    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f13,plain,(
% 7.70/1.50    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 7.70/1.50    inference(ennf_transformation,[],[f7])).
% 7.70/1.50  
% 7.70/1.50  fof(f43,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 7.70/1.50    inference(cnf_transformation,[],[f13])).
% 7.70/1.50  
% 7.70/1.50  fof(f72,plain,(
% 7.70/1.50    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 7.70/1.50    inference(equality_resolution,[],[f43])).
% 7.70/1.50  
% 7.70/1.50  fof(f54,plain,(
% 7.70/1.50    k7_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5),
% 7.70/1.50    inference(cnf_transformation,[],[f28])).
% 7.70/1.50  
% 7.70/1.50  fof(f45,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 7.70/1.50    inference(cnf_transformation,[],[f25])).
% 7.70/1.50  
% 7.70/1.50  fof(f62,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 7.70/1.50    inference(definition_unfolding,[],[f45,f40])).
% 7.70/1.50  
% 7.70/1.50  fof(f31,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.70/1.50    inference(cnf_transformation,[],[f21])).
% 7.70/1.50  
% 7.70/1.50  fof(f58,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 7.70/1.50    inference(definition_unfolding,[],[f31,f35])).
% 7.70/1.50  
% 7.70/1.50  fof(f65,plain,(
% 7.70/1.50    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 7.70/1.50    inference(equality_resolution,[],[f58])).
% 7.70/1.50  
% 7.70/1.50  fof(f66,plain,(
% 7.70/1.50    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 7.70/1.50    inference(equality_resolution,[],[f65])).
% 7.70/1.50  
% 7.70/1.50  fof(f38,plain,(
% 7.70/1.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 7.70/1.50    inference(cnf_transformation,[],[f23])).
% 7.70/1.50  
% 7.70/1.50  fof(f70,plain,(
% 7.70/1.50    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.70/1.50    inference(equality_resolution,[],[f38])).
% 7.70/1.50  
% 7.70/1.50  fof(f4,axiom,(
% 7.70/1.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 7.70/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f39,plain,(
% 7.70/1.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 7.70/1.50    inference(cnf_transformation,[],[f4])).
% 7.70/1.50  
% 7.70/1.50  cnf(c_4,plain,
% 7.70/1.50      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18933,plain,
% 7.70/1.50      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_14,plain,
% 7.70/1.50      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.70/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18928,plain,
% 7.70/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.70/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18932,plain,
% 7.70/1.50      ( X0 = X1
% 7.70/1.50      | X0 = X2
% 7.70/1.50      | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19531,plain,
% 7.70/1.50      ( k1_enumset1(X0,X0,X1) = k1_xboole_0
% 7.70/1.50      | sK1(k1_enumset1(X0,X0,X1)) = X0
% 7.70/1.50      | sK1(k1_enumset1(X0,X0,X1)) = X1 ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_18928,c_18932]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_15,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.70/1.50      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 7.70/1.50      | k1_xboole_0 = X2
% 7.70/1.50      | k1_xboole_0 = X1
% 7.70/1.50      | k1_xboole_0 = X3 ),
% 7.70/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19,negated_conjecture,
% 7.70/1.50      ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_154,plain,
% 7.70/1.50      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 7.70/1.50      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 7.70/1.50      | sK5 != X3
% 7.70/1.50      | k1_xboole_0 = X0
% 7.70/1.50      | k1_xboole_0 = X1
% 7.70/1.50      | k1_xboole_0 = X2 ),
% 7.70/1.50      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_155,plain,
% 7.70/1.50      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK5),k6_mcart_1(X0,X1,X2,sK5)),k7_mcart_1(X0,X1,X2,sK5)) = sK5
% 7.70/1.50      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 7.70/1.50      | k1_xboole_0 = X1
% 7.70/1.50      | k1_xboole_0 = X0
% 7.70/1.50      | k1_xboole_0 = X2 ),
% 7.70/1.50      inference(unflattening,[status(thm)],[c_154]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19085,plain,
% 7.70/1.50      ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5
% 7.70/1.50      | sK4 = k1_xboole_0
% 7.70/1.50      | sK3 = k1_xboole_0
% 7.70/1.50      | sK2 = k1_xboole_0 ),
% 7.70/1.50      inference(equality_resolution,[status(thm)],[c_155]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_22,negated_conjecture,
% 7.70/1.50      ( k1_xboole_0 != sK2 ),
% 7.70/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_21,negated_conjecture,
% 7.70/1.50      ( k1_xboole_0 != sK3 ),
% 7.70/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_20,negated_conjecture,
% 7.70/1.50      ( k1_xboole_0 != sK4 ),
% 7.70/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_8,plain,
% 7.70/1.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.70/1.50      | k1_xboole_0 = X1
% 7.70/1.50      | k1_xboole_0 = X0 ),
% 7.70/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_41,plain,
% 7.70/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.70/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_7,plain,
% 7.70/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.70/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_42,plain,
% 7.70/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_869,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5828,plain,
% 7.70/1.50      ( X0 = X1 | X1 != k1_xboole_0 | X0 != k1_xboole_0 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_869]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6298,plain,
% 7.70/1.50      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_5828]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6299,plain,
% 7.70/1.50      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_5828]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6300,plain,
% 7.70/1.50      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_5828]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19111,plain,
% 7.70/1.50      ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_19085,c_22,c_21,c_20,c_41,c_42,c_6298,c_6299,c_6300]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_17,plain,
% 7.70/1.50      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 7.70/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19115,plain,
% 7.70/1.50      ( k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)) = k1_mcart_1(sK5) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19111,c_17]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_16,plain,
% 7.70/1.50      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 7.70/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19213,plain,
% 7.70/1.50      ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19115,c_16]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19222,plain,
% 7.70/1.50      ( k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_19213,c_19115]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19212,plain,
% 7.70/1.50      ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19115,c_17]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19444,plain,
% 7.70/1.50      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
% 7.70/1.50      inference(light_normalisation,[status(thm)],[c_19222,c_19212]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_12,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,X1)
% 7.70/1.50      | k4_tarski(k4_tarski(X2,X0),X3) != sK1(X1)
% 7.70/1.50      | k1_xboole_0 = X1 ),
% 7.70/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18930,plain,
% 7.70/1.50      ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
% 7.70/1.50      | k1_xboole_0 = X3
% 7.70/1.50      | r2_hidden(X1,X3) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19495,plain,
% 7.70/1.50      ( k4_tarski(k1_mcart_1(sK5),X0) != sK1(X1)
% 7.70/1.50      | k1_xboole_0 = X1
% 7.70/1.50      | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),X1) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19444,c_18930]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_20246,plain,
% 7.70/1.50      ( k1_enumset1(X0,X0,X1) = k1_xboole_0
% 7.70/1.50      | k4_tarski(k1_mcart_1(sK5),X2) != X1
% 7.70/1.50      | sK1(k1_enumset1(X0,X0,X1)) = X0
% 7.70/1.50      | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,X1)) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19531,c_19495]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_10,negated_conjecture,
% 7.70/1.50      ( k4_tarski(X0,X1) != k2_mcart_1(k4_tarski(X0,X1)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18961,plain,
% 7.70/1.50      ( k4_tarski(X0,X1) != X1 ),
% 7.70/1.50      inference(light_normalisation,[status(thm)],[c_10,c_16]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19117,plain,
% 7.70/1.50      ( k7_mcart_1(sK2,sK3,sK4,sK5) != sK5 ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19111,c_18961]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19116,plain,
% 7.70/1.50      ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19111,c_16]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19142,plain,
% 7.70/1.50      ( k2_mcart_1(sK5) != sK5 ),
% 7.70/1.50      inference(light_normalisation,[status(thm)],[c_19117,c_19116]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18,negated_conjecture,
% 7.70/1.50      ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 7.70/1.50      | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 7.70/1.50      | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
% 7.70/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19132,plain,
% 7.70/1.50      ( k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 7.70/1.50      | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 7.70/1.50      | k2_mcart_1(sK5) = sK5 ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_18,c_19116]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19145,plain,
% 7.70/1.50      ( k6_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
% 7.70/1.50      inference(backward_subsumption_resolution,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_19142,c_19132]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19408,plain,
% 7.70/1.50      ( k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19145,c_19213]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19410,plain,
% 7.70/1.50      ( k1_mcart_1(k1_mcart_1(sK5)) = sK5 | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_19408,c_19212]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19125,plain,
% 7.70/1.50      ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) = sK5 ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_19116,c_19111]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_13,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,X1)
% 7.70/1.50      | k4_tarski(k4_tarski(X0,X2),X3) != sK1(X1)
% 7.70/1.50      | k1_xboole_0 = X1 ),
% 7.70/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18929,plain,
% 7.70/1.50      ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
% 7.70/1.50      | k1_xboole_0 = X3
% 7.70/1.50      | r2_hidden(X0,X3) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19255,plain,
% 7.70/1.50      ( sK1(X0) != sK5
% 7.70/1.50      | k1_xboole_0 = X0
% 7.70/1.50      | r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK5),X0) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19125,c_18929]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19309,plain,
% 7.70/1.50      ( sK1(X0) != sK5
% 7.70/1.50      | k1_xboole_0 = X0
% 7.70/1.50      | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),X0) != iProver_top ),
% 7.70/1.50      inference(light_normalisation,[status(thm)],[c_19255,c_19212]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_20244,plain,
% 7.70/1.50      ( k1_enumset1(X0,X0,X1) = k1_xboole_0
% 7.70/1.50      | sK1(k1_enumset1(X0,X0,X1)) = X0
% 7.70/1.50      | sK5 != X1
% 7.70/1.50      | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,X1)) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19531,c_19309]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_20834,plain,
% 7.70/1.50      ( k1_enumset1(X0,X0,sK5) = k1_xboole_0
% 7.70/1.50      | sK1(k1_enumset1(X0,X0,sK5)) = X0
% 7.70/1.50      | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,sK5)) != iProver_top ),
% 7.70/1.50      inference(equality_resolution,[status(thm)],[c_20244]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_21234,plain,
% 7.70/1.50      ( k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_xboole_0
% 7.70/1.50      | sK1(k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5)) = k1_mcart_1(k1_mcart_1(sK5)) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_18933,c_20834]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_21476,plain,
% 7.70/1.50      ( k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_xboole_0
% 7.70/1.50      | k1_mcart_1(k1_mcart_1(sK5)) != sK5
% 7.70/1.50      | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5)) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_21234,c_19309]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_21898,plain,
% 7.70/1.50      ( k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_xboole_0
% 7.70/1.50      | k1_mcart_1(k1_mcart_1(sK5)) != sK5 ),
% 7.70/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_21476,c_18933]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_21899,plain,
% 7.70/1.50      ( k1_enumset1(k1_mcart_1(k1_mcart_1(sK5)),k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_xboole_0
% 7.70/1.50      | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19410,c_21898]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_3,plain,
% 7.70/1.50      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18934,plain,
% 7.70/1.50      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_21923,plain,
% 7.70/1.50      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 7.70/1.50      | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_21899,c_18934]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6,plain,
% 7.70/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.70/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_9,negated_conjecture,
% 7.70/1.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18931,plain,
% 7.70/1.50      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19092,plain,
% 7.70/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_6,c_18931]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_22010,plain,
% 7.70/1.50      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
% 7.70/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_21923,c_19092]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_22087,plain,
% 7.70/1.50      ( k1_enumset1(X0,X0,X1) = k1_xboole_0
% 7.70/1.50      | k4_tarski(k1_mcart_1(sK5),X2) != X1
% 7.70/1.50      | sK1(k1_enumset1(X0,X0,X1)) = X0
% 7.70/1.50      | r2_hidden(sK5,k1_enumset1(X0,X0,X1)) != iProver_top ),
% 7.70/1.50      inference(light_normalisation,[status(thm)],[c_20246,c_22010]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_22096,plain,
% 7.70/1.50      ( k1_enumset1(X0,X0,k4_tarski(k1_mcart_1(sK5),X1)) = k1_xboole_0
% 7.70/1.50      | sK1(k1_enumset1(X0,X0,k4_tarski(k1_mcart_1(sK5),X1))) = X0
% 7.70/1.50      | r2_hidden(sK5,k1_enumset1(X0,X0,k4_tarski(k1_mcart_1(sK5),X1))) != iProver_top ),
% 7.70/1.50      inference(equality_resolution,[status(thm)],[c_22087]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23343,plain,
% 7.70/1.50      ( k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0)) = k1_xboole_0
% 7.70/1.50      | sK1(k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0))) = sK5 ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_18933,c_22096]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19281,plain,
% 7.70/1.50      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) = sK5 ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_19212,c_19125]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_19465,plain,
% 7.70/1.50      ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5 ),
% 7.70/1.50      inference(light_normalisation,[status(thm)],[c_19281,c_19213,c_19444]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_20161,plain,
% 7.70/1.50      ( sK1(X0) != sK5
% 7.70/1.50      | k1_xboole_0 = X0
% 7.70/1.50      | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),X0) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_19465,c_19495]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_22018,plain,
% 7.70/1.50      ( sK1(X0) != sK5 | k1_xboole_0 = X0 | r2_hidden(sK5,X0) != iProver_top ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_22010,c_20161]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23412,plain,
% 7.70/1.50      ( k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0)) = k1_xboole_0
% 7.70/1.50      | r2_hidden(sK5,k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0))) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_23343,c_22018]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23536,plain,
% 7.70/1.50      ( k1_enumset1(sK5,sK5,k4_tarski(k1_mcart_1(sK5),X0)) = k1_xboole_0 ),
% 7.70/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_23412,c_18933]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23544,plain,
% 7.70/1.50      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_23536,c_18933]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23781,plain,
% 7.70/1.50      ( $false ),
% 7.70/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_23544,c_19092]) ).
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  ------                               Statistics
% 7.70/1.50  
% 7.70/1.50  ------ Selected
% 7.70/1.50  
% 7.70/1.50  total_time:                             0.518
% 7.70/1.50  
%------------------------------------------------------------------------------
