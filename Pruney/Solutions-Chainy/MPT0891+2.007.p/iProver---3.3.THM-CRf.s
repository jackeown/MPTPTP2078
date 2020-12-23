%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:33 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  174 (3325 expanded)
%              Number of clauses        :   85 ( 873 expanded)
%              Number of leaves         :   22 ( 982 expanded)
%              Depth                    :   21
%              Number of atoms          :  599 (14908 expanded)
%              Number of equality atoms :  463 (11631 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f37])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f82])).

fof(f109,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f61,f57])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f59,f82])).

fof(f110,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f88])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f71,f64,f65])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( k7_mcart_1(X0,X1,X2,sK6) = sK6
          | k6_mcart_1(X0,X1,X2,sK6) = sK6
          | k5_mcart_1(X0,X1,X2,sK6) = sK6 )
        & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
          ( ( k7_mcart_1(sK3,sK4,sK5,X3) = X3
            | k6_mcart_1(sK3,sK4,sK5,X3) = X3
            | k5_mcart_1(sK3,sK4,sK5,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK3,sK4,sK5)) )
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 )
    & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f40,f39])).

fof(f80,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f80,f65])).

fof(f77,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f82])).

fof(f107,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f85])).

fof(f108,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f107])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f65])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f72,f65])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f73,f65])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f70,f64])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f101,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f100])).

fof(f81,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f67])).

fof(f76,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f69,f64])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f45])).

fof(f105,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f104])).

cnf(c_24,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_876,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_885,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3302,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK2(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_876,c_885])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_879,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_xboole_0
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3529,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_879])).

cnf(c_1,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_883,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2603,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_883])).

cnf(c_3534,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3529,c_2603])).

cnf(c_3887,plain,
    ( sK2(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3302,c_3534])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_355,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_356,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK6),k6_mcart_1(X0,X1,X2,sK6)),k7_mcart_1(X0,X1,X2,sK6)) = sK6
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_1351,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_356])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_77,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_80,plain,
    ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_538,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1164,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1165,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1166,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1167,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_1168,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1169,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_1774,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_35,c_34,c_33,c_77,c_80,c_1165,c_1167,c_1169])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_337,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_338,plain,
    ( k7_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(sK6)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_1215,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_338])).

cnf(c_1586,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1215,c_35,c_34,c_33,c_77,c_80,c_1165,c_1167,c_1169])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_301,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_302,plain,
    ( k5_mcart_1(X0,X1,X2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_1221,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_302])).

cnf(c_1728,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1221,c_35,c_34,c_33,c_77,c_80,c_1165,c_1167,c_1169])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_319,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_320,plain,
    ( k6_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_1345,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_320])).

cnf(c_1768,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1345,c_35,c_34,c_33,c_77,c_80,c_1165,c_1167,c_1169])).

cnf(c_1776,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_1774,c_1586,c_1728,c_1768])).

cnf(c_30,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1778,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(superposition,[status(thm)],[c_1776,c_30])).

cnf(c_1814,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(demodulation,[status(thm)],[c_1778,c_1776])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_878,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2436,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK2(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_878])).

cnf(c_2888,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_2436])).

cnf(c_3893,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_2888])).

cnf(c_4484,plain,
    ( sK6 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3893,c_3534])).

cnf(c_4488,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4484])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_892,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_31,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1589,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_31,c_1586])).

cnf(c_1771,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_1589,c_1768])).

cnf(c_1773,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(demodulation,[status(thm)],[c_1771,c_1728])).

cnf(c_1815,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_1773,c_1778])).

cnf(c_20,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_29,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_922,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_20,c_29])).

cnf(c_1900,plain,
    ( k2_mcart_1(sK6) != sK6 ),
    inference(superposition,[status(thm)],[c_1814,c_922])).

cnf(c_2047,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1815,c_1900])).

cnf(c_2048,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(renaming,[status(thm)],[c_2047])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_877,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1846,plain,
    ( k4_tarski(sK6,X0) != sK2(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k1_mcart_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_877])).

cnf(c_3901,plain,
    ( k1_enumset1(X0,X0,X0) = k1_xboole_0
    | k4_tarski(sK6,X1) != X0
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3887,c_1846])).

cnf(c_5106,plain,
    ( k4_tarski(sK6,X0) != X1
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3901,c_3534])).

cnf(c_5110,plain,
    ( k1_mcart_1(sK6) != X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_5106])).

cnf(c_5130,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5110,c_885])).

cnf(c_5134,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_892,c_5130])).

cnf(c_5882,plain,
    ( r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4488,c_5134])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_890,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5884,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5882,c_890])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.50/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/1.00  
% 3.50/1.00  ------  iProver source info
% 3.50/1.00  
% 3.50/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.50/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/1.00  git: non_committed_changes: false
% 3.50/1.00  git: last_make_outside_of_git: false
% 3.50/1.00  
% 3.50/1.00  ------ 
% 3.50/1.00  
% 3.50/1.00  ------ Input Options
% 3.50/1.00  
% 3.50/1.00  --out_options                           all
% 3.50/1.00  --tptp_safe_out                         true
% 3.50/1.00  --problem_path                          ""
% 3.50/1.00  --include_path                          ""
% 3.50/1.00  --clausifier                            res/vclausify_rel
% 3.50/1.00  --clausifier_options                    --mode clausify
% 3.50/1.00  --stdin                                 false
% 3.50/1.00  --stats_out                             all
% 3.50/1.00  
% 3.50/1.00  ------ General Options
% 3.50/1.00  
% 3.50/1.00  --fof                                   false
% 3.50/1.00  --time_out_real                         305.
% 3.50/1.00  --time_out_virtual                      -1.
% 3.50/1.00  --symbol_type_check                     false
% 3.50/1.00  --clausify_out                          false
% 3.50/1.00  --sig_cnt_out                           false
% 3.50/1.00  --trig_cnt_out                          false
% 3.50/1.00  --trig_cnt_out_tolerance                1.
% 3.50/1.00  --trig_cnt_out_sk_spl                   false
% 3.50/1.00  --abstr_cl_out                          false
% 3.50/1.00  
% 3.50/1.00  ------ Global Options
% 3.50/1.00  
% 3.50/1.00  --schedule                              default
% 3.50/1.00  --add_important_lit                     false
% 3.50/1.00  --prop_solver_per_cl                    1000
% 3.50/1.00  --min_unsat_core                        false
% 3.50/1.00  --soft_assumptions                      false
% 3.50/1.00  --soft_lemma_size                       3
% 3.50/1.00  --prop_impl_unit_size                   0
% 3.50/1.00  --prop_impl_unit                        []
% 3.50/1.00  --share_sel_clauses                     true
% 3.50/1.00  --reset_solvers                         false
% 3.50/1.00  --bc_imp_inh                            [conj_cone]
% 3.50/1.00  --conj_cone_tolerance                   3.
% 3.50/1.00  --extra_neg_conj                        none
% 3.50/1.00  --large_theory_mode                     true
% 3.50/1.00  --prolific_symb_bound                   200
% 3.50/1.00  --lt_threshold                          2000
% 3.50/1.00  --clause_weak_htbl                      true
% 3.50/1.00  --gc_record_bc_elim                     false
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing Options
% 3.50/1.00  
% 3.50/1.00  --preprocessing_flag                    true
% 3.50/1.00  --time_out_prep_mult                    0.1
% 3.50/1.00  --splitting_mode                        input
% 3.50/1.00  --splitting_grd                         true
% 3.50/1.00  --splitting_cvd                         false
% 3.50/1.00  --splitting_cvd_svl                     false
% 3.50/1.00  --splitting_nvd                         32
% 3.50/1.00  --sub_typing                            true
% 3.50/1.00  --prep_gs_sim                           true
% 3.50/1.00  --prep_unflatten                        true
% 3.50/1.00  --prep_res_sim                          true
% 3.50/1.00  --prep_upred                            true
% 3.50/1.00  --prep_sem_filter                       exhaustive
% 3.50/1.00  --prep_sem_filter_out                   false
% 3.50/1.00  --pred_elim                             true
% 3.50/1.00  --res_sim_input                         true
% 3.50/1.00  --eq_ax_congr_red                       true
% 3.50/1.00  --pure_diseq_elim                       true
% 3.50/1.00  --brand_transform                       false
% 3.50/1.00  --non_eq_to_eq                          false
% 3.50/1.00  --prep_def_merge                        true
% 3.50/1.00  --prep_def_merge_prop_impl              false
% 3.50/1.00  --prep_def_merge_mbd                    true
% 3.50/1.00  --prep_def_merge_tr_red                 false
% 3.50/1.00  --prep_def_merge_tr_cl                  false
% 3.50/1.00  --smt_preprocessing                     true
% 3.50/1.00  --smt_ac_axioms                         fast
% 3.50/1.00  --preprocessed_out                      false
% 3.50/1.00  --preprocessed_stats                    false
% 3.50/1.00  
% 3.50/1.00  ------ Abstraction refinement Options
% 3.50/1.00  
% 3.50/1.00  --abstr_ref                             []
% 3.50/1.00  --abstr_ref_prep                        false
% 3.50/1.00  --abstr_ref_until_sat                   false
% 3.50/1.00  --abstr_ref_sig_restrict                funpre
% 3.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/1.00  --abstr_ref_under                       []
% 3.50/1.00  
% 3.50/1.00  ------ SAT Options
% 3.50/1.00  
% 3.50/1.00  --sat_mode                              false
% 3.50/1.00  --sat_fm_restart_options                ""
% 3.50/1.00  --sat_gr_def                            false
% 3.50/1.00  --sat_epr_types                         true
% 3.50/1.00  --sat_non_cyclic_types                  false
% 3.50/1.00  --sat_finite_models                     false
% 3.50/1.00  --sat_fm_lemmas                         false
% 3.50/1.00  --sat_fm_prep                           false
% 3.50/1.00  --sat_fm_uc_incr                        true
% 3.50/1.00  --sat_out_model                         small
% 3.50/1.00  --sat_out_clauses                       false
% 3.50/1.00  
% 3.50/1.00  ------ QBF Options
% 3.50/1.00  
% 3.50/1.00  --qbf_mode                              false
% 3.50/1.00  --qbf_elim_univ                         false
% 3.50/1.00  --qbf_dom_inst                          none
% 3.50/1.00  --qbf_dom_pre_inst                      false
% 3.50/1.00  --qbf_sk_in                             false
% 3.50/1.00  --qbf_pred_elim                         true
% 3.50/1.00  --qbf_split                             512
% 3.50/1.00  
% 3.50/1.00  ------ BMC1 Options
% 3.50/1.00  
% 3.50/1.00  --bmc1_incremental                      false
% 3.50/1.00  --bmc1_axioms                           reachable_all
% 3.50/1.00  --bmc1_min_bound                        0
% 3.50/1.00  --bmc1_max_bound                        -1
% 3.50/1.00  --bmc1_max_bound_default                -1
% 3.50/1.00  --bmc1_symbol_reachability              true
% 3.50/1.00  --bmc1_property_lemmas                  false
% 3.50/1.00  --bmc1_k_induction                      false
% 3.50/1.00  --bmc1_non_equiv_states                 false
% 3.50/1.00  --bmc1_deadlock                         false
% 3.50/1.00  --bmc1_ucm                              false
% 3.50/1.00  --bmc1_add_unsat_core                   none
% 3.50/1.00  --bmc1_unsat_core_children              false
% 3.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/1.00  --bmc1_out_stat                         full
% 3.50/1.00  --bmc1_ground_init                      false
% 3.50/1.00  --bmc1_pre_inst_next_state              false
% 3.50/1.00  --bmc1_pre_inst_state                   false
% 3.50/1.00  --bmc1_pre_inst_reach_state             false
% 3.50/1.00  --bmc1_out_unsat_core                   false
% 3.50/1.00  --bmc1_aig_witness_out                  false
% 3.50/1.00  --bmc1_verbose                          false
% 3.50/1.00  --bmc1_dump_clauses_tptp                false
% 3.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.50/1.00  --bmc1_dump_file                        -
% 3.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.50/1.00  --bmc1_ucm_extend_mode                  1
% 3.50/1.00  --bmc1_ucm_init_mode                    2
% 3.50/1.00  --bmc1_ucm_cone_mode                    none
% 3.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.50/1.00  --bmc1_ucm_relax_model                  4
% 3.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/1.00  --bmc1_ucm_layered_model                none
% 3.50/1.00  --bmc1_ucm_max_lemma_size               10
% 3.50/1.00  
% 3.50/1.00  ------ AIG Options
% 3.50/1.00  
% 3.50/1.00  --aig_mode                              false
% 3.50/1.00  
% 3.50/1.00  ------ Instantiation Options
% 3.50/1.00  
% 3.50/1.00  --instantiation_flag                    true
% 3.50/1.00  --inst_sos_flag                         false
% 3.50/1.00  --inst_sos_phase                        true
% 3.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/1.00  --inst_lit_sel_side                     num_symb
% 3.50/1.00  --inst_solver_per_active                1400
% 3.50/1.00  --inst_solver_calls_frac                1.
% 3.50/1.00  --inst_passive_queue_type               priority_queues
% 3.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/1.00  --inst_passive_queues_freq              [25;2]
% 3.50/1.00  --inst_dismatching                      true
% 3.50/1.00  --inst_eager_unprocessed_to_passive     true
% 3.50/1.00  --inst_prop_sim_given                   true
% 3.50/1.00  --inst_prop_sim_new                     false
% 3.50/1.00  --inst_subs_new                         false
% 3.50/1.00  --inst_eq_res_simp                      false
% 3.50/1.00  --inst_subs_given                       false
% 3.50/1.00  --inst_orphan_elimination               true
% 3.50/1.00  --inst_learning_loop_flag               true
% 3.50/1.00  --inst_learning_start                   3000
% 3.50/1.00  --inst_learning_factor                  2
% 3.50/1.00  --inst_start_prop_sim_after_learn       3
% 3.50/1.00  --inst_sel_renew                        solver
% 3.50/1.00  --inst_lit_activity_flag                true
% 3.50/1.00  --inst_restr_to_given                   false
% 3.50/1.00  --inst_activity_threshold               500
% 3.50/1.00  --inst_out_proof                        true
% 3.50/1.00  
% 3.50/1.00  ------ Resolution Options
% 3.50/1.00  
% 3.50/1.00  --resolution_flag                       true
% 3.50/1.00  --res_lit_sel                           adaptive
% 3.50/1.00  --res_lit_sel_side                      none
% 3.50/1.00  --res_ordering                          kbo
% 3.50/1.00  --res_to_prop_solver                    active
% 3.50/1.00  --res_prop_simpl_new                    false
% 3.50/1.00  --res_prop_simpl_given                  true
% 3.50/1.00  --res_passive_queue_type                priority_queues
% 3.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/1.00  --res_passive_queues_freq               [15;5]
% 3.50/1.00  --res_forward_subs                      full
% 3.50/1.00  --res_backward_subs                     full
% 3.50/1.00  --res_forward_subs_resolution           true
% 3.50/1.00  --res_backward_subs_resolution          true
% 3.50/1.00  --res_orphan_elimination                true
% 3.50/1.00  --res_time_limit                        2.
% 3.50/1.00  --res_out_proof                         true
% 3.50/1.00  
% 3.50/1.00  ------ Superposition Options
% 3.50/1.00  
% 3.50/1.00  --superposition_flag                    true
% 3.50/1.00  --sup_passive_queue_type                priority_queues
% 3.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.50/1.00  --demod_completeness_check              fast
% 3.50/1.00  --demod_use_ground                      true
% 3.50/1.00  --sup_to_prop_solver                    passive
% 3.50/1.00  --sup_prop_simpl_new                    true
% 3.50/1.00  --sup_prop_simpl_given                  true
% 3.50/1.00  --sup_fun_splitting                     false
% 3.50/1.00  --sup_smt_interval                      50000
% 3.50/1.00  
% 3.50/1.00  ------ Superposition Simplification Setup
% 3.50/1.00  
% 3.50/1.00  --sup_indices_passive                   []
% 3.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_full_bw                           [BwDemod]
% 3.50/1.00  --sup_immed_triv                        [TrivRules]
% 3.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_immed_bw_main                     []
% 3.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.00  
% 3.50/1.00  ------ Combination Options
% 3.50/1.00  
% 3.50/1.00  --comb_res_mult                         3
% 3.50/1.00  --comb_sup_mult                         2
% 3.50/1.00  --comb_inst_mult                        10
% 3.50/1.00  
% 3.50/1.00  ------ Debug Options
% 3.50/1.00  
% 3.50/1.00  --dbg_backtrace                         false
% 3.50/1.00  --dbg_dump_prop_clauses                 false
% 3.50/1.00  --dbg_dump_prop_clauses_file            -
% 3.50/1.00  --dbg_out_stat                          false
% 3.50/1.00  ------ Parsing...
% 3.50/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/1.00  ------ Proving...
% 3.50/1.00  ------ Problem Properties 
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  clauses                                 35
% 3.50/1.00  conjectures                             4
% 3.50/1.00  EPR                                     3
% 3.50/1.00  Horn                                    25
% 3.50/1.00  unary                                   14
% 3.50/1.00  binary                                  5
% 3.50/1.00  lits                                    83
% 3.50/1.00  lits eq                                 59
% 3.50/1.00  fd_pure                                 0
% 3.50/1.00  fd_pseudo                               0
% 3.50/1.00  fd_cond                                 7
% 3.50/1.00  fd_pseudo_cond                          7
% 3.50/1.00  AC symbols                              0
% 3.50/1.00  
% 3.50/1.00  ------ Schedule dynamic 5 is on 
% 3.50/1.00  
% 3.50/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ 
% 3.50/1.00  Current options:
% 3.50/1.00  ------ 
% 3.50/1.00  
% 3.50/1.00  ------ Input Options
% 3.50/1.00  
% 3.50/1.00  --out_options                           all
% 3.50/1.00  --tptp_safe_out                         true
% 3.50/1.00  --problem_path                          ""
% 3.50/1.00  --include_path                          ""
% 3.50/1.00  --clausifier                            res/vclausify_rel
% 3.50/1.00  --clausifier_options                    --mode clausify
% 3.50/1.00  --stdin                                 false
% 3.50/1.00  --stats_out                             all
% 3.50/1.00  
% 3.50/1.00  ------ General Options
% 3.50/1.00  
% 3.50/1.00  --fof                                   false
% 3.50/1.00  --time_out_real                         305.
% 3.50/1.00  --time_out_virtual                      -1.
% 3.50/1.00  --symbol_type_check                     false
% 3.50/1.00  --clausify_out                          false
% 3.50/1.00  --sig_cnt_out                           false
% 3.50/1.00  --trig_cnt_out                          false
% 3.50/1.00  --trig_cnt_out_tolerance                1.
% 3.50/1.00  --trig_cnt_out_sk_spl                   false
% 3.50/1.00  --abstr_cl_out                          false
% 3.50/1.00  
% 3.50/1.00  ------ Global Options
% 3.50/1.00  
% 3.50/1.00  --schedule                              default
% 3.50/1.00  --add_important_lit                     false
% 3.50/1.00  --prop_solver_per_cl                    1000
% 3.50/1.00  --min_unsat_core                        false
% 3.50/1.00  --soft_assumptions                      false
% 3.50/1.00  --soft_lemma_size                       3
% 3.50/1.00  --prop_impl_unit_size                   0
% 3.50/1.00  --prop_impl_unit                        []
% 3.50/1.00  --share_sel_clauses                     true
% 3.50/1.00  --reset_solvers                         false
% 3.50/1.00  --bc_imp_inh                            [conj_cone]
% 3.50/1.00  --conj_cone_tolerance                   3.
% 3.50/1.00  --extra_neg_conj                        none
% 3.50/1.00  --large_theory_mode                     true
% 3.50/1.00  --prolific_symb_bound                   200
% 3.50/1.00  --lt_threshold                          2000
% 3.50/1.00  --clause_weak_htbl                      true
% 3.50/1.00  --gc_record_bc_elim                     false
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing Options
% 3.50/1.00  
% 3.50/1.00  --preprocessing_flag                    true
% 3.50/1.00  --time_out_prep_mult                    0.1
% 3.50/1.00  --splitting_mode                        input
% 3.50/1.00  --splitting_grd                         true
% 3.50/1.00  --splitting_cvd                         false
% 3.50/1.00  --splitting_cvd_svl                     false
% 3.50/1.00  --splitting_nvd                         32
% 3.50/1.00  --sub_typing                            true
% 3.50/1.00  --prep_gs_sim                           true
% 3.50/1.00  --prep_unflatten                        true
% 3.50/1.00  --prep_res_sim                          true
% 3.50/1.00  --prep_upred                            true
% 3.50/1.00  --prep_sem_filter                       exhaustive
% 3.50/1.00  --prep_sem_filter_out                   false
% 3.50/1.00  --pred_elim                             true
% 3.50/1.00  --res_sim_input                         true
% 3.50/1.00  --eq_ax_congr_red                       true
% 3.50/1.00  --pure_diseq_elim                       true
% 3.50/1.00  --brand_transform                       false
% 3.50/1.00  --non_eq_to_eq                          false
% 3.50/1.00  --prep_def_merge                        true
% 3.50/1.00  --prep_def_merge_prop_impl              false
% 3.50/1.00  --prep_def_merge_mbd                    true
% 3.50/1.00  --prep_def_merge_tr_red                 false
% 3.50/1.00  --prep_def_merge_tr_cl                  false
% 3.50/1.00  --smt_preprocessing                     true
% 3.50/1.00  --smt_ac_axioms                         fast
% 3.50/1.00  --preprocessed_out                      false
% 3.50/1.00  --preprocessed_stats                    false
% 3.50/1.00  
% 3.50/1.00  ------ Abstraction refinement Options
% 3.50/1.00  
% 3.50/1.00  --abstr_ref                             []
% 3.50/1.00  --abstr_ref_prep                        false
% 3.50/1.00  --abstr_ref_until_sat                   false
% 3.50/1.00  --abstr_ref_sig_restrict                funpre
% 3.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/1.00  --abstr_ref_under                       []
% 3.50/1.00  
% 3.50/1.00  ------ SAT Options
% 3.50/1.00  
% 3.50/1.00  --sat_mode                              false
% 3.50/1.00  --sat_fm_restart_options                ""
% 3.50/1.00  --sat_gr_def                            false
% 3.50/1.00  --sat_epr_types                         true
% 3.50/1.00  --sat_non_cyclic_types                  false
% 3.50/1.00  --sat_finite_models                     false
% 3.50/1.00  --sat_fm_lemmas                         false
% 3.50/1.00  --sat_fm_prep                           false
% 3.50/1.00  --sat_fm_uc_incr                        true
% 3.50/1.00  --sat_out_model                         small
% 3.50/1.00  --sat_out_clauses                       false
% 3.50/1.00  
% 3.50/1.00  ------ QBF Options
% 3.50/1.00  
% 3.50/1.00  --qbf_mode                              false
% 3.50/1.00  --qbf_elim_univ                         false
% 3.50/1.00  --qbf_dom_inst                          none
% 3.50/1.00  --qbf_dom_pre_inst                      false
% 3.50/1.00  --qbf_sk_in                             false
% 3.50/1.00  --qbf_pred_elim                         true
% 3.50/1.00  --qbf_split                             512
% 3.50/1.00  
% 3.50/1.00  ------ BMC1 Options
% 3.50/1.00  
% 3.50/1.00  --bmc1_incremental                      false
% 3.50/1.00  --bmc1_axioms                           reachable_all
% 3.50/1.00  --bmc1_min_bound                        0
% 3.50/1.00  --bmc1_max_bound                        -1
% 3.50/1.00  --bmc1_max_bound_default                -1
% 3.50/1.00  --bmc1_symbol_reachability              true
% 3.50/1.00  --bmc1_property_lemmas                  false
% 3.50/1.00  --bmc1_k_induction                      false
% 3.50/1.00  --bmc1_non_equiv_states                 false
% 3.50/1.00  --bmc1_deadlock                         false
% 3.50/1.00  --bmc1_ucm                              false
% 3.50/1.00  --bmc1_add_unsat_core                   none
% 3.50/1.00  --bmc1_unsat_core_children              false
% 3.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/1.00  --bmc1_out_stat                         full
% 3.50/1.00  --bmc1_ground_init                      false
% 3.50/1.00  --bmc1_pre_inst_next_state              false
% 3.50/1.00  --bmc1_pre_inst_state                   false
% 3.50/1.00  --bmc1_pre_inst_reach_state             false
% 3.50/1.00  --bmc1_out_unsat_core                   false
% 3.50/1.00  --bmc1_aig_witness_out                  false
% 3.50/1.00  --bmc1_verbose                          false
% 3.50/1.00  --bmc1_dump_clauses_tptp                false
% 3.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.50/1.00  --bmc1_dump_file                        -
% 3.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.50/1.00  --bmc1_ucm_extend_mode                  1
% 3.50/1.00  --bmc1_ucm_init_mode                    2
% 3.50/1.00  --bmc1_ucm_cone_mode                    none
% 3.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.50/1.00  --bmc1_ucm_relax_model                  4
% 3.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/1.00  --bmc1_ucm_layered_model                none
% 3.50/1.00  --bmc1_ucm_max_lemma_size               10
% 3.50/1.00  
% 3.50/1.00  ------ AIG Options
% 3.50/1.00  
% 3.50/1.00  --aig_mode                              false
% 3.50/1.00  
% 3.50/1.00  ------ Instantiation Options
% 3.50/1.00  
% 3.50/1.00  --instantiation_flag                    true
% 3.50/1.00  --inst_sos_flag                         false
% 3.50/1.00  --inst_sos_phase                        true
% 3.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/1.00  --inst_lit_sel_side                     none
% 3.50/1.00  --inst_solver_per_active                1400
% 3.50/1.00  --inst_solver_calls_frac                1.
% 3.50/1.00  --inst_passive_queue_type               priority_queues
% 3.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/1.00  --inst_passive_queues_freq              [25;2]
% 3.50/1.00  --inst_dismatching                      true
% 3.50/1.00  --inst_eager_unprocessed_to_passive     true
% 3.50/1.00  --inst_prop_sim_given                   true
% 3.50/1.00  --inst_prop_sim_new                     false
% 3.50/1.00  --inst_subs_new                         false
% 3.50/1.00  --inst_eq_res_simp                      false
% 3.50/1.00  --inst_subs_given                       false
% 3.50/1.00  --inst_orphan_elimination               true
% 3.50/1.00  --inst_learning_loop_flag               true
% 3.50/1.00  --inst_learning_start                   3000
% 3.50/1.00  --inst_learning_factor                  2
% 3.50/1.00  --inst_start_prop_sim_after_learn       3
% 3.50/1.00  --inst_sel_renew                        solver
% 3.50/1.00  --inst_lit_activity_flag                true
% 3.50/1.00  --inst_restr_to_given                   false
% 3.50/1.00  --inst_activity_threshold               500
% 3.50/1.00  --inst_out_proof                        true
% 3.50/1.00  
% 3.50/1.00  ------ Resolution Options
% 3.50/1.00  
% 3.50/1.00  --resolution_flag                       false
% 3.50/1.00  --res_lit_sel                           adaptive
% 3.50/1.00  --res_lit_sel_side                      none
% 3.50/1.00  --res_ordering                          kbo
% 3.50/1.00  --res_to_prop_solver                    active
% 3.50/1.00  --res_prop_simpl_new                    false
% 3.50/1.00  --res_prop_simpl_given                  true
% 3.50/1.00  --res_passive_queue_type                priority_queues
% 3.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/1.00  --res_passive_queues_freq               [15;5]
% 3.50/1.00  --res_forward_subs                      full
% 3.50/1.00  --res_backward_subs                     full
% 3.50/1.00  --res_forward_subs_resolution           true
% 3.50/1.00  --res_backward_subs_resolution          true
% 3.50/1.00  --res_orphan_elimination                true
% 3.50/1.00  --res_time_limit                        2.
% 3.50/1.00  --res_out_proof                         true
% 3.50/1.00  
% 3.50/1.00  ------ Superposition Options
% 3.50/1.00  
% 3.50/1.00  --superposition_flag                    true
% 3.50/1.00  --sup_passive_queue_type                priority_queues
% 3.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.50/1.00  --demod_completeness_check              fast
% 3.50/1.00  --demod_use_ground                      true
% 3.50/1.00  --sup_to_prop_solver                    passive
% 3.50/1.00  --sup_prop_simpl_new                    true
% 3.50/1.00  --sup_prop_simpl_given                  true
% 3.50/1.00  --sup_fun_splitting                     false
% 3.50/1.00  --sup_smt_interval                      50000
% 3.50/1.00  
% 3.50/1.00  ------ Superposition Simplification Setup
% 3.50/1.00  
% 3.50/1.00  --sup_indices_passive                   []
% 3.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_full_bw                           [BwDemod]
% 3.50/1.00  --sup_immed_triv                        [TrivRules]
% 3.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_immed_bw_main                     []
% 3.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.00  
% 3.50/1.00  ------ Combination Options
% 3.50/1.00  
% 3.50/1.00  --comb_res_mult                         3
% 3.50/1.00  --comb_sup_mult                         2
% 3.50/1.00  --comb_inst_mult                        10
% 3.50/1.00  
% 3.50/1.00  ------ Debug Options
% 3.50/1.00  
% 3.50/1.00  --dbg_backtrace                         false
% 3.50/1.00  --dbg_dump_prop_clauses                 false
% 3.50/1.00  --dbg_dump_prop_clauses_file            -
% 3.50/1.00  --dbg_out_stat                          false
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ Proving...
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  % SZS status Theorem for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00   Resolution empty clause
% 3.50/1.00  
% 3.50/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  fof(f12,axiom,(
% 3.50/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f20,plain,(
% 3.50/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.50/1.00    inference(ennf_transformation,[],[f12])).
% 3.50/1.00  
% 3.50/1.00  fof(f37,plain,(
% 3.50/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 3.50/1.00    introduced(choice_axiom,[])).
% 3.50/1.00  
% 3.50/1.00  fof(f38,plain,(
% 3.50/1.00    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 3.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f37])).
% 3.50/1.00  
% 3.50/1.00  fof(f68,plain,(
% 3.50/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f38])).
% 3.50/1.00  
% 3.50/1.00  fof(f4,axiom,(
% 3.50/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f29,plain,(
% 3.50/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.50/1.00    inference(nnf_transformation,[],[f4])).
% 3.50/1.00  
% 3.50/1.00  fof(f30,plain,(
% 3.50/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.50/1.00    inference(rectify,[],[f29])).
% 3.50/1.00  
% 3.50/1.00  fof(f31,plain,(
% 3.50/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.50/1.00    introduced(choice_axiom,[])).
% 3.50/1.00  
% 3.50/1.00  fof(f32,plain,(
% 3.50/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.50/1.00  
% 3.50/1.00  fof(f52,plain,(
% 3.50/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.50/1.00    inference(cnf_transformation,[],[f32])).
% 3.50/1.00  
% 3.50/1.00  fof(f5,axiom,(
% 3.50/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f56,plain,(
% 3.50/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f5])).
% 3.50/1.00  
% 3.50/1.00  fof(f6,axiom,(
% 3.50/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f57,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f6])).
% 3.50/1.00  
% 3.50/1.00  fof(f82,plain,(
% 3.50/1.00    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f56,f57])).
% 3.50/1.00  
% 3.50/1.00  fof(f86,plain,(
% 3.50/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.50/1.00    inference(definition_unfolding,[],[f52,f82])).
% 3.50/1.00  
% 3.50/1.00  fof(f109,plain,(
% 3.50/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.50/1.00    inference(equality_resolution,[],[f86])).
% 3.50/1.00  
% 3.50/1.00  fof(f1,axiom,(
% 3.50/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f42,plain,(
% 3.50/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f1])).
% 3.50/1.00  
% 3.50/1.00  fof(f8,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f35,plain,(
% 3.50/1.00    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.50/1.00    inference(nnf_transformation,[],[f8])).
% 3.50/1.00  
% 3.50/1.00  fof(f36,plain,(
% 3.50/1.00    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.50/1.00    inference(flattening,[],[f35])).
% 3.50/1.00  
% 3.50/1.00  fof(f61,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f36])).
% 3.50/1.00  
% 3.50/1.00  fof(f92,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)) )),
% 3.50/1.00    inference(definition_unfolding,[],[f61,f57])).
% 3.50/1.00  
% 3.50/1.00  fof(f2,axiom,(
% 3.50/1.00    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f43,plain,(
% 3.50/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f2])).
% 3.50/1.00  
% 3.50/1.00  fof(f7,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f33,plain,(
% 3.50/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.50/1.00    inference(nnf_transformation,[],[f7])).
% 3.50/1.00  
% 3.50/1.00  fof(f34,plain,(
% 3.50/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.50/1.00    inference(flattening,[],[f33])).
% 3.50/1.00  
% 3.50/1.00  fof(f59,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f34])).
% 3.50/1.00  
% 3.50/1.00  fof(f88,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 3.50/1.00    inference(definition_unfolding,[],[f59,f82])).
% 3.50/1.00  
% 3.50/1.00  fof(f110,plain,(
% 3.50/1.00    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 3.50/1.00    inference(equality_resolution,[],[f88])).
% 3.50/1.00  
% 3.50/1.00  fof(f13,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f21,plain,(
% 3.50/1.00    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.50/1.00    inference(ennf_transformation,[],[f13])).
% 3.50/1.00  
% 3.50/1.00  fof(f71,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f21])).
% 3.50/1.00  
% 3.50/1.00  fof(f9,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f64,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f9])).
% 3.50/1.00  
% 3.50/1.00  fof(f10,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f65,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f10])).
% 3.50/1.00  
% 3.50/1.00  fof(f95,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(definition_unfolding,[],[f71,f64,f65])).
% 3.50/1.00  
% 3.50/1.00  fof(f16,conjecture,(
% 3.50/1.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f17,negated_conjecture,(
% 3.50/1.00    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.50/1.00    inference(negated_conjecture,[],[f16])).
% 3.50/1.00  
% 3.50/1.00  fof(f23,plain,(
% 3.50/1.00    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.50/1.00    inference(ennf_transformation,[],[f17])).
% 3.50/1.00  
% 3.50/1.00  fof(f40,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK6) = sK6 | k6_mcart_1(X0,X1,X2,sK6) = sK6 | k5_mcart_1(X0,X1,X2,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)))) )),
% 3.50/1.00    introduced(choice_axiom,[])).
% 3.50/1.00  
% 3.50/1.00  fof(f39,plain,(
% 3.50/1.00    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK3,sK4,sK5,X3) = X3 | k6_mcart_1(sK3,sK4,sK5,X3) = X3 | k5_mcart_1(sK3,sK4,sK5,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3)),
% 3.50/1.00    introduced(choice_axiom,[])).
% 3.50/1.00  
% 3.50/1.00  fof(f41,plain,(
% 3.50/1.00    ((k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3),
% 3.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f40,f39])).
% 3.50/1.00  
% 3.50/1.00  fof(f80,plain,(
% 3.50/1.00    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 3.50/1.00    inference(cnf_transformation,[],[f41])).
% 3.50/1.00  
% 3.50/1.00  fof(f99,plain,(
% 3.50/1.00    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 3.50/1.00    inference(definition_unfolding,[],[f80,f65])).
% 3.50/1.00  
% 3.50/1.00  fof(f77,plain,(
% 3.50/1.00    k1_xboole_0 != sK3),
% 3.50/1.00    inference(cnf_transformation,[],[f41])).
% 3.50/1.00  
% 3.50/1.00  fof(f78,plain,(
% 3.50/1.00    k1_xboole_0 != sK4),
% 3.50/1.00    inference(cnf_transformation,[],[f41])).
% 3.50/1.00  
% 3.50/1.00  fof(f79,plain,(
% 3.50/1.00    k1_xboole_0 != sK5),
% 3.50/1.00    inference(cnf_transformation,[],[f41])).
% 3.50/1.00  
% 3.50/1.00  fof(f53,plain,(
% 3.50/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.50/1.00    inference(cnf_transformation,[],[f32])).
% 3.50/1.00  
% 3.50/1.00  fof(f85,plain,(
% 3.50/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 3.50/1.00    inference(definition_unfolding,[],[f53,f82])).
% 3.50/1.00  
% 3.50/1.00  fof(f107,plain,(
% 3.50/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 3.50/1.00    inference(equality_resolution,[],[f85])).
% 3.50/1.00  
% 3.50/1.00  fof(f108,plain,(
% 3.50/1.00    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 3.50/1.00    inference(equality_resolution,[],[f107])).
% 3.50/1.00  
% 3.50/1.00  fof(f14,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f22,plain,(
% 3.50/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.50/1.00    inference(ennf_transformation,[],[f14])).
% 3.50/1.00  
% 3.50/1.00  fof(f74,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f22])).
% 3.50/1.00  
% 3.50/1.00  fof(f96,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(definition_unfolding,[],[f74,f65])).
% 3.50/1.00  
% 3.50/1.00  fof(f72,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f22])).
% 3.50/1.00  
% 3.50/1.00  fof(f98,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(definition_unfolding,[],[f72,f65])).
% 3.50/1.00  
% 3.50/1.00  fof(f73,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f22])).
% 3.50/1.00  
% 3.50/1.00  fof(f97,plain,(
% 3.50/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(definition_unfolding,[],[f73,f65])).
% 3.50/1.00  
% 3.50/1.00  fof(f15,axiom,(
% 3.50/1.00    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f75,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f15])).
% 3.50/1.00  
% 3.50/1.00  fof(f70,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f38])).
% 3.50/1.00  
% 3.50/1.00  fof(f93,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(definition_unfolding,[],[f70,f64])).
% 3.50/1.00  
% 3.50/1.00  fof(f3,axiom,(
% 3.50/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f18,plain,(
% 3.50/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.50/1.00    inference(ennf_transformation,[],[f3])).
% 3.50/1.00  
% 3.50/1.00  fof(f24,plain,(
% 3.50/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.50/1.00    inference(nnf_transformation,[],[f18])).
% 3.50/1.00  
% 3.50/1.00  fof(f25,plain,(
% 3.50/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.50/1.00    inference(flattening,[],[f24])).
% 3.50/1.00  
% 3.50/1.00  fof(f26,plain,(
% 3.50/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.50/1.00    inference(rectify,[],[f25])).
% 3.50/1.00  
% 3.50/1.00  fof(f27,plain,(
% 3.50/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.50/1.00    introduced(choice_axiom,[])).
% 3.50/1.00  
% 3.50/1.00  fof(f28,plain,(
% 3.50/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.50/1.00  
% 3.50/1.00  fof(f47,plain,(
% 3.50/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.50/1.00    inference(cnf_transformation,[],[f28])).
% 3.50/1.00  
% 3.50/1.00  fof(f100,plain,(
% 3.50/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 3.50/1.00    inference(equality_resolution,[],[f47])).
% 3.50/1.00  
% 3.50/1.00  fof(f101,plain,(
% 3.50/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 3.50/1.00    inference(equality_resolution,[],[f100])).
% 3.50/1.00  
% 3.50/1.00  fof(f81,plain,(
% 3.50/1.00    k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6),
% 3.50/1.00    inference(cnf_transformation,[],[f41])).
% 3.50/1.00  
% 3.50/1.00  fof(f11,axiom,(
% 3.50/1.00    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.50/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f19,plain,(
% 3.50/1.00    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 3.50/1.00    inference(ennf_transformation,[],[f11])).
% 3.50/1.00  
% 3.50/1.00  fof(f67,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f19])).
% 3.50/1.00  
% 3.50/1.00  fof(f111,plain,(
% 3.50/1.00    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 3.50/1.00    inference(equality_resolution,[],[f67])).
% 3.50/1.00  
% 3.50/1.00  fof(f76,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.50/1.00    inference(cnf_transformation,[],[f15])).
% 3.50/1.00  
% 3.50/1.00  fof(f69,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f38])).
% 3.50/1.00  
% 3.50/1.00  fof(f94,plain,(
% 3.50/1.00    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.50/1.00    inference(definition_unfolding,[],[f69,f64])).
% 3.50/1.00  
% 3.50/1.00  fof(f45,plain,(
% 3.50/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.50/1.00    inference(cnf_transformation,[],[f28])).
% 3.50/1.00  
% 3.50/1.00  fof(f104,plain,(
% 3.50/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 3.50/1.00    inference(equality_resolution,[],[f45])).
% 3.50/1.00  
% 3.50/1.00  fof(f105,plain,(
% 3.50/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 3.50/1.00    inference(equality_resolution,[],[f104])).
% 3.50/1.00  
% 3.50/1.00  cnf(c_24,plain,
% 3.50/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.50/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_876,plain,
% 3.50/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_13,plain,
% 3.50/1.00      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.50/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_885,plain,
% 3.50/1.00      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3302,plain,
% 3.50/1.00      ( k1_enumset1(X0,X0,X0) = k1_xboole_0 | sK2(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_876,c_885]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_0,plain,
% 3.50/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.50/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_19,plain,
% 3.50/1.00      ( r2_hidden(X0,X1)
% 3.50/1.00      | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_xboole_0 ),
% 3.50/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_879,plain,
% 3.50/1.00      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_xboole_0
% 3.50/1.00      | r2_hidden(X0,X2) = iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3529,plain,
% 3.50/1.00      ( k1_enumset1(X0,X0,X1) != k1_xboole_0
% 3.50/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_0,c_879]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1,plain,
% 3.50/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.50/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_15,plain,
% 3.50/1.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) ),
% 3.50/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_883,plain,
% 3.50/1.00      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2603,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1,c_883]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3534,plain,
% 3.50/1.00      ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
% 3.50/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3529,c_2603]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3887,plain,
% 3.50/1.00      ( sK2(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.50/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3302,c_3534]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_25,plain,
% 3.50/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.50/1.00      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2
% 3.50/1.00      | k1_xboole_0 = X3 ),
% 3.50/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_32,negated_conjecture,
% 3.50/1.00      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 3.50/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_355,plain,
% 3.50/1.00      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.50/1.00      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 3.50/1.00      | sK6 != X3
% 3.50/1.00      | k1_xboole_0 = X0
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2 ),
% 3.50/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_356,plain,
% 3.50/1.00      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.50/1.00      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK6),k6_mcart_1(X0,X1,X2,sK6)),k7_mcart_1(X0,X1,X2,sK6)) = sK6
% 3.50/1.00      | k1_xboole_0 = X0
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2 ),
% 3.50/1.00      inference(unflattening,[status(thm)],[c_355]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1351,plain,
% 3.50/1.00      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
% 3.50/1.00      | sK5 = k1_xboole_0
% 3.50/1.00      | sK4 = k1_xboole_0
% 3.50/1.00      | sK3 = k1_xboole_0 ),
% 3.50/1.00      inference(equality_resolution,[status(thm)],[c_356]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_35,negated_conjecture,
% 3.50/1.00      ( k1_xboole_0 != sK3 ),
% 3.50/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_34,negated_conjecture,
% 3.50/1.00      ( k1_xboole_0 != sK4 ),
% 3.50/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_33,negated_conjecture,
% 3.50/1.00      ( k1_xboole_0 != sK5 ),
% 3.50/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_77,plain,
% 3.50/1.00      ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.50/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_12,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 3.50/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_80,plain,
% 3.50/1.00      ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_538,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1164,plain,
% 3.50/1.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_538]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1165,plain,
% 3.50/1.00      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_1164]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1166,plain,
% 3.50/1.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_538]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1167,plain,
% 3.50/1.00      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_1166]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1168,plain,
% 3.50/1.00      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_538]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1169,plain,
% 3.50/1.00      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 3.50/1.00      inference(instantiation,[status(thm)],[c_1168]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1774,plain,
% 3.50/1.00      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6 ),
% 3.50/1.00      inference(global_propositional_subsumption,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_1351,c_35,c_34,c_33,c_77,c_80,c_1165,c_1167,c_1169]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_26,plain,
% 3.50/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.50/1.00      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2
% 3.50/1.00      | k1_xboole_0 = X3 ),
% 3.50/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_337,plain,
% 3.50/1.00      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.50/1.00      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.50/1.00      | sK6 != X3
% 3.50/1.00      | k1_xboole_0 = X0
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2 ),
% 3.50/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_32]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_338,plain,
% 3.50/1.00      ( k7_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(sK6)
% 3.50/1.00      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.50/1.00      | k1_xboole_0 = X0
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2 ),
% 3.50/1.00      inference(unflattening,[status(thm)],[c_337]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1215,plain,
% 3.50/1.00      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
% 3.50/1.00      | sK5 = k1_xboole_0
% 3.50/1.00      | sK4 = k1_xboole_0
% 3.50/1.00      | sK3 = k1_xboole_0 ),
% 3.50/1.00      inference(equality_resolution,[status(thm)],[c_338]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1586,plain,
% 3.50/1.00      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
% 3.50/1.00      inference(global_propositional_subsumption,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_1215,c_35,c_34,c_33,c_77,c_80,c_1165,c_1167,c_1169]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_28,plain,
% 3.50/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.50/1.00      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2
% 3.50/1.00      | k1_xboole_0 = X3 ),
% 3.50/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_301,plain,
% 3.50/1.00      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.50/1.00      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.50/1.00      | sK6 != X3
% 3.50/1.00      | k1_xboole_0 = X0
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2 ),
% 3.50/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_302,plain,
% 3.50/1.00      ( k5_mcart_1(X0,X1,X2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 3.50/1.00      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.50/1.00      | k1_xboole_0 = X0
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2 ),
% 3.50/1.00      inference(unflattening,[status(thm)],[c_301]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1221,plain,
% 3.50/1.00      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 3.50/1.00      | sK5 = k1_xboole_0
% 3.50/1.00      | sK4 = k1_xboole_0
% 3.50/1.00      | sK3 = k1_xboole_0 ),
% 3.50/1.00      inference(equality_resolution,[status(thm)],[c_302]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1728,plain,
% 3.50/1.00      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
% 3.50/1.00      inference(global_propositional_subsumption,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_1221,c_35,c_34,c_33,c_77,c_80,c_1165,c_1167,c_1169]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_27,plain,
% 3.50/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.50/1.00      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2
% 3.50/1.00      | k1_xboole_0 = X3 ),
% 3.50/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_319,plain,
% 3.50/1.00      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.50/1.00      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.50/1.00      | sK6 != X3
% 3.50/1.00      | k1_xboole_0 = X0
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2 ),
% 3.50/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_320,plain,
% 3.50/1.00      ( k6_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 3.50/1.00      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 3.50/1.00      | k1_xboole_0 = X0
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | k1_xboole_0 = X2 ),
% 3.50/1.00      inference(unflattening,[status(thm)],[c_319]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1345,plain,
% 3.50/1.00      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 3.50/1.00      | sK5 = k1_xboole_0
% 3.50/1.00      | sK4 = k1_xboole_0
% 3.50/1.00      | sK3 = k1_xboole_0 ),
% 3.50/1.00      inference(equality_resolution,[status(thm)],[c_320]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1768,plain,
% 3.50/1.00      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
% 3.50/1.00      inference(global_propositional_subsumption,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_1345,c_35,c_34,c_33,c_77,c_80,c_1165,c_1167,c_1169]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1776,plain,
% 3.50/1.00      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
% 3.50/1.00      inference(light_normalisation,
% 3.50/1.00                [status(thm)],
% 3.50/1.00                [c_1774,c_1586,c_1728,c_1768]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_30,plain,
% 3.50/1.00      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.50/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1778,plain,
% 3.50/1.00      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1776,c_30]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1814,plain,
% 3.50/1.00      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 3.50/1.00      inference(demodulation,[status(thm)],[c_1778,c_1776]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_22,plain,
% 3.50/1.00      ( ~ r2_hidden(X0,X1)
% 3.50/1.00      | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
% 3.50/1.00      | k1_xboole_0 = X1 ),
% 3.50/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_878,plain,
% 3.50/1.00      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 3.50/1.00      | k1_xboole_0 = X3
% 3.50/1.00      | r2_hidden(X1,X3) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2436,plain,
% 3.50/1.00      ( k4_tarski(k1_mcart_1(sK6),X0) != sK2(X1)
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X1) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1778,c_878]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2888,plain,
% 3.50/1.00      ( sK2(X0) != sK6
% 3.50/1.00      | k1_xboole_0 = X0
% 3.50/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1814,c_2436]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3893,plain,
% 3.50/1.00      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.50/1.00      | sK6 != X0
% 3.50/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_3887,c_2888]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_4484,plain,
% 3.50/1.00      ( sK6 != X0
% 3.50/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.50/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3893,c_3534]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_4488,plain,
% 3.50/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
% 3.50/1.00      inference(equality_resolution,[status(thm)],[c_4484]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_6,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 3.50/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_892,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) = iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_31,negated_conjecture,
% 3.50/1.00      ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.50/1.00      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.50/1.00      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
% 3.50/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1589,plain,
% 3.50/1.00      ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.50/1.00      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.50/1.00      | k2_mcart_1(sK6) = sK6 ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_31,c_1586]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1771,plain,
% 3.50/1.00      ( k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 3.50/1.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.50/1.00      | k2_mcart_1(sK6) = sK6 ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1589,c_1768]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1773,plain,
% 3.50/1.00      ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.50/1.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.50/1.00      | k2_mcart_1(sK6) = sK6 ),
% 3.50/1.00      inference(demodulation,[status(thm)],[c_1771,c_1728]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1815,plain,
% 3.50/1.00      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 3.50/1.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.50/1.00      | k2_mcart_1(sK6) = sK6 ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1773,c_1778]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_20,plain,
% 3.50/1.00      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 3.50/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_29,plain,
% 3.50/1.00      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.50/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_922,plain,
% 3.50/1.00      ( k4_tarski(X0,X1) != X1 ),
% 3.50/1.00      inference(light_normalisation,[status(thm)],[c_20,c_29]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1900,plain,
% 3.50/1.00      ( k2_mcart_1(sK6) != sK6 ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1814,c_922]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2047,plain,
% 3.50/1.00      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.50/1.00      | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 3.50/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1815,c_1900]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_2048,plain,
% 3.50/1.00      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 3.50/1.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 3.50/1.00      inference(renaming,[status(thm)],[c_2047]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_23,plain,
% 3.50/1.00      ( ~ r2_hidden(X0,X1)
% 3.50/1.00      | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
% 3.50/1.00      | k1_xboole_0 = X1 ),
% 3.50/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_877,plain,
% 3.50/1.00      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 3.50/1.00      | k1_xboole_0 = X3
% 3.50/1.00      | r2_hidden(X0,X3) != iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_1846,plain,
% 3.50/1.00      ( k4_tarski(sK6,X0) != sK2(X1)
% 3.50/1.00      | k1_xboole_0 = X1
% 3.50/1.00      | r2_hidden(k1_mcart_1(sK6),X1) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_1814,c_877]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_3901,plain,
% 3.50/1.00      ( k1_enumset1(X0,X0,X0) = k1_xboole_0
% 3.50/1.00      | k4_tarski(sK6,X1) != X0
% 3.50/1.00      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_3887,c_1846]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_5106,plain,
% 3.50/1.00      ( k4_tarski(sK6,X0) != X1
% 3.50/1.00      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.50/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3901,c_3534]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_5110,plain,
% 3.50/1.00      ( k1_mcart_1(sK6) != X0
% 3.50/1.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.50/1.00      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_2048,c_5106]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_5130,plain,
% 3.50/1.00      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 3.50/1.00      | r2_hidden(k1_mcart_1(sK6),k1_enumset1(X0,X0,X0)) != iProver_top ),
% 3.50/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5110,c_885]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_5134,plain,
% 3.50/1.00      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 3.50/1.00      inference(superposition,[status(thm)],[c_892,c_5130]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_5882,plain,
% 3.50/1.00      ( r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) != iProver_top ),
% 3.50/1.00      inference(light_normalisation,[status(thm)],[c_4488,c_5134]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_8,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 3.50/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_890,plain,
% 3.50/1.00      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
% 3.50/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.50/1.00  
% 3.50/1.00  cnf(c_5884,plain,
% 3.50/1.00      ( $false ),
% 3.50/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5882,c_890]) ).
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  ------                               Statistics
% 3.50/1.00  
% 3.50/1.00  ------ General
% 3.50/1.00  
% 3.50/1.00  abstr_ref_over_cycles:                  0
% 3.50/1.00  abstr_ref_under_cycles:                 0
% 3.50/1.00  gc_basic_clause_elim:                   0
% 3.50/1.00  forced_gc_time:                         0
% 3.50/1.00  parsing_time:                           0.009
% 3.50/1.00  unif_index_cands_time:                  0.
% 3.50/1.00  unif_index_add_time:                    0.
% 3.50/1.00  orderings_time:                         0.
% 3.50/1.00  out_proof_time:                         0.014
% 3.50/1.00  total_time:                             0.21
% 3.50/1.00  num_of_symbols:                         50
% 3.50/1.00  num_of_terms:                           7908
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing
% 3.50/1.00  
% 3.50/1.00  num_of_splits:                          0
% 3.50/1.00  num_of_split_atoms:                     0
% 3.50/1.00  num_of_reused_defs:                     0
% 3.50/1.00  num_eq_ax_congr_red:                    30
% 3.50/1.00  num_of_sem_filtered_clauses:            1
% 3.50/1.00  num_of_subtypes:                        0
% 3.50/1.00  monotx_restored_types:                  0
% 3.50/1.00  sat_num_of_epr_types:                   0
% 3.50/1.00  sat_num_of_non_cyclic_types:            0
% 3.50/1.00  sat_guarded_non_collapsed_types:        0
% 3.50/1.00  num_pure_diseq_elim:                    0
% 3.50/1.00  simp_replaced_by:                       0
% 3.50/1.00  res_preprocessed:                       164
% 3.50/1.00  prep_upred:                             0
% 3.50/1.00  prep_unflattend:                        4
% 3.50/1.00  smt_new_axioms:                         0
% 3.50/1.00  pred_elim_cands:                        1
% 3.50/1.00  pred_elim:                              1
% 3.50/1.00  pred_elim_cl:                           1
% 3.50/1.00  pred_elim_cycles:                       3
% 3.50/1.00  merged_defs:                            0
% 3.50/1.00  merged_defs_ncl:                        0
% 3.50/1.00  bin_hyper_res:                          0
% 3.50/1.00  prep_cycles:                            4
% 3.50/1.00  pred_elim_time:                         0.003
% 3.50/1.00  splitting_time:                         0.
% 3.50/1.00  sem_filter_time:                        0.
% 3.50/1.00  monotx_time:                            0.001
% 3.50/1.00  subtype_inf_time:                       0.
% 3.50/1.00  
% 3.50/1.00  ------ Problem properties
% 3.50/1.00  
% 3.50/1.00  clauses:                                35
% 3.50/1.00  conjectures:                            4
% 3.50/1.00  epr:                                    3
% 3.50/1.00  horn:                                   25
% 3.50/1.00  ground:                                 4
% 3.50/1.00  unary:                                  14
% 3.50/1.00  binary:                                 5
% 3.50/1.00  lits:                                   83
% 3.50/1.00  lits_eq:                                59
% 3.50/1.00  fd_pure:                                0
% 3.50/1.00  fd_pseudo:                              0
% 3.50/1.00  fd_cond:                                7
% 3.50/1.00  fd_pseudo_cond:                         7
% 3.50/1.00  ac_symbols:                             0
% 3.50/1.00  
% 3.50/1.00  ------ Propositional Solver
% 3.50/1.00  
% 3.50/1.00  prop_solver_calls:                      27
% 3.50/1.00  prop_fast_solver_calls:                 1116
% 3.50/1.00  smt_solver_calls:                       0
% 3.50/1.00  smt_fast_solver_calls:                  0
% 3.50/1.00  prop_num_of_clauses:                    2308
% 3.50/1.00  prop_preprocess_simplified:             8426
% 3.50/1.00  prop_fo_subsumed:                       34
% 3.50/1.00  prop_solver_time:                       0.
% 3.50/1.00  smt_solver_time:                        0.
% 3.50/1.00  smt_fast_solver_time:                   0.
% 3.50/1.00  prop_fast_solver_time:                  0.
% 3.50/1.00  prop_unsat_core_time:                   0.
% 3.50/1.00  
% 3.50/1.00  ------ QBF
% 3.50/1.00  
% 3.50/1.00  qbf_q_res:                              0
% 3.50/1.00  qbf_num_tautologies:                    0
% 3.50/1.00  qbf_prep_cycles:                        0
% 3.50/1.00  
% 3.50/1.00  ------ BMC1
% 3.50/1.00  
% 3.50/1.00  bmc1_current_bound:                     -1
% 3.50/1.00  bmc1_last_solved_bound:                 -1
% 3.50/1.00  bmc1_unsat_core_size:                   -1
% 3.50/1.00  bmc1_unsat_core_parents_size:           -1
% 3.50/1.00  bmc1_merge_next_fun:                    0
% 3.50/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.50/1.00  
% 3.50/1.00  ------ Instantiation
% 3.50/1.00  
% 3.50/1.00  inst_num_of_clauses:                    900
% 3.50/1.00  inst_num_in_passive:                    350
% 3.50/1.00  inst_num_in_active:                     436
% 3.50/1.00  inst_num_in_unprocessed:                114
% 3.50/1.00  inst_num_of_loops:                      440
% 3.50/1.00  inst_num_of_learning_restarts:          0
% 3.50/1.00  inst_num_moves_active_passive:          4
% 3.50/1.00  inst_lit_activity:                      0
% 3.50/1.00  inst_lit_activity_moves:                0
% 3.50/1.00  inst_num_tautologies:                   0
% 3.50/1.00  inst_num_prop_implied:                  0
% 3.50/1.00  inst_num_existing_simplified:           0
% 3.50/1.00  inst_num_eq_res_simplified:             0
% 3.50/1.00  inst_num_child_elim:                    0
% 3.50/1.00  inst_num_of_dismatching_blockings:      46
% 3.50/1.00  inst_num_of_non_proper_insts:           835
% 3.50/1.00  inst_num_of_duplicates:                 0
% 3.50/1.00  inst_inst_num_from_inst_to_res:         0
% 3.50/1.00  inst_dismatching_checking_time:         0.
% 3.50/1.00  
% 3.50/1.00  ------ Resolution
% 3.50/1.00  
% 3.50/1.00  res_num_of_clauses:                     0
% 3.50/1.00  res_num_in_passive:                     0
% 3.50/1.00  res_num_in_active:                      0
% 3.50/1.00  res_num_of_loops:                       168
% 3.50/1.00  res_forward_subset_subsumed:            98
% 3.50/1.00  res_backward_subset_subsumed:           0
% 3.50/1.00  res_forward_subsumed:                   0
% 3.50/1.00  res_backward_subsumed:                  0
% 3.50/1.00  res_forward_subsumption_resolution:     0
% 3.50/1.00  res_backward_subsumption_resolution:    0
% 3.50/1.00  res_clause_to_clause_subsumption:       593
% 3.50/1.00  res_orphan_elimination:                 0
% 3.50/1.00  res_tautology_del:                      7
% 3.50/1.00  res_num_eq_res_simplified:              0
% 3.50/1.00  res_num_sel_changes:                    0
% 3.50/1.00  res_moves_from_active_to_pass:          0
% 3.50/1.00  
% 3.50/1.00  ------ Superposition
% 3.50/1.00  
% 3.50/1.00  sup_time_total:                         0.
% 3.50/1.00  sup_time_generating:                    0.
% 3.50/1.00  sup_time_sim_full:                      0.
% 3.50/1.00  sup_time_sim_immed:                     0.
% 3.50/1.00  
% 3.50/1.00  sup_num_of_clauses:                     104
% 3.50/1.00  sup_num_in_active:                      65
% 3.50/1.00  sup_num_in_passive:                     39
% 3.50/1.00  sup_num_of_loops:                       87
% 3.50/1.00  sup_fw_superposition:                   68
% 3.50/1.00  sup_bw_superposition:                   81
% 3.50/1.00  sup_immediate_simplified:               18
% 3.50/1.00  sup_given_eliminated:                   0
% 3.50/1.00  comparisons_done:                       0
% 3.50/1.00  comparisons_avoided:                    11
% 3.50/1.00  
% 3.50/1.00  ------ Simplifications
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  sim_fw_subset_subsumed:                 9
% 3.50/1.00  sim_bw_subset_subsumed:                 5
% 3.50/1.00  sim_fw_subsumed:                        4
% 3.50/1.00  sim_bw_subsumed:                        2
% 3.50/1.00  sim_fw_subsumption_res:                 10
% 3.50/1.00  sim_bw_subsumption_res:                 0
% 3.50/1.00  sim_tautology_del:                      3
% 3.50/1.00  sim_eq_tautology_del:                   15
% 3.50/1.00  sim_eq_res_simp:                        0
% 3.50/1.00  sim_fw_demodulated:                     3
% 3.50/1.00  sim_bw_demodulated:                     18
% 3.50/1.00  sim_light_normalised:                   4
% 3.50/1.00  sim_joinable_taut:                      0
% 3.50/1.00  sim_joinable_simp:                      0
% 3.50/1.00  sim_ac_normalised:                      0
% 3.50/1.00  sim_smt_subsumption:                    0
% 3.50/1.00  
%------------------------------------------------------------------------------
