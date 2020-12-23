%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:33 EST 2020

% Result     : Theorem 27.74s
% Output     : CNFRefutation 27.74s
% Verified   : 
% Statistics : Number of formulae       :  192 (24815 expanded)
%              Number of clauses        :  110 (5470 expanded)
%              Number of leaves         :   20 (7603 expanded)
%              Depth                    :   39
%              Number of atoms          :  647 (135366 expanded)
%              Number of equality atoms :  525 (111664 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
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

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f38])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f108,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f51])).

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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
    ( ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 )
    & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f41,f40])).

fof(f83,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f83,f68])).

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

fof(f74,plain,(
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

fof(f67,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f67,f68])).

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

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f75,f68])).

fof(f80,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f68])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f77,f68])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f107,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f106])).

fof(f73,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f73,f67])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f42])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f110,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f70])).

fof(f79,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f72,f67])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f54])).

fof(f103,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f102])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f36])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f64,f60])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f62,f85])).

fof(f109,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f87])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f105,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f104])).

cnf(c_26,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_694,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_703,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4105,plain,
    ( k1_enumset1(X0,X1,X2) = k1_xboole_0
    | sK2(k1_enumset1(X0,X1,X2)) = X0
    | sK2(k1_enumset1(X0,X1,X2)) = X1
    | sK2(k1_enumset1(X0,X1,X2)) = X2 ),
    inference(superposition,[status(thm)],[c_694,c_703])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_689,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_693,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5190,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_689,c_693])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_690,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1147,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_689,c_690])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1089,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1456,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1147,c_37,c_36,c_35,c_34,c_1089])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_691,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2218,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_689,c_691])).

cnf(c_1086,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2813,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2218,c_37,c_36,c_35,c_34,c_1086])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_692,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3736,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_689,c_692])).

cnf(c_1083,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4408,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3736,c_37,c_36,c_35,c_34,c_1083])).

cnf(c_5191,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5190,c_1456,c_2813,c_4408])).

cnf(c_79,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_82,plain,
    ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_266,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_990,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_991,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_992,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_993,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_994,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_995,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_6111,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5191,c_37,c_36,c_35,c_79,c_82,c_991,c_993,c_995])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_696,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6120,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6111,c_696])).

cnf(c_56882,plain,
    ( k1_enumset1(X0,X1,X2) = k1_xboole_0
    | sK2(k1_enumset1(X0,X1,X2)) = X0
    | sK2(k1_enumset1(X0,X1,X2)) = X2
    | sK6 != X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4105,c_6120])).

cnf(c_61006,plain,
    ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
    | sK2(k1_enumset1(X0,sK6,X1)) = X0
    | sK2(k1_enumset1(X0,sK6,X1)) = X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,sK6,X1)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_56882])).

cnf(c_32,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6119,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(superposition,[status(thm)],[c_6111,c_32])).

cnf(c_6135,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(demodulation,[status(thm)],[c_6119,c_6111])).

cnf(c_33,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4411,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_33,c_4408])).

cnf(c_4413,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(demodulation,[status(thm)],[c_4411,c_1456,c_2813])).

cnf(c_6348,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_4413,c_6119])).

cnf(c_22,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_31,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_742,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_22,c_31])).

cnf(c_6144,plain,
    ( k2_mcart_1(sK6) != sK6 ),
    inference(superposition,[status(thm)],[c_6135,c_742])).

cnf(c_6520,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6348,c_6144])).

cnf(c_6521,plain,
    ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(renaming,[status(thm)],[c_6520])).

cnf(c_6528,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_6521,c_32])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_695,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6121,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6111,c_695])).

cnf(c_56823,plain,
    ( k1_enumset1(X0,X1,X2) = k1_xboole_0
    | sK2(k1_enumset1(X0,X1,X2)) = X1
    | sK2(k1_enumset1(X0,X1,X2)) = X0
    | sK6 != X2
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4105,c_6121])).

cnf(c_60250,plain,
    ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
    | sK2(k1_enumset1(X0,X1,sK6)) = X1
    | sK2(k1_enumset1(X0,X1,sK6)) = X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X1,sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_56823])).

cnf(c_69959,plain,
    ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
    | sK2(k1_enumset1(X0,X1,sK6)) = X1
    | sK2(k1_enumset1(X0,X1,sK6)) = X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(sK6,k1_enumset1(X0,X1,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6528,c_60250])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_5809,plain,
    ( r2_hidden(sK6,k1_enumset1(X0,X1,sK6)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5814,plain,
    ( r2_hidden(sK6,k1_enumset1(X0,X1,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5809])).

cnf(c_70635,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | sK2(k1_enumset1(X0,X1,sK6)) = X0
    | sK2(k1_enumset1(X0,X1,sK6)) = X1
    | k1_enumset1(X0,X1,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_69959,c_5814])).

cnf(c_70636,plain,
    ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
    | sK2(k1_enumset1(X0,X1,sK6)) = X1
    | sK2(k1_enumset1(X0,X1,sK6)) = X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(renaming,[status(thm)],[c_70635])).

cnf(c_70705,plain,
    ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
    | sK2(k1_enumset1(X0,X1,sK6)) = X1
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | sK6 != X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X1,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_70636,c_6121])).

cnf(c_6114,plain,
    ( k4_tarski(k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_4413,c_6111])).

cnf(c_6185,plain,
    ( k4_tarski(k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6114,c_6144])).

cnf(c_7856,plain,
    ( sK2(X0) != sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k1_xboole_0 = X0
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6185,c_695])).

cnf(c_70702,plain,
    ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
    | sK2(k1_enumset1(X0,X1,sK6)) = X1
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | sK6 != X0
    | r2_hidden(sK6,k1_enumset1(X0,X1,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_70636,c_7856])).

cnf(c_73147,plain,
    ( sK6 != X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | sK2(k1_enumset1(X0,X1,sK6)) = X1
    | k1_enumset1(X0,X1,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_70705,c_5814,c_70702])).

cnf(c_73148,plain,
    ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
    | sK2(k1_enumset1(X0,X1,sK6)) = X1
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | sK6 != X0 ),
    inference(renaming,[status(thm)],[c_73147])).

cnf(c_73153,plain,
    ( k1_enumset1(sK6,X0,sK6) = k1_xboole_0
    | sK2(k1_enumset1(sK6,X0,sK6)) = X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(equality_resolution,[status(thm)],[c_73148])).

cnf(c_6525,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK2(X1)
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k1_xboole_0 = X1
    | r2_hidden(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6521,c_695])).

cnf(c_81515,plain,
    ( k1_enumset1(sK6,X0,sK6) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),X1) != X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | r2_hidden(sK6,k1_enumset1(sK6,X0,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_73153,c_6525])).

cnf(c_704,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_83427,plain,
    ( k1_enumset1(sK6,X0,sK6) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),X1) != X0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_81515,c_704])).

cnf(c_83429,plain,
    ( k1_enumset1(sK6,X0,sK6) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | sK6 != X0 ),
    inference(superposition,[status(thm)],[c_6135,c_83427])).

cnf(c_83446,plain,
    ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(equality_resolution,[status(thm)],[c_83429])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_697,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_xboole_0
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2119,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_697])).

cnf(c_7,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_701,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2033,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_701])).

cnf(c_2208,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2119,c_2033])).

cnf(c_85478,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_83446,c_2208])).

cnf(c_105830,plain,
    ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
    | sK2(k1_enumset1(X0,sK6,X1)) = X0
    | sK2(k1_enumset1(X0,sK6,X1)) = X1
    | r2_hidden(sK6,k1_enumset1(X0,sK6,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_61006,c_85478])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_705,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_105835,plain,
    ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
    | sK2(k1_enumset1(X0,sK6,X1)) = X0
    | sK2(k1_enumset1(X0,sK6,X1)) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_105830,c_705])).

cnf(c_106027,plain,
    ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
    | sK2(k1_enumset1(X0,sK6,X1)) = X1
    | sK6 != X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_105835,c_6121])).

cnf(c_5819,plain,
    ( r2_hidden(sK6,k1_enumset1(X0,sK6,X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5824,plain,
    ( r2_hidden(sK6,k1_enumset1(X0,sK6,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5819])).

cnf(c_85518,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_85478,c_6120])).

cnf(c_105963,plain,
    ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
    | sK2(k1_enumset1(X0,sK6,X1)) = X1
    | sK6 != X0
    | r2_hidden(sK6,k1_enumset1(X0,sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_105835,c_85518])).

cnf(c_107114,plain,
    ( sK6 != X0
    | sK2(k1_enumset1(X0,sK6,X1)) = X1
    | k1_enumset1(X0,sK6,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_106027,c_5824,c_105963])).

cnf(c_107115,plain,
    ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
    | sK2(k1_enumset1(X0,sK6,X1)) = X1
    | sK6 != X0 ),
    inference(renaming,[status(thm)],[c_107114])).

cnf(c_107119,plain,
    ( k1_enumset1(sK6,sK6,X0) = k1_xboole_0
    | sK2(k1_enumset1(sK6,sK6,X0)) = X0 ),
    inference(equality_resolution,[status(thm)],[c_107115])).

cnf(c_107859,plain,
    ( sK2(k1_enumset1(sK6,sK6,X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_107119,c_2208])).

cnf(c_107878,plain,
    ( k1_enumset1(sK6,sK6,X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(sK6,k1_enumset1(sK6,sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_107859,c_85518])).

cnf(c_108554,plain,
    ( sK6 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_107878,c_704,c_2208])).

cnf(c_108556,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_108554])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:29:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.74/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.74/4.00  
% 27.74/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.74/4.00  
% 27.74/4.00  ------  iProver source info
% 27.74/4.00  
% 27.74/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.74/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.74/4.00  git: non_committed_changes: false
% 27.74/4.00  git: last_make_outside_of_git: false
% 27.74/4.00  
% 27.74/4.00  ------ 
% 27.74/4.00  ------ Parsing...
% 27.74/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.74/4.00  
% 27.74/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 27.74/4.00  
% 27.74/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.74/4.00  
% 27.74/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.74/4.00  ------ Proving...
% 27.74/4.00  ------ Problem Properties 
% 27.74/4.00  
% 27.74/4.00  
% 27.74/4.00  clauses                                 38
% 27.74/4.00  conjectures                             5
% 27.74/4.00  EPR                                     3
% 27.74/4.00  Horn                                    25
% 27.74/4.00  unary                                   14
% 27.74/4.00  binary                                  6
% 27.74/4.00  lits                                    92
% 27.74/4.00  lits eq                                 53
% 27.74/4.00  fd_pure                                 0
% 27.74/4.00  fd_pseudo                               0
% 27.74/4.00  fd_cond                                 6
% 27.74/4.00  fd_pseudo_cond                          8
% 27.74/4.00  AC symbols                              0
% 27.74/4.00  
% 27.74/4.00  ------ Input Options Time Limit: Unbounded
% 27.74/4.00  
% 27.74/4.00  
% 27.74/4.00  ------ 
% 27.74/4.00  Current options:
% 27.74/4.00  ------ 
% 27.74/4.00  
% 27.74/4.00  
% 27.74/4.00  
% 27.74/4.00  
% 27.74/4.00  ------ Proving...
% 27.74/4.00  
% 27.74/4.00  
% 27.74/4.00  % SZS status Theorem for theBenchmark.p
% 27.74/4.00  
% 27.74/4.00   Resolution empty clause
% 27.74/4.00  
% 27.74/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.74/4.00  
% 27.74/4.00  fof(f12,axiom,(
% 27.74/4.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f20,plain,(
% 27.74/4.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 27.74/4.00    inference(ennf_transformation,[],[f12])).
% 27.74/4.00  
% 27.74/4.00  fof(f38,plain,(
% 27.74/4.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 27.74/4.00    introduced(choice_axiom,[])).
% 27.74/4.00  
% 27.74/4.00  fof(f39,plain,(
% 27.74/4.00    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 27.74/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f38])).
% 27.74/4.00  
% 27.74/4.00  fof(f71,plain,(
% 27.74/4.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f39])).
% 27.74/4.00  
% 27.74/4.00  fof(f4,axiom,(
% 27.74/4.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f18,plain,(
% 27.74/4.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 27.74/4.00    inference(ennf_transformation,[],[f4])).
% 27.74/4.00  
% 27.74/4.00  fof(f29,plain,(
% 27.74/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.74/4.00    inference(nnf_transformation,[],[f18])).
% 27.74/4.00  
% 27.74/4.00  fof(f30,plain,(
% 27.74/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.74/4.00    inference(flattening,[],[f29])).
% 27.74/4.00  
% 27.74/4.00  fof(f31,plain,(
% 27.74/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.74/4.00    inference(rectify,[],[f30])).
% 27.74/4.00  
% 27.74/4.00  fof(f32,plain,(
% 27.74/4.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 27.74/4.00    introduced(choice_axiom,[])).
% 27.74/4.00  
% 27.74/4.00  fof(f33,plain,(
% 27.74/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.74/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 27.74/4.00  
% 27.74/4.00  fof(f51,plain,(
% 27.74/4.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 27.74/4.00    inference(cnf_transformation,[],[f33])).
% 27.74/4.00  
% 27.74/4.00  fof(f108,plain,(
% 27.74/4.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 27.74/4.00    inference(equality_resolution,[],[f51])).
% 27.74/4.00  
% 27.74/4.00  fof(f16,conjecture,(
% 27.74/4.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f17,negated_conjecture,(
% 27.74/4.00    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 27.74/4.00    inference(negated_conjecture,[],[f16])).
% 27.74/4.00  
% 27.74/4.00  fof(f23,plain,(
% 27.74/4.00    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 27.74/4.00    inference(ennf_transformation,[],[f17])).
% 27.74/4.00  
% 27.74/4.00  fof(f41,plain,(
% 27.74/4.00    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK6) = sK6 | k6_mcart_1(X0,X1,X2,sK6) = sK6 | k5_mcart_1(X0,X1,X2,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)))) )),
% 27.74/4.00    introduced(choice_axiom,[])).
% 27.74/4.00  
% 27.74/4.00  fof(f40,plain,(
% 27.74/4.00    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK3,sK4,sK5,X3) = X3 | k6_mcart_1(sK3,sK4,sK5,X3) = X3 | k5_mcart_1(sK3,sK4,sK5,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3)),
% 27.74/4.00    introduced(choice_axiom,[])).
% 27.74/4.00  
% 27.74/4.00  fof(f42,plain,(
% 27.74/4.00    ((k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3),
% 27.74/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f41,f40])).
% 27.74/4.00  
% 27.74/4.00  fof(f83,plain,(
% 27.74/4.00    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 27.74/4.00    inference(cnf_transformation,[],[f42])).
% 27.74/4.00  
% 27.74/4.00  fof(f10,axiom,(
% 27.74/4.00    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f68,plain,(
% 27.74/4.00    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 27.74/4.00    inference(cnf_transformation,[],[f10])).
% 27.74/4.00  
% 27.74/4.00  fof(f98,plain,(
% 27.74/4.00    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 27.74/4.00    inference(definition_unfolding,[],[f83,f68])).
% 27.74/4.00  
% 27.74/4.00  fof(f13,axiom,(
% 27.74/4.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f21,plain,(
% 27.74/4.00    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 27.74/4.00    inference(ennf_transformation,[],[f13])).
% 27.74/4.00  
% 27.74/4.00  fof(f74,plain,(
% 27.74/4.00    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f21])).
% 27.74/4.00  
% 27.74/4.00  fof(f9,axiom,(
% 27.74/4.00    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f67,plain,(
% 27.74/4.00    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 27.74/4.00    inference(cnf_transformation,[],[f9])).
% 27.74/4.00  
% 27.74/4.00  fof(f94,plain,(
% 27.74/4.00    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(definition_unfolding,[],[f74,f67,f68])).
% 27.74/4.00  
% 27.74/4.00  fof(f14,axiom,(
% 27.74/4.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f22,plain,(
% 27.74/4.00    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 27.74/4.00    inference(ennf_transformation,[],[f14])).
% 27.74/4.00  
% 27.74/4.00  fof(f75,plain,(
% 27.74/4.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f22])).
% 27.74/4.00  
% 27.74/4.00  fof(f97,plain,(
% 27.74/4.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(definition_unfolding,[],[f75,f68])).
% 27.74/4.00  
% 27.74/4.00  fof(f80,plain,(
% 27.74/4.00    k1_xboole_0 != sK3),
% 27.74/4.00    inference(cnf_transformation,[],[f42])).
% 27.74/4.00  
% 27.74/4.00  fof(f81,plain,(
% 27.74/4.00    k1_xboole_0 != sK4),
% 27.74/4.00    inference(cnf_transformation,[],[f42])).
% 27.74/4.00  
% 27.74/4.00  fof(f82,plain,(
% 27.74/4.00    k1_xboole_0 != sK5),
% 27.74/4.00    inference(cnf_transformation,[],[f42])).
% 27.74/4.00  
% 27.74/4.00  fof(f76,plain,(
% 27.74/4.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f22])).
% 27.74/4.00  
% 27.74/4.00  fof(f96,plain,(
% 27.74/4.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(definition_unfolding,[],[f76,f68])).
% 27.74/4.00  
% 27.74/4.00  fof(f77,plain,(
% 27.74/4.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f22])).
% 27.74/4.00  
% 27.74/4.00  fof(f95,plain,(
% 27.74/4.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(definition_unfolding,[],[f77,f68])).
% 27.74/4.00  
% 27.74/4.00  fof(f52,plain,(
% 27.74/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 27.74/4.00    inference(cnf_transformation,[],[f33])).
% 27.74/4.00  
% 27.74/4.00  fof(f106,plain,(
% 27.74/4.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 27.74/4.00    inference(equality_resolution,[],[f52])).
% 27.74/4.00  
% 27.74/4.00  fof(f107,plain,(
% 27.74/4.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 27.74/4.00    inference(equality_resolution,[],[f106])).
% 27.74/4.00  
% 27.74/4.00  fof(f73,plain,(
% 27.74/4.00    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f39])).
% 27.74/4.00  
% 27.74/4.00  fof(f92,plain,(
% 27.74/4.00    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(definition_unfolding,[],[f73,f67])).
% 27.74/4.00  
% 27.74/4.00  fof(f15,axiom,(
% 27.74/4.00    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f78,plain,(
% 27.74/4.00    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f15])).
% 27.74/4.00  
% 27.74/4.00  fof(f84,plain,(
% 27.74/4.00    k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6),
% 27.74/4.00    inference(cnf_transformation,[],[f42])).
% 27.74/4.00  
% 27.74/4.00  fof(f11,axiom,(
% 27.74/4.00    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f19,plain,(
% 27.74/4.00    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 27.74/4.00    inference(ennf_transformation,[],[f11])).
% 27.74/4.00  
% 27.74/4.00  fof(f70,plain,(
% 27.74/4.00    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f19])).
% 27.74/4.00  
% 27.74/4.00  fof(f110,plain,(
% 27.74/4.00    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 27.74/4.00    inference(equality_resolution,[],[f70])).
% 27.74/4.00  
% 27.74/4.00  fof(f79,plain,(
% 27.74/4.00    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 27.74/4.00    inference(cnf_transformation,[],[f15])).
% 27.74/4.00  
% 27.74/4.00  fof(f72,plain,(
% 27.74/4.00    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f39])).
% 27.74/4.00  
% 27.74/4.00  fof(f93,plain,(
% 27.74/4.00    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 27.74/4.00    inference(definition_unfolding,[],[f72,f67])).
% 27.74/4.00  
% 27.74/4.00  fof(f54,plain,(
% 27.74/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 27.74/4.00    inference(cnf_transformation,[],[f33])).
% 27.74/4.00  
% 27.74/4.00  fof(f102,plain,(
% 27.74/4.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 27.74/4.00    inference(equality_resolution,[],[f54])).
% 27.74/4.00  
% 27.74/4.00  fof(f103,plain,(
% 27.74/4.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 27.74/4.00    inference(equality_resolution,[],[f102])).
% 27.74/4.00  
% 27.74/4.00  fof(f2,axiom,(
% 27.74/4.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f49,plain,(
% 27.74/4.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f2])).
% 27.74/4.00  
% 27.74/4.00  fof(f8,axiom,(
% 27.74/4.00    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f36,plain,(
% 27.74/4.00    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 27.74/4.00    inference(nnf_transformation,[],[f8])).
% 27.74/4.00  
% 27.74/4.00  fof(f37,plain,(
% 27.74/4.00    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 27.74/4.00    inference(flattening,[],[f36])).
% 27.74/4.00  
% 27.74/4.00  fof(f64,plain,(
% 27.74/4.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f37])).
% 27.74/4.00  
% 27.74/4.00  fof(f6,axiom,(
% 27.74/4.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f60,plain,(
% 27.74/4.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.74/4.00    inference(cnf_transformation,[],[f6])).
% 27.74/4.00  
% 27.74/4.00  fof(f91,plain,(
% 27.74/4.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_xboole_0) )),
% 27.74/4.00    inference(definition_unfolding,[],[f64,f60])).
% 27.74/4.00  
% 27.74/4.00  fof(f3,axiom,(
% 27.74/4.00    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f50,plain,(
% 27.74/4.00    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 27.74/4.00    inference(cnf_transformation,[],[f3])).
% 27.74/4.00  
% 27.74/4.00  fof(f7,axiom,(
% 27.74/4.00    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f34,plain,(
% 27.74/4.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 27.74/4.00    inference(nnf_transformation,[],[f7])).
% 27.74/4.00  
% 27.74/4.00  fof(f35,plain,(
% 27.74/4.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 27.74/4.00    inference(flattening,[],[f34])).
% 27.74/4.00  
% 27.74/4.00  fof(f62,plain,(
% 27.74/4.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 27.74/4.00    inference(cnf_transformation,[],[f35])).
% 27.74/4.00  
% 27.74/4.00  fof(f5,axiom,(
% 27.74/4.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.74/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.74/4.00  
% 27.74/4.00  fof(f59,plain,(
% 27.74/4.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.74/4.00    inference(cnf_transformation,[],[f5])).
% 27.74/4.00  
% 27.74/4.00  fof(f85,plain,(
% 27.74/4.00    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 27.74/4.00    inference(definition_unfolding,[],[f59,f60])).
% 27.74/4.00  
% 27.74/4.00  fof(f87,plain,(
% 27.74/4.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 27.74/4.00    inference(definition_unfolding,[],[f62,f85])).
% 27.74/4.00  
% 27.74/4.00  fof(f109,plain,(
% 27.74/4.00    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 27.74/4.00    inference(equality_resolution,[],[f87])).
% 27.74/4.00  
% 27.74/4.00  fof(f53,plain,(
% 27.74/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 27.74/4.00    inference(cnf_transformation,[],[f33])).
% 27.74/4.00  
% 27.74/4.00  fof(f104,plain,(
% 27.74/4.00    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 27.74/4.00    inference(equality_resolution,[],[f53])).
% 27.74/4.00  
% 27.74/4.00  fof(f105,plain,(
% 27.74/4.00    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 27.74/4.00    inference(equality_resolution,[],[f104])).
% 27.74/4.00  
% 27.74/4.00  cnf(c_26,plain,
% 27.74/4.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 27.74/4.00      inference(cnf_transformation,[],[f71]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_694,plain,
% 27.74/4.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_15,plain,
% 27.74/4.00      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3)) | X0 = X1 | X0 = X2 | X0 = X3 ),
% 27.74/4.00      inference(cnf_transformation,[],[f108]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_703,plain,
% 27.74/4.00      ( X0 = X1
% 27.74/4.00      | X0 = X2
% 27.74/4.00      | X0 = X3
% 27.74/4.00      | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_4105,plain,
% 27.74/4.00      ( k1_enumset1(X0,X1,X2) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,X2)) = X0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,X2)) = X1
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,X2)) = X2 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_694,c_703]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_34,negated_conjecture,
% 27.74/4.00      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 27.74/4.00      inference(cnf_transformation,[],[f98]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_689,plain,
% 27.74/4.00      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_27,plain,
% 27.74/4.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 27.74/4.00      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 27.74/4.00      | k1_xboole_0 = X1
% 27.74/4.00      | k1_xboole_0 = X2
% 27.74/4.00      | k1_xboole_0 = X3 ),
% 27.74/4.00      inference(cnf_transformation,[],[f94]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_693,plain,
% 27.74/4.00      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 27.74/4.00      | k1_xboole_0 = X0
% 27.74/4.00      | k1_xboole_0 = X1
% 27.74/4.00      | k1_xboole_0 = X2
% 27.74/4.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_5190,plain,
% 27.74/4.00      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
% 27.74/4.00      | sK5 = k1_xboole_0
% 27.74/4.00      | sK4 = k1_xboole_0
% 27.74/4.00      | sK3 = k1_xboole_0 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_689,c_693]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_30,plain,
% 27.74/4.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 27.74/4.00      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 27.74/4.00      | k1_xboole_0 = X1
% 27.74/4.00      | k1_xboole_0 = X2
% 27.74/4.00      | k1_xboole_0 = X3 ),
% 27.74/4.00      inference(cnf_transformation,[],[f97]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_690,plain,
% 27.74/4.00      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 27.74/4.00      | k1_xboole_0 = X0
% 27.74/4.00      | k1_xboole_0 = X1
% 27.74/4.00      | k1_xboole_0 = X2
% 27.74/4.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_1147,plain,
% 27.74/4.00      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 27.74/4.00      | sK5 = k1_xboole_0
% 27.74/4.00      | sK4 = k1_xboole_0
% 27.74/4.00      | sK3 = k1_xboole_0 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_689,c_690]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_37,negated_conjecture,
% 27.74/4.00      ( k1_xboole_0 != sK3 ),
% 27.74/4.00      inference(cnf_transformation,[],[f80]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_36,negated_conjecture,
% 27.74/4.00      ( k1_xboole_0 != sK4 ),
% 27.74/4.00      inference(cnf_transformation,[],[f81]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_35,negated_conjecture,
% 27.74/4.00      ( k1_xboole_0 != sK5 ),
% 27.74/4.00      inference(cnf_transformation,[],[f82]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_1089,plain,
% 27.74/4.00      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
% 27.74/4.00      | k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 27.74/4.00      | k1_xboole_0 = sK5
% 27.74/4.00      | k1_xboole_0 = sK4
% 27.74/4.00      | k1_xboole_0 = sK3 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_30]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_1456,plain,
% 27.74/4.00      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
% 27.74/4.00      inference(global_propositional_subsumption,
% 27.74/4.00                [status(thm)],
% 27.74/4.00                [c_1147,c_37,c_36,c_35,c_34,c_1089]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_29,plain,
% 27.74/4.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 27.74/4.00      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 27.74/4.00      | k1_xboole_0 = X1
% 27.74/4.00      | k1_xboole_0 = X2
% 27.74/4.00      | k1_xboole_0 = X3 ),
% 27.74/4.00      inference(cnf_transformation,[],[f96]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_691,plain,
% 27.74/4.00      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 27.74/4.00      | k1_xboole_0 = X0
% 27.74/4.00      | k1_xboole_0 = X1
% 27.74/4.00      | k1_xboole_0 = X2
% 27.74/4.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_2218,plain,
% 27.74/4.00      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 27.74/4.00      | sK5 = k1_xboole_0
% 27.74/4.00      | sK4 = k1_xboole_0
% 27.74/4.00      | sK3 = k1_xboole_0 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_689,c_691]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_1086,plain,
% 27.74/4.00      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
% 27.74/4.00      | k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 27.74/4.00      | k1_xboole_0 = sK5
% 27.74/4.00      | k1_xboole_0 = sK4
% 27.74/4.00      | k1_xboole_0 = sK3 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_29]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_2813,plain,
% 27.74/4.00      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
% 27.74/4.00      inference(global_propositional_subsumption,
% 27.74/4.00                [status(thm)],
% 27.74/4.00                [c_2218,c_37,c_36,c_35,c_34,c_1086]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_28,plain,
% 27.74/4.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 27.74/4.00      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 27.74/4.00      | k1_xboole_0 = X1
% 27.74/4.00      | k1_xboole_0 = X2
% 27.74/4.00      | k1_xboole_0 = X3 ),
% 27.74/4.00      inference(cnf_transformation,[],[f95]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_692,plain,
% 27.74/4.00      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 27.74/4.00      | k1_xboole_0 = X0
% 27.74/4.00      | k1_xboole_0 = X1
% 27.74/4.00      | k1_xboole_0 = X2
% 27.74/4.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_3736,plain,
% 27.74/4.00      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
% 27.74/4.00      | sK5 = k1_xboole_0
% 27.74/4.00      | sK4 = k1_xboole_0
% 27.74/4.00      | sK3 = k1_xboole_0 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_689,c_692]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_1083,plain,
% 27.74/4.00      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
% 27.74/4.00      | k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
% 27.74/4.00      | k1_xboole_0 = sK5
% 27.74/4.00      | k1_xboole_0 = sK4
% 27.74/4.00      | k1_xboole_0 = sK3 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_28]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_4408,plain,
% 27.74/4.00      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
% 27.74/4.00      inference(global_propositional_subsumption,
% 27.74/4.00                [status(thm)],
% 27.74/4.00                [c_3736,c_37,c_36,c_35,c_34,c_1083]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_5191,plain,
% 27.74/4.00      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
% 27.74/4.00      | sK5 = k1_xboole_0
% 27.74/4.00      | sK4 = k1_xboole_0
% 27.74/4.00      | sK3 = k1_xboole_0 ),
% 27.74/4.00      inference(light_normalisation,
% 27.74/4.00                [status(thm)],
% 27.74/4.00                [c_5190,c_1456,c_2813,c_4408]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_79,plain,
% 27.74/4.00      ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 27.74/4.00      | k1_xboole_0 = k1_xboole_0 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_15]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_14,plain,
% 27.74/4.00      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 27.74/4.00      inference(cnf_transformation,[],[f107]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_82,plain,
% 27.74/4.00      ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_14]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_266,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_990,plain,
% 27.74/4.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_266]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_991,plain,
% 27.74/4.00      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_990]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_992,plain,
% 27.74/4.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_266]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_993,plain,
% 27.74/4.00      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_992]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_994,plain,
% 27.74/4.00      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_266]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_995,plain,
% 27.74/4.00      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_994]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6111,plain,
% 27.74/4.00      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(global_propositional_subsumption,
% 27.74/4.00                [status(thm)],
% 27.74/4.00                [c_5191,c_37,c_36,c_35,c_79,c_82,c_991,c_993,c_995]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_24,plain,
% 27.74/4.00      ( ~ r2_hidden(X0,X1)
% 27.74/4.00      | k4_tarski(k4_tarski(X2,X0),X3) != sK2(X1)
% 27.74/4.00      | k1_xboole_0 = X1 ),
% 27.74/4.00      inference(cnf_transformation,[],[f92]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_696,plain,
% 27.74/4.00      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 27.74/4.00      | k1_xboole_0 = X3
% 27.74/4.00      | r2_hidden(X1,X3) != iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6120,plain,
% 27.74/4.00      ( sK2(X0) != sK6
% 27.74/4.00      | k1_xboole_0 = X0
% 27.74/4.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6111,c_696]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_56882,plain,
% 27.74/4.00      ( k1_enumset1(X0,X1,X2) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,X2)) = X0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,X2)) = X2
% 27.74/4.00      | sK6 != X1
% 27.74/4.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X1,X2)) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_4105,c_6120]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_61006,plain,
% 27.74/4.00      ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X1
% 27.74/4.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,sK6,X1)) != iProver_top ),
% 27.74/4.00      inference(equality_resolution,[status(thm)],[c_56882]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_32,plain,
% 27.74/4.00      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 27.74/4.00      inference(cnf_transformation,[],[f78]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6119,plain,
% 27.74/4.00      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6111,c_32]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6135,plain,
% 27.74/4.00      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(demodulation,[status(thm)],[c_6119,c_6111]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_33,negated_conjecture,
% 27.74/4.00      ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 27.74/4.00      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 27.74/4.00      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
% 27.74/4.00      inference(cnf_transformation,[],[f84]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_4411,plain,
% 27.74/4.00      ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 27.74/4.00      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 27.74/4.00      | k2_mcart_1(sK6) = sK6 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_33,c_4408]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_4413,plain,
% 27.74/4.00      ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | k2_mcart_1(sK6) = sK6 ),
% 27.74/4.00      inference(demodulation,[status(thm)],[c_4411,c_1456,c_2813]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6348,plain,
% 27.74/4.00      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | k2_mcart_1(sK6) = sK6 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_4413,c_6119]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_22,plain,
% 27.74/4.00      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 27.74/4.00      inference(cnf_transformation,[],[f110]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_31,plain,
% 27.74/4.00      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 27.74/4.00      inference(cnf_transformation,[],[f79]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_742,plain,
% 27.74/4.00      ( k4_tarski(X0,X1) != X1 ),
% 27.74/4.00      inference(light_normalisation,[status(thm)],[c_22,c_31]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6144,plain,
% 27.74/4.00      ( k2_mcart_1(sK6) != sK6 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6135,c_742]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6520,plain,
% 27.74/4.00      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 27.74/4.00      inference(global_propositional_subsumption,[status(thm)],[c_6348,c_6144]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6521,plain,
% 27.74/4.00      ( k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(renaming,[status(thm)],[c_6520]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6528,plain,
% 27.74/4.00      ( k1_mcart_1(k1_mcart_1(sK6)) = sK6 | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6521,c_32]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_25,plain,
% 27.74/4.00      ( ~ r2_hidden(X0,X1)
% 27.74/4.00      | k4_tarski(k4_tarski(X0,X2),X3) != sK2(X1)
% 27.74/4.00      | k1_xboole_0 = X1 ),
% 27.74/4.00      inference(cnf_transformation,[],[f93]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_695,plain,
% 27.74/4.00      ( k4_tarski(k4_tarski(X0,X1),X2) != sK2(X3)
% 27.74/4.00      | k1_xboole_0 = X3
% 27.74/4.00      | r2_hidden(X0,X3) != iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6121,plain,
% 27.74/4.00      ( sK2(X0) != sK6
% 27.74/4.00      | k1_xboole_0 = X0
% 27.74/4.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6111,c_695]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_56823,plain,
% 27.74/4.00      ( k1_enumset1(X0,X1,X2) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,X2)) = X1
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,X2)) = X0
% 27.74/4.00      | sK6 != X2
% 27.74/4.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X1,X2)) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_4105,c_6121]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_60250,plain,
% 27.74/4.00      ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X1
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X0
% 27.74/4.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X1,sK6)) != iProver_top ),
% 27.74/4.00      inference(equality_resolution,[status(thm)],[c_56823]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_69959,plain,
% 27.74/4.00      ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X1
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X0
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | r2_hidden(sK6,k1_enumset1(X0,X1,sK6)) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6528,c_60250]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_12,plain,
% 27.74/4.00      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 27.74/4.00      inference(cnf_transformation,[],[f103]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_5809,plain,
% 27.74/4.00      ( r2_hidden(sK6,k1_enumset1(X0,X1,sK6)) ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_12]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_5814,plain,
% 27.74/4.00      ( r2_hidden(sK6,k1_enumset1(X0,X1,sK6)) = iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_5809]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_70635,plain,
% 27.74/4.00      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X1
% 27.74/4.00      | k1_enumset1(X0,X1,sK6) = k1_xboole_0 ),
% 27.74/4.00      inference(global_propositional_subsumption,
% 27.74/4.00                [status(thm)],
% 27.74/4.00                [c_69959,c_5814]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_70636,plain,
% 27.74/4.00      ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X1
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X0
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(renaming,[status(thm)],[c_70635]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_70705,plain,
% 27.74/4.00      ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X1
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | sK6 != X0
% 27.74/4.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,X1,sK6)) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_70636,c_6121]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6114,plain,
% 27.74/4.00      ( k4_tarski(k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | k2_mcart_1(sK6) = sK6 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_4413,c_6111]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6185,plain,
% 27.74/4.00      ( k4_tarski(k4_tarski(sK6,k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(forward_subsumption_resolution,[status(thm)],[c_6114,c_6144]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_7856,plain,
% 27.74/4.00      ( sK2(X0) != sK6
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | k1_xboole_0 = X0
% 27.74/4.00      | r2_hidden(sK6,X0) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6185,c_695]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_70702,plain,
% 27.74/4.00      ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X1
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | sK6 != X0
% 27.74/4.00      | r2_hidden(sK6,k1_enumset1(X0,X1,sK6)) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_70636,c_7856]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_73147,plain,
% 27.74/4.00      ( sK6 != X0
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X1
% 27.74/4.00      | k1_enumset1(X0,X1,sK6) = k1_xboole_0 ),
% 27.74/4.00      inference(global_propositional_subsumption,
% 27.74/4.00                [status(thm)],
% 27.74/4.00                [c_70705,c_5814,c_70702]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_73148,plain,
% 27.74/4.00      ( k1_enumset1(X0,X1,sK6) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,X1,sK6)) = X1
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | sK6 != X0 ),
% 27.74/4.00      inference(renaming,[status(thm)],[c_73147]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_73153,plain,
% 27.74/4.00      ( k1_enumset1(sK6,X0,sK6) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(sK6,X0,sK6)) = X0
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(equality_resolution,[status(thm)],[c_73148]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6525,plain,
% 27.74/4.00      ( k4_tarski(k1_mcart_1(sK6),X0) != sK2(X1)
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | k1_xboole_0 = X1
% 27.74/4.00      | r2_hidden(sK6,X1) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6521,c_695]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_81515,plain,
% 27.74/4.00      ( k1_enumset1(sK6,X0,sK6) = k1_xboole_0
% 27.74/4.00      | k4_tarski(k1_mcart_1(sK6),X1) != X0
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | r2_hidden(sK6,k1_enumset1(sK6,X0,sK6)) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_73153,c_6525]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_704,plain,
% 27.74/4.00      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) = iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_83427,plain,
% 27.74/4.00      ( k1_enumset1(sK6,X0,sK6) = k1_xboole_0
% 27.74/4.00      | k4_tarski(k1_mcart_1(sK6),X1) != X0
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(forward_subsumption_resolution,[status(thm)],[c_81515,c_704]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_83429,plain,
% 27.74/4.00      ( k1_enumset1(sK6,X0,sK6) = k1_xboole_0
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 27.74/4.00      | sK6 != X0 ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6135,c_83427]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_83446,plain,
% 27.74/4.00      ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0
% 27.74/4.00      | k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(equality_resolution,[status(thm)],[c_83429]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_6,plain,
% 27.74/4.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.74/4.00      inference(cnf_transformation,[],[f49]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_21,plain,
% 27.74/4.00      ( r2_hidden(X0,X1)
% 27.74/4.00      | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_xboole_0 ),
% 27.74/4.00      inference(cnf_transformation,[],[f91]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_697,plain,
% 27.74/4.00      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_xboole_0
% 27.74/4.00      | r2_hidden(X0,X2) = iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_2119,plain,
% 27.74/4.00      ( k1_enumset1(X0,X0,X1) != k1_xboole_0
% 27.74/4.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_6,c_697]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_7,plain,
% 27.74/4.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.74/4.00      inference(cnf_transformation,[],[f50]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_17,plain,
% 27.74/4.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) ),
% 27.74/4.00      inference(cnf_transformation,[],[f109]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_701,plain,
% 27.74/4.00      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) != iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_2033,plain,
% 27.74/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_7,c_701]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_2208,plain,
% 27.74/4.00      ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
% 27.74/4.00      inference(global_propositional_subsumption,[status(thm)],[c_2119,c_2033]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_85478,plain,
% 27.74/4.00      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6 ),
% 27.74/4.00      inference(forward_subsumption_resolution,[status(thm)],[c_83446,c_2208]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_105830,plain,
% 27.74/4.00      ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X1
% 27.74/4.00      | r2_hidden(sK6,k1_enumset1(X0,sK6,X1)) != iProver_top ),
% 27.74/4.00      inference(light_normalisation,[status(thm)],[c_61006,c_85478]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_13,plain,
% 27.74/4.00      ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
% 27.74/4.00      inference(cnf_transformation,[],[f105]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_705,plain,
% 27.74/4.00      ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) = iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_105835,plain,
% 27.74/4.00      ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X1 ),
% 27.74/4.00      inference(forward_subsumption_resolution,[status(thm)],[c_105830,c_705]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_106027,plain,
% 27.74/4.00      ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X1
% 27.74/4.00      | sK6 != X0
% 27.74/4.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_enumset1(X0,sK6,X1)) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_105835,c_6121]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_5819,plain,
% 27.74/4.00      ( r2_hidden(sK6,k1_enumset1(X0,sK6,X1)) ),
% 27.74/4.00      inference(instantiation,[status(thm)],[c_13]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_5824,plain,
% 27.74/4.00      ( r2_hidden(sK6,k1_enumset1(X0,sK6,X1)) = iProver_top ),
% 27.74/4.00      inference(predicate_to_equality,[status(thm)],[c_5819]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_85518,plain,
% 27.74/4.00      ( sK2(X0) != sK6 | k1_xboole_0 = X0 | r2_hidden(sK6,X0) != iProver_top ),
% 27.74/4.00      inference(demodulation,[status(thm)],[c_85478,c_6120]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_105963,plain,
% 27.74/4.00      ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X1
% 27.74/4.00      | sK6 != X0
% 27.74/4.00      | r2_hidden(sK6,k1_enumset1(X0,sK6,X1)) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_105835,c_85518]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_107114,plain,
% 27.74/4.00      ( sK6 != X0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X1
% 27.74/4.00      | k1_enumset1(X0,sK6,X1) = k1_xboole_0 ),
% 27.74/4.00      inference(global_propositional_subsumption,
% 27.74/4.00                [status(thm)],
% 27.74/4.00                [c_106027,c_5824,c_105963]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_107115,plain,
% 27.74/4.00      ( k1_enumset1(X0,sK6,X1) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(X0,sK6,X1)) = X1
% 27.74/4.00      | sK6 != X0 ),
% 27.74/4.00      inference(renaming,[status(thm)],[c_107114]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_107119,plain,
% 27.74/4.00      ( k1_enumset1(sK6,sK6,X0) = k1_xboole_0
% 27.74/4.00      | sK2(k1_enumset1(sK6,sK6,X0)) = X0 ),
% 27.74/4.00      inference(equality_resolution,[status(thm)],[c_107115]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_107859,plain,
% 27.74/4.00      ( sK2(k1_enumset1(sK6,sK6,X0)) = X0 ),
% 27.74/4.00      inference(forward_subsumption_resolution,[status(thm)],[c_107119,c_2208]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_107878,plain,
% 27.74/4.00      ( k1_enumset1(sK6,sK6,X0) = k1_xboole_0
% 27.74/4.00      | sK6 != X0
% 27.74/4.00      | r2_hidden(sK6,k1_enumset1(sK6,sK6,X0)) != iProver_top ),
% 27.74/4.00      inference(superposition,[status(thm)],[c_107859,c_85518]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_108554,plain,
% 27.74/4.00      ( sK6 != X0 ),
% 27.74/4.00      inference(forward_subsumption_resolution,
% 27.74/4.00                [status(thm)],
% 27.74/4.00                [c_107878,c_704,c_2208]) ).
% 27.74/4.00  
% 27.74/4.00  cnf(c_108556,plain,
% 27.74/4.00      ( $false ),
% 27.74/4.00      inference(equality_resolution,[status(thm)],[c_108554]) ).
% 27.74/4.00  
% 27.74/4.00  
% 27.74/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.74/4.00  
% 27.74/4.00  ------                               Statistics
% 27.74/4.00  
% 27.74/4.00  ------ Selected
% 27.74/4.00  
% 27.74/4.00  total_time:                             3.16
% 27.74/4.00  
%------------------------------------------------------------------------------
