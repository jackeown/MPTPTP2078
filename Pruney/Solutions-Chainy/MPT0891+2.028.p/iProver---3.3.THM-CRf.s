%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:36 EST 2020

% Result     : Theorem 23.61s
% Output     : CNFRefutation 23.61s
% Verified   : 
% Statistics : Number of formulae       :  191 (5080 expanded)
%              Number of clauses        :  107 (1381 expanded)
%              Number of leaves         :   21 (1451 expanded)
%              Depth                    :   25
%              Number of atoms          :  598 (27013 expanded)
%              Number of equality atoms :  488 (21359 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f59,f52,f53])).

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

fof(f22,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
      | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
      | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 )
    & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f34,f33])).

fof(f68,plain,(
    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f68,f53])).

fof(f65,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f92,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f76])).

fof(f93,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f92])).

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

fof(f21,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f53])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f53])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f90,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f91,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f90])).

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

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f31])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f46,f46])).

fof(f58,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f69,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f55])).

fof(f64,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f52])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_338,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | sK5 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_339,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK5),k6_mcart_1(X0,X1,X2,sK5)),k7_mcart_1(X0,X1,X2,sK5)) = sK5
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_1262,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_339])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_67,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_70,plain,
    ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_528,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1107,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_1108,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1107])).

cnf(c_1109,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_1110,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_1111,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_1112,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_1617,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_28,c_27,c_26,c_67,c_70,c_1108,c_1110,c_1112])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_320,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | sK5 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_321,plain,
    ( k7_mcart_1(X0,X1,X2,sK5) = k2_mcart_1(sK5)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_1174,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_321])).

cnf(c_1451,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1174,c_28,c_27,c_26,c_67,c_70,c_1108,c_1110,c_1112])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_284,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | sK5 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_285,plain,
    ( k5_mcart_1(X0,X1,X2,sK5) = k1_mcart_1(k1_mcart_1(sK5))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_1180,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_285])).

cnf(c_1586,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1180,c_28,c_27,c_26,c_67,c_70,c_1108,c_1110,c_1112])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_302,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | sK5 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_303,plain,
    ( k6_mcart_1(X0,X1,X2,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_1256,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_303])).

cnf(c_1611,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1256,c_28,c_27,c_26,c_67,c_70,c_1108,c_1110,c_1112])).

cnf(c_1619,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_1617,c_1451,c_1586,c_1611])).

cnf(c_23,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1621,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
    inference(superposition,[status(thm)],[c_1619,c_23])).

cnf(c_1657,plain,
    ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_1621,c_1619])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_913,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_903,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_911,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2413,plain,
    ( k1_enumset1(X0,X0,X1) = k1_xboole_0
    | sK1(k1_enumset1(X0,X0,X1)) = X0
    | sK1(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_903,c_911])).

cnf(c_69,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_929,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_0,c_1])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_906,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2592,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0
    | r2_hidden(X0,k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_929,c_906])).

cnf(c_3702,plain,
    ( sK1(k1_enumset1(X0,X0,X1)) = X0
    | sK1(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2413,c_69,c_2592])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_905,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2302,plain,
    ( k4_tarski(k1_mcart_1(sK5),X0) != sK1(X1)
    | k1_xboole_0 = X1
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1621,c_905])).

cnf(c_2471,plain,
    ( sK1(X0) != sK5
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_2302])).

cnf(c_3729,plain,
    ( k1_enumset1(X0,X0,X1) = k1_xboole_0
    | sK1(k1_enumset1(X0,X0,X1)) = X1
    | sK5 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_2471])).

cnf(c_4318,plain,
    ( sK1(k1_enumset1(X0,X0,X1)) = X1
    | sK5 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3729,c_69,c_2592])).

cnf(c_4325,plain,
    ( sK1(k1_enumset1(sK5,sK5,X0)) = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(sK5,sK5,X0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4318])).

cnf(c_69039,plain,
    ( sK1(k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5)))) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(superposition,[status(thm)],[c_913,c_4325])).

cnf(c_69190,plain,
    ( k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5))) = k1_xboole_0
    | k4_tarski(k4_tarski(X0,X1),X2) != k2_mcart_1(k1_mcart_1(sK5))
    | r2_hidden(X1,k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_69039,c_905])).

cnf(c_2934,plain,
    ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2592,c_69])).

cnf(c_136681,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != k2_mcart_1(k1_mcart_1(sK5))
    | r2_hidden(X1,k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_69190,c_2934])).

cnf(c_136714,plain,
    ( k4_tarski(k1_mcart_1(sK5),X0) != k2_mcart_1(k1_mcart_1(sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1621,c_136681])).

cnf(c_136777,plain,
    ( k4_tarski(k1_mcart_1(sK5),X0) != k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_136714,c_913])).

cnf(c_136793,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) != sK5 ),
    inference(superposition,[status(thm)],[c_1657,c_136777])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_enumset1(X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_910,plain,
    ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2412,plain,
    ( X0 = X1
    | X0 = X2
    | k4_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X0)) = k1_enumset1(X2,X2,X1) ),
    inference(superposition,[status(thm)],[c_910,c_911])).

cnf(c_4143,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X2,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2412,c_906])).

cnf(c_4197,plain,
    ( X0 = X1
    | k1_enumset1(X1,X1,X1) = k1_xboole_0
    | sK1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_903,c_4143])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_enumset1(X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_909,plain,
    ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2375,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0
    | r2_hidden(X0,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_929,c_909])).

cnf(c_912,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2931,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2375,c_912])).

cnf(c_4619,plain,
    ( X0 = X1
    | sK1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4197,c_2931])).

cnf(c_24,negated_conjecture,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1454,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_24,c_1451])).

cnf(c_1614,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1454,c_1611])).

cnf(c_1616,plain,
    ( k1_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_1614,c_1586])).

cnf(c_1658,plain,
    ( k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5)
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1616,c_1621])).

cnf(c_13,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_22,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_939,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_13,c_22])).

cnf(c_1743,plain,
    ( k2_mcart_1(sK5) != sK5 ),
    inference(superposition,[status(thm)],[c_1657,c_939])).

cnf(c_1864,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1658,c_1743])).

cnf(c_1865,plain,
    ( k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5)
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
    inference(renaming,[status(thm)],[c_1864])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_904,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1870,plain,
    ( k4_tarski(k1_mcart_1(sK5),X0) != sK1(X1)
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k1_xboole_0 = X1
    | r2_hidden(sK5,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1865,c_904])).

cnf(c_4632,plain,
    ( X0 = X1
    | k1_enumset1(X1,X1,X1) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK5),X2) != X1
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | r2_hidden(sK5,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4619,c_1870])).

cnf(c_102059,plain,
    ( X0 = X1
    | k4_tarski(k1_mcart_1(sK5),X2) != X0
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | r2_hidden(sK5,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4632,c_2931])).

cnf(c_1655,plain,
    ( k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1616,c_1619])).

cnf(c_1885,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1655,c_1743])).

cnf(c_1886,plain,
    ( k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
    inference(renaming,[status(thm)],[c_1885])).

cnf(c_1894,plain,
    ( sK1(X0) != sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k1_xboole_0 = X0
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_904])).

cnf(c_4627,plain,
    ( X0 = X1
    | k1_enumset1(X1,X1,X1) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | sK5 != X1
    | r2_hidden(sK5,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4619,c_1894])).

cnf(c_4194,plain,
    ( X0 = X1
    | X2 = X1
    | k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X1,X1,X1) ),
    inference(superposition,[status(thm)],[c_910,c_4143])).

cnf(c_5260,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4194,c_909])).

cnf(c_8022,plain,
    ( X0 = X1
    | k1_enumset1(X0,X0,X0) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | r2_hidden(sK5,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4627,c_5260])).

cnf(c_102061,plain,
    ( X0 = X1
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | r2_hidden(sK5,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_102059,c_2931,c_8022])).

cnf(c_102065,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | sK5 = X0 ),
    inference(superposition,[status(thm)],[c_913,c_102061])).

cnf(c_102905,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | sK5 != sK5 ),
    inference(equality_factoring,[status(thm)],[c_102065])).

cnf(c_102908,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_102905])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_136793,c_102908])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.61/3.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.61/3.51  
% 23.61/3.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.61/3.51  
% 23.61/3.51  ------  iProver source info
% 23.61/3.51  
% 23.61/3.51  git: date: 2020-06-30 10:37:57 +0100
% 23.61/3.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.61/3.51  git: non_committed_changes: false
% 23.61/3.51  git: last_make_outside_of_git: false
% 23.61/3.51  
% 23.61/3.51  ------ 
% 23.61/3.51  
% 23.61/3.51  ------ Input Options
% 23.61/3.51  
% 23.61/3.51  --out_options                           all
% 23.61/3.51  --tptp_safe_out                         true
% 23.61/3.51  --problem_path                          ""
% 23.61/3.51  --include_path                          ""
% 23.61/3.51  --clausifier                            res/vclausify_rel
% 23.61/3.51  --clausifier_options                    --mode clausify
% 23.61/3.51  --stdin                                 false
% 23.61/3.51  --stats_out                             all
% 23.61/3.51  
% 23.61/3.51  ------ General Options
% 23.61/3.51  
% 23.61/3.51  --fof                                   false
% 23.61/3.51  --time_out_real                         305.
% 23.61/3.51  --time_out_virtual                      -1.
% 23.61/3.51  --symbol_type_check                     false
% 23.61/3.51  --clausify_out                          false
% 23.61/3.51  --sig_cnt_out                           false
% 23.61/3.51  --trig_cnt_out                          false
% 23.61/3.51  --trig_cnt_out_tolerance                1.
% 23.61/3.51  --trig_cnt_out_sk_spl                   false
% 23.61/3.51  --abstr_cl_out                          false
% 23.61/3.51  
% 23.61/3.51  ------ Global Options
% 23.61/3.51  
% 23.61/3.51  --schedule                              default
% 23.61/3.51  --add_important_lit                     false
% 23.61/3.51  --prop_solver_per_cl                    1000
% 23.61/3.51  --min_unsat_core                        false
% 23.61/3.51  --soft_assumptions                      false
% 23.61/3.51  --soft_lemma_size                       3
% 23.61/3.51  --prop_impl_unit_size                   0
% 23.61/3.51  --prop_impl_unit                        []
% 23.61/3.51  --share_sel_clauses                     true
% 23.61/3.51  --reset_solvers                         false
% 23.61/3.51  --bc_imp_inh                            [conj_cone]
% 23.61/3.51  --conj_cone_tolerance                   3.
% 23.61/3.51  --extra_neg_conj                        none
% 23.61/3.51  --large_theory_mode                     true
% 23.61/3.51  --prolific_symb_bound                   200
% 23.61/3.51  --lt_threshold                          2000
% 23.61/3.51  --clause_weak_htbl                      true
% 23.61/3.51  --gc_record_bc_elim                     false
% 23.61/3.51  
% 23.61/3.51  ------ Preprocessing Options
% 23.61/3.51  
% 23.61/3.51  --preprocessing_flag                    true
% 23.61/3.51  --time_out_prep_mult                    0.1
% 23.61/3.51  --splitting_mode                        input
% 23.61/3.51  --splitting_grd                         true
% 23.61/3.51  --splitting_cvd                         false
% 23.61/3.51  --splitting_cvd_svl                     false
% 23.61/3.51  --splitting_nvd                         32
% 23.61/3.51  --sub_typing                            true
% 23.61/3.51  --prep_gs_sim                           true
% 23.61/3.51  --prep_unflatten                        true
% 23.61/3.51  --prep_res_sim                          true
% 23.61/3.51  --prep_upred                            true
% 23.61/3.51  --prep_sem_filter                       exhaustive
% 23.61/3.51  --prep_sem_filter_out                   false
% 23.61/3.51  --pred_elim                             true
% 23.61/3.51  --res_sim_input                         true
% 23.61/3.51  --eq_ax_congr_red                       true
% 23.61/3.51  --pure_diseq_elim                       true
% 23.61/3.51  --brand_transform                       false
% 23.61/3.51  --non_eq_to_eq                          false
% 23.61/3.51  --prep_def_merge                        true
% 23.61/3.51  --prep_def_merge_prop_impl              false
% 23.61/3.51  --prep_def_merge_mbd                    true
% 23.61/3.51  --prep_def_merge_tr_red                 false
% 23.61/3.51  --prep_def_merge_tr_cl                  false
% 23.61/3.51  --smt_preprocessing                     true
% 23.61/3.51  --smt_ac_axioms                         fast
% 23.61/3.51  --preprocessed_out                      false
% 23.61/3.51  --preprocessed_stats                    false
% 23.61/3.51  
% 23.61/3.51  ------ Abstraction refinement Options
% 23.61/3.51  
% 23.61/3.51  --abstr_ref                             []
% 23.61/3.51  --abstr_ref_prep                        false
% 23.61/3.51  --abstr_ref_until_sat                   false
% 23.61/3.51  --abstr_ref_sig_restrict                funpre
% 23.61/3.51  --abstr_ref_af_restrict_to_split_sk     false
% 23.61/3.51  --abstr_ref_under                       []
% 23.61/3.51  
% 23.61/3.51  ------ SAT Options
% 23.61/3.51  
% 23.61/3.51  --sat_mode                              false
% 23.61/3.51  --sat_fm_restart_options                ""
% 23.61/3.51  --sat_gr_def                            false
% 23.61/3.51  --sat_epr_types                         true
% 23.61/3.51  --sat_non_cyclic_types                  false
% 23.61/3.51  --sat_finite_models                     false
% 23.61/3.51  --sat_fm_lemmas                         false
% 23.61/3.51  --sat_fm_prep                           false
% 23.61/3.51  --sat_fm_uc_incr                        true
% 23.61/3.51  --sat_out_model                         small
% 23.61/3.51  --sat_out_clauses                       false
% 23.61/3.51  
% 23.61/3.51  ------ QBF Options
% 23.61/3.51  
% 23.61/3.51  --qbf_mode                              false
% 23.61/3.51  --qbf_elim_univ                         false
% 23.61/3.51  --qbf_dom_inst                          none
% 23.61/3.51  --qbf_dom_pre_inst                      false
% 23.61/3.51  --qbf_sk_in                             false
% 23.61/3.51  --qbf_pred_elim                         true
% 23.61/3.51  --qbf_split                             512
% 23.61/3.51  
% 23.61/3.51  ------ BMC1 Options
% 23.61/3.51  
% 23.61/3.51  --bmc1_incremental                      false
% 23.61/3.51  --bmc1_axioms                           reachable_all
% 23.61/3.51  --bmc1_min_bound                        0
% 23.61/3.51  --bmc1_max_bound                        -1
% 23.61/3.51  --bmc1_max_bound_default                -1
% 23.61/3.51  --bmc1_symbol_reachability              true
% 23.61/3.51  --bmc1_property_lemmas                  false
% 23.61/3.51  --bmc1_k_induction                      false
% 23.61/3.51  --bmc1_non_equiv_states                 false
% 23.61/3.51  --bmc1_deadlock                         false
% 23.61/3.51  --bmc1_ucm                              false
% 23.61/3.51  --bmc1_add_unsat_core                   none
% 23.61/3.52  --bmc1_unsat_core_children              false
% 23.61/3.52  --bmc1_unsat_core_extrapolate_axioms    false
% 23.61/3.52  --bmc1_out_stat                         full
% 23.61/3.52  --bmc1_ground_init                      false
% 23.61/3.52  --bmc1_pre_inst_next_state              false
% 23.61/3.52  --bmc1_pre_inst_state                   false
% 23.61/3.52  --bmc1_pre_inst_reach_state             false
% 23.61/3.52  --bmc1_out_unsat_core                   false
% 23.61/3.52  --bmc1_aig_witness_out                  false
% 23.61/3.52  --bmc1_verbose                          false
% 23.61/3.52  --bmc1_dump_clauses_tptp                false
% 23.61/3.52  --bmc1_dump_unsat_core_tptp             false
% 23.61/3.52  --bmc1_dump_file                        -
% 23.61/3.52  --bmc1_ucm_expand_uc_limit              128
% 23.61/3.52  --bmc1_ucm_n_expand_iterations          6
% 23.61/3.52  --bmc1_ucm_extend_mode                  1
% 23.61/3.52  --bmc1_ucm_init_mode                    2
% 23.61/3.52  --bmc1_ucm_cone_mode                    none
% 23.61/3.52  --bmc1_ucm_reduced_relation_type        0
% 23.61/3.52  --bmc1_ucm_relax_model                  4
% 23.61/3.52  --bmc1_ucm_full_tr_after_sat            true
% 23.61/3.52  --bmc1_ucm_expand_neg_assumptions       false
% 23.61/3.52  --bmc1_ucm_layered_model                none
% 23.61/3.52  --bmc1_ucm_max_lemma_size               10
% 23.61/3.52  
% 23.61/3.52  ------ AIG Options
% 23.61/3.52  
% 23.61/3.52  --aig_mode                              false
% 23.61/3.52  
% 23.61/3.52  ------ Instantiation Options
% 23.61/3.52  
% 23.61/3.52  --instantiation_flag                    true
% 23.61/3.52  --inst_sos_flag                         false
% 23.61/3.52  --inst_sos_phase                        true
% 23.61/3.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.61/3.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.61/3.52  --inst_lit_sel_side                     num_symb
% 23.61/3.52  --inst_solver_per_active                1400
% 23.61/3.52  --inst_solver_calls_frac                1.
% 23.61/3.52  --inst_passive_queue_type               priority_queues
% 23.61/3.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.61/3.52  --inst_passive_queues_freq              [25;2]
% 23.61/3.52  --inst_dismatching                      true
% 23.61/3.52  --inst_eager_unprocessed_to_passive     true
% 23.61/3.52  --inst_prop_sim_given                   true
% 23.61/3.52  --inst_prop_sim_new                     false
% 23.61/3.52  --inst_subs_new                         false
% 23.61/3.52  --inst_eq_res_simp                      false
% 23.61/3.52  --inst_subs_given                       false
% 23.61/3.52  --inst_orphan_elimination               true
% 23.61/3.52  --inst_learning_loop_flag               true
% 23.61/3.52  --inst_learning_start                   3000
% 23.61/3.52  --inst_learning_factor                  2
% 23.61/3.52  --inst_start_prop_sim_after_learn       3
% 23.61/3.52  --inst_sel_renew                        solver
% 23.61/3.52  --inst_lit_activity_flag                true
% 23.61/3.52  --inst_restr_to_given                   false
% 23.61/3.52  --inst_activity_threshold               500
% 23.61/3.52  --inst_out_proof                        true
% 23.61/3.52  
% 23.61/3.52  ------ Resolution Options
% 23.61/3.52  
% 23.61/3.52  --resolution_flag                       true
% 23.61/3.52  --res_lit_sel                           adaptive
% 23.61/3.52  --res_lit_sel_side                      none
% 23.61/3.52  --res_ordering                          kbo
% 23.61/3.52  --res_to_prop_solver                    active
% 23.61/3.52  --res_prop_simpl_new                    false
% 23.61/3.52  --res_prop_simpl_given                  true
% 23.61/3.52  --res_passive_queue_type                priority_queues
% 23.61/3.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.61/3.52  --res_passive_queues_freq               [15;5]
% 23.61/3.52  --res_forward_subs                      full
% 23.61/3.52  --res_backward_subs                     full
% 23.61/3.52  --res_forward_subs_resolution           true
% 23.61/3.52  --res_backward_subs_resolution          true
% 23.61/3.52  --res_orphan_elimination                true
% 23.61/3.52  --res_time_limit                        2.
% 23.61/3.52  --res_out_proof                         true
% 23.61/3.52  
% 23.61/3.52  ------ Superposition Options
% 23.61/3.52  
% 23.61/3.52  --superposition_flag                    true
% 23.61/3.52  --sup_passive_queue_type                priority_queues
% 23.61/3.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.61/3.52  --sup_passive_queues_freq               [8;1;4]
% 23.61/3.52  --demod_completeness_check              fast
% 23.61/3.52  --demod_use_ground                      true
% 23.61/3.52  --sup_to_prop_solver                    passive
% 23.61/3.52  --sup_prop_simpl_new                    true
% 23.61/3.52  --sup_prop_simpl_given                  true
% 23.61/3.52  --sup_fun_splitting                     false
% 23.61/3.52  --sup_smt_interval                      50000
% 23.61/3.52  
% 23.61/3.52  ------ Superposition Simplification Setup
% 23.61/3.52  
% 23.61/3.52  --sup_indices_passive                   []
% 23.61/3.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.61/3.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.61/3.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.61/3.52  --sup_full_triv                         [TrivRules;PropSubs]
% 23.61/3.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.61/3.52  --sup_full_bw                           [BwDemod]
% 23.61/3.52  --sup_immed_triv                        [TrivRules]
% 23.61/3.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.61/3.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.61/3.52  --sup_immed_bw_main                     []
% 23.61/3.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.61/3.52  --sup_input_triv                        [Unflattening;TrivRules]
% 23.61/3.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.61/3.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.61/3.52  
% 23.61/3.52  ------ Combination Options
% 23.61/3.52  
% 23.61/3.52  --comb_res_mult                         3
% 23.61/3.52  --comb_sup_mult                         2
% 23.61/3.52  --comb_inst_mult                        10
% 23.61/3.52  
% 23.61/3.52  ------ Debug Options
% 23.61/3.52  
% 23.61/3.52  --dbg_backtrace                         false
% 23.61/3.52  --dbg_dump_prop_clauses                 false
% 23.61/3.52  --dbg_dump_prop_clauses_file            -
% 23.61/3.52  --dbg_out_stat                          false
% 23.61/3.52  ------ Parsing...
% 23.61/3.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.61/3.52  
% 23.61/3.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.61/3.52  
% 23.61/3.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.61/3.52  
% 23.61/3.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.61/3.52  ------ Proving...
% 23.61/3.52  ------ Problem Properties 
% 23.61/3.52  
% 23.61/3.52  
% 23.61/3.52  clauses                                 28
% 23.61/3.52  conjectures                             4
% 23.61/3.52  EPR                                     3
% 23.61/3.52  Horn                                    18
% 23.61/3.52  unary                                   11
% 23.61/3.52  binary                                  5
% 23.61/3.52  lits                                    66
% 23.61/3.52  lits eq                                 51
% 23.61/3.52  fd_pure                                 0
% 23.61/3.52  fd_pseudo                               0
% 23.61/3.52  fd_cond                                 7
% 23.61/3.52  fd_pseudo_cond                          3
% 23.61/3.52  AC symbols                              0
% 23.61/3.52  
% 23.61/3.52  ------ Schedule dynamic 5 is on 
% 23.61/3.52  
% 23.61/3.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.61/3.52  
% 23.61/3.52  
% 23.61/3.52  ------ 
% 23.61/3.52  Current options:
% 23.61/3.52  ------ 
% 23.61/3.52  
% 23.61/3.52  ------ Input Options
% 23.61/3.52  
% 23.61/3.52  --out_options                           all
% 23.61/3.52  --tptp_safe_out                         true
% 23.61/3.52  --problem_path                          ""
% 23.61/3.52  --include_path                          ""
% 23.61/3.52  --clausifier                            res/vclausify_rel
% 23.61/3.52  --clausifier_options                    --mode clausify
% 23.61/3.52  --stdin                                 false
% 23.61/3.52  --stats_out                             all
% 23.61/3.52  
% 23.61/3.52  ------ General Options
% 23.61/3.52  
% 23.61/3.52  --fof                                   false
% 23.61/3.52  --time_out_real                         305.
% 23.61/3.52  --time_out_virtual                      -1.
% 23.61/3.52  --symbol_type_check                     false
% 23.61/3.52  --clausify_out                          false
% 23.61/3.52  --sig_cnt_out                           false
% 23.61/3.52  --trig_cnt_out                          false
% 23.61/3.52  --trig_cnt_out_tolerance                1.
% 23.61/3.52  --trig_cnt_out_sk_spl                   false
% 23.61/3.52  --abstr_cl_out                          false
% 23.61/3.52  
% 23.61/3.52  ------ Global Options
% 23.61/3.52  
% 23.61/3.52  --schedule                              default
% 23.61/3.52  --add_important_lit                     false
% 23.61/3.52  --prop_solver_per_cl                    1000
% 23.61/3.52  --min_unsat_core                        false
% 23.61/3.52  --soft_assumptions                      false
% 23.61/3.52  --soft_lemma_size                       3
% 23.61/3.52  --prop_impl_unit_size                   0
% 23.61/3.52  --prop_impl_unit                        []
% 23.61/3.52  --share_sel_clauses                     true
% 23.61/3.52  --reset_solvers                         false
% 23.61/3.52  --bc_imp_inh                            [conj_cone]
% 23.61/3.52  --conj_cone_tolerance                   3.
% 23.61/3.52  --extra_neg_conj                        none
% 23.61/3.52  --large_theory_mode                     true
% 23.61/3.52  --prolific_symb_bound                   200
% 23.61/3.52  --lt_threshold                          2000
% 23.61/3.52  --clause_weak_htbl                      true
% 23.61/3.52  --gc_record_bc_elim                     false
% 23.61/3.52  
% 23.61/3.52  ------ Preprocessing Options
% 23.61/3.52  
% 23.61/3.52  --preprocessing_flag                    true
% 23.61/3.52  --time_out_prep_mult                    0.1
% 23.61/3.52  --splitting_mode                        input
% 23.61/3.52  --splitting_grd                         true
% 23.61/3.52  --splitting_cvd                         false
% 23.61/3.52  --splitting_cvd_svl                     false
% 23.61/3.52  --splitting_nvd                         32
% 23.61/3.52  --sub_typing                            true
% 23.61/3.52  --prep_gs_sim                           true
% 23.61/3.52  --prep_unflatten                        true
% 23.61/3.52  --prep_res_sim                          true
% 23.61/3.52  --prep_upred                            true
% 23.61/3.52  --prep_sem_filter                       exhaustive
% 23.61/3.52  --prep_sem_filter_out                   false
% 23.61/3.52  --pred_elim                             true
% 23.61/3.52  --res_sim_input                         true
% 23.61/3.52  --eq_ax_congr_red                       true
% 23.61/3.52  --pure_diseq_elim                       true
% 23.61/3.52  --brand_transform                       false
% 23.61/3.52  --non_eq_to_eq                          false
% 23.61/3.52  --prep_def_merge                        true
% 23.61/3.52  --prep_def_merge_prop_impl              false
% 23.61/3.52  --prep_def_merge_mbd                    true
% 23.61/3.52  --prep_def_merge_tr_red                 false
% 23.61/3.52  --prep_def_merge_tr_cl                  false
% 23.61/3.52  --smt_preprocessing                     true
% 23.61/3.52  --smt_ac_axioms                         fast
% 23.61/3.52  --preprocessed_out                      false
% 23.61/3.52  --preprocessed_stats                    false
% 23.61/3.52  
% 23.61/3.52  ------ Abstraction refinement Options
% 23.61/3.52  
% 23.61/3.52  --abstr_ref                             []
% 23.61/3.52  --abstr_ref_prep                        false
% 23.61/3.52  --abstr_ref_until_sat                   false
% 23.61/3.52  --abstr_ref_sig_restrict                funpre
% 23.61/3.52  --abstr_ref_af_restrict_to_split_sk     false
% 23.61/3.52  --abstr_ref_under                       []
% 23.61/3.52  
% 23.61/3.52  ------ SAT Options
% 23.61/3.52  
% 23.61/3.52  --sat_mode                              false
% 23.61/3.52  --sat_fm_restart_options                ""
% 23.61/3.52  --sat_gr_def                            false
% 23.61/3.52  --sat_epr_types                         true
% 23.61/3.52  --sat_non_cyclic_types                  false
% 23.61/3.52  --sat_finite_models                     false
% 23.61/3.52  --sat_fm_lemmas                         false
% 23.61/3.52  --sat_fm_prep                           false
% 23.61/3.52  --sat_fm_uc_incr                        true
% 23.61/3.52  --sat_out_model                         small
% 23.61/3.52  --sat_out_clauses                       false
% 23.61/3.52  
% 23.61/3.52  ------ QBF Options
% 23.61/3.52  
% 23.61/3.52  --qbf_mode                              false
% 23.61/3.52  --qbf_elim_univ                         false
% 23.61/3.52  --qbf_dom_inst                          none
% 23.61/3.52  --qbf_dom_pre_inst                      false
% 23.61/3.52  --qbf_sk_in                             false
% 23.61/3.52  --qbf_pred_elim                         true
% 23.61/3.52  --qbf_split                             512
% 23.61/3.52  
% 23.61/3.52  ------ BMC1 Options
% 23.61/3.52  
% 23.61/3.52  --bmc1_incremental                      false
% 23.61/3.52  --bmc1_axioms                           reachable_all
% 23.61/3.52  --bmc1_min_bound                        0
% 23.61/3.52  --bmc1_max_bound                        -1
% 23.61/3.52  --bmc1_max_bound_default                -1
% 23.61/3.52  --bmc1_symbol_reachability              true
% 23.61/3.52  --bmc1_property_lemmas                  false
% 23.61/3.52  --bmc1_k_induction                      false
% 23.61/3.52  --bmc1_non_equiv_states                 false
% 23.61/3.52  --bmc1_deadlock                         false
% 23.61/3.52  --bmc1_ucm                              false
% 23.61/3.52  --bmc1_add_unsat_core                   none
% 23.61/3.52  --bmc1_unsat_core_children              false
% 23.61/3.52  --bmc1_unsat_core_extrapolate_axioms    false
% 23.61/3.52  --bmc1_out_stat                         full
% 23.61/3.52  --bmc1_ground_init                      false
% 23.61/3.52  --bmc1_pre_inst_next_state              false
% 23.61/3.52  --bmc1_pre_inst_state                   false
% 23.61/3.52  --bmc1_pre_inst_reach_state             false
% 23.61/3.52  --bmc1_out_unsat_core                   false
% 23.61/3.52  --bmc1_aig_witness_out                  false
% 23.61/3.52  --bmc1_verbose                          false
% 23.61/3.52  --bmc1_dump_clauses_tptp                false
% 23.61/3.52  --bmc1_dump_unsat_core_tptp             false
% 23.61/3.52  --bmc1_dump_file                        -
% 23.61/3.52  --bmc1_ucm_expand_uc_limit              128
% 23.61/3.52  --bmc1_ucm_n_expand_iterations          6
% 23.61/3.52  --bmc1_ucm_extend_mode                  1
% 23.61/3.52  --bmc1_ucm_init_mode                    2
% 23.61/3.52  --bmc1_ucm_cone_mode                    none
% 23.61/3.52  --bmc1_ucm_reduced_relation_type        0
% 23.61/3.52  --bmc1_ucm_relax_model                  4
% 23.61/3.52  --bmc1_ucm_full_tr_after_sat            true
% 23.61/3.52  --bmc1_ucm_expand_neg_assumptions       false
% 23.61/3.52  --bmc1_ucm_layered_model                none
% 23.61/3.52  --bmc1_ucm_max_lemma_size               10
% 23.61/3.52  
% 23.61/3.52  ------ AIG Options
% 23.61/3.52  
% 23.61/3.52  --aig_mode                              false
% 23.61/3.52  
% 23.61/3.52  ------ Instantiation Options
% 23.61/3.52  
% 23.61/3.52  --instantiation_flag                    true
% 23.61/3.52  --inst_sos_flag                         false
% 23.61/3.52  --inst_sos_phase                        true
% 23.61/3.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.61/3.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.61/3.52  --inst_lit_sel_side                     none
% 23.61/3.52  --inst_solver_per_active                1400
% 23.61/3.52  --inst_solver_calls_frac                1.
% 23.61/3.52  --inst_passive_queue_type               priority_queues
% 23.61/3.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.61/3.52  --inst_passive_queues_freq              [25;2]
% 23.61/3.52  --inst_dismatching                      true
% 23.61/3.52  --inst_eager_unprocessed_to_passive     true
% 23.61/3.52  --inst_prop_sim_given                   true
% 23.61/3.52  --inst_prop_sim_new                     false
% 23.61/3.52  --inst_subs_new                         false
% 23.61/3.52  --inst_eq_res_simp                      false
% 23.61/3.52  --inst_subs_given                       false
% 23.61/3.52  --inst_orphan_elimination               true
% 23.61/3.52  --inst_learning_loop_flag               true
% 23.61/3.52  --inst_learning_start                   3000
% 23.61/3.52  --inst_learning_factor                  2
% 23.61/3.52  --inst_start_prop_sim_after_learn       3
% 23.61/3.52  --inst_sel_renew                        solver
% 23.61/3.52  --inst_lit_activity_flag                true
% 23.61/3.52  --inst_restr_to_given                   false
% 23.61/3.52  --inst_activity_threshold               500
% 23.61/3.52  --inst_out_proof                        true
% 23.61/3.52  
% 23.61/3.52  ------ Resolution Options
% 23.61/3.52  
% 23.61/3.52  --resolution_flag                       false
% 23.61/3.52  --res_lit_sel                           adaptive
% 23.61/3.52  --res_lit_sel_side                      none
% 23.61/3.52  --res_ordering                          kbo
% 23.61/3.52  --res_to_prop_solver                    active
% 23.61/3.52  --res_prop_simpl_new                    false
% 23.61/3.52  --res_prop_simpl_given                  true
% 23.61/3.52  --res_passive_queue_type                priority_queues
% 23.61/3.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.61/3.52  --res_passive_queues_freq               [15;5]
% 23.61/3.52  --res_forward_subs                      full
% 23.61/3.52  --res_backward_subs                     full
% 23.61/3.52  --res_forward_subs_resolution           true
% 23.61/3.52  --res_backward_subs_resolution          true
% 23.61/3.52  --res_orphan_elimination                true
% 23.61/3.52  --res_time_limit                        2.
% 23.61/3.52  --res_out_proof                         true
% 23.61/3.52  
% 23.61/3.52  ------ Superposition Options
% 23.61/3.52  
% 23.61/3.52  --superposition_flag                    true
% 23.61/3.52  --sup_passive_queue_type                priority_queues
% 23.61/3.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.61/3.52  --sup_passive_queues_freq               [8;1;4]
% 23.61/3.52  --demod_completeness_check              fast
% 23.61/3.52  --demod_use_ground                      true
% 23.61/3.52  --sup_to_prop_solver                    passive
% 23.61/3.52  --sup_prop_simpl_new                    true
% 23.61/3.52  --sup_prop_simpl_given                  true
% 23.61/3.52  --sup_fun_splitting                     false
% 23.61/3.52  --sup_smt_interval                      50000
% 23.61/3.52  
% 23.61/3.52  ------ Superposition Simplification Setup
% 23.61/3.52  
% 23.61/3.52  --sup_indices_passive                   []
% 23.61/3.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.61/3.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.61/3.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.61/3.52  --sup_full_triv                         [TrivRules;PropSubs]
% 23.61/3.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.61/3.52  --sup_full_bw                           [BwDemod]
% 23.61/3.52  --sup_immed_triv                        [TrivRules]
% 23.61/3.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.61/3.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.61/3.52  --sup_immed_bw_main                     []
% 23.61/3.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.61/3.52  --sup_input_triv                        [Unflattening;TrivRules]
% 23.61/3.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.61/3.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.61/3.52  
% 23.61/3.52  ------ Combination Options
% 23.61/3.52  
% 23.61/3.52  --comb_res_mult                         3
% 23.61/3.52  --comb_sup_mult                         2
% 23.61/3.52  --comb_inst_mult                        10
% 23.61/3.52  
% 23.61/3.52  ------ Debug Options
% 23.61/3.52  
% 23.61/3.52  --dbg_backtrace                         false
% 23.61/3.52  --dbg_dump_prop_clauses                 false
% 23.61/3.52  --dbg_dump_prop_clauses_file            -
% 23.61/3.52  --dbg_out_stat                          false
% 23.61/3.52  
% 23.61/3.52  
% 23.61/3.52  
% 23.61/3.52  
% 23.61/3.52  ------ Proving...
% 23.61/3.52  
% 23.61/3.52  
% 23.61/3.52  % SZS status Theorem for theBenchmark.p
% 23.61/3.52  
% 23.61/3.52  % SZS output start CNFRefutation for theBenchmark.p
% 23.61/3.52  
% 23.61/3.52  fof(f13,axiom,(
% 23.61/3.52    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f20,plain,(
% 23.61/3.52    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 23.61/3.52    inference(ennf_transformation,[],[f13])).
% 23.61/3.52  
% 23.61/3.52  fof(f59,plain,(
% 23.61/3.52    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f20])).
% 23.61/3.52  
% 23.61/3.52  fof(f9,axiom,(
% 23.61/3.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f52,plain,(
% 23.61/3.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 23.61/3.52    inference(cnf_transformation,[],[f9])).
% 23.61/3.52  
% 23.61/3.52  fof(f10,axiom,(
% 23.61/3.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f53,plain,(
% 23.61/3.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 23.61/3.52    inference(cnf_transformation,[],[f10])).
% 23.61/3.52  
% 23.61/3.52  fof(f85,plain,(
% 23.61/3.52    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(definition_unfolding,[],[f59,f52,f53])).
% 23.61/3.52  
% 23.61/3.52  fof(f16,conjecture,(
% 23.61/3.52    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f17,negated_conjecture,(
% 23.61/3.52    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 23.61/3.52    inference(negated_conjecture,[],[f16])).
% 23.61/3.52  
% 23.61/3.52  fof(f22,plain,(
% 23.61/3.52    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 23.61/3.52    inference(ennf_transformation,[],[f17])).
% 23.61/3.52  
% 23.61/3.52  fof(f34,plain,(
% 23.61/3.52    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK5) = sK5 | k6_mcart_1(X0,X1,X2,sK5) = sK5 | k5_mcart_1(X0,X1,X2,sK5) = sK5) & m1_subset_1(sK5,k3_zfmisc_1(X0,X1,X2)))) )),
% 23.61/3.52    introduced(choice_axiom,[])).
% 23.61/3.52  
% 23.61/3.52  fof(f33,plain,(
% 23.61/3.52    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK2,sK3,sK4,X3) = X3 | k6_mcart_1(sK2,sK3,sK4,X3) = X3 | k5_mcart_1(sK2,sK3,sK4,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2)),
% 23.61/3.52    introduced(choice_axiom,[])).
% 23.61/3.52  
% 23.61/3.52  fof(f35,plain,(
% 23.61/3.52    ((k7_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5) & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2),
% 23.61/3.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f34,f33])).
% 23.61/3.52  
% 23.61/3.52  fof(f68,plain,(
% 23.61/3.52    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))),
% 23.61/3.52    inference(cnf_transformation,[],[f35])).
% 23.61/3.52  
% 23.61/3.52  fof(f89,plain,(
% 23.61/3.52    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 23.61/3.52    inference(definition_unfolding,[],[f68,f53])).
% 23.61/3.52  
% 23.61/3.52  fof(f65,plain,(
% 23.61/3.52    k1_xboole_0 != sK2),
% 23.61/3.52    inference(cnf_transformation,[],[f35])).
% 23.61/3.52  
% 23.61/3.52  fof(f66,plain,(
% 23.61/3.52    k1_xboole_0 != sK3),
% 23.61/3.52    inference(cnf_transformation,[],[f35])).
% 23.61/3.52  
% 23.61/3.52  fof(f67,plain,(
% 23.61/3.52    k1_xboole_0 != sK4),
% 23.61/3.52    inference(cnf_transformation,[],[f35])).
% 23.61/3.52  
% 23.61/3.52  fof(f4,axiom,(
% 23.61/3.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f23,plain,(
% 23.61/3.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.61/3.52    inference(nnf_transformation,[],[f4])).
% 23.61/3.52  
% 23.61/3.52  fof(f24,plain,(
% 23.61/3.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.61/3.52    inference(flattening,[],[f23])).
% 23.61/3.52  
% 23.61/3.52  fof(f25,plain,(
% 23.61/3.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.61/3.52    inference(rectify,[],[f24])).
% 23.61/3.52  
% 23.61/3.52  fof(f26,plain,(
% 23.61/3.52    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.61/3.52    introduced(choice_axiom,[])).
% 23.61/3.52  
% 23.61/3.52  fof(f27,plain,(
% 23.61/3.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.61/3.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 23.61/3.52  
% 23.61/3.52  fof(f39,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 23.61/3.52    inference(cnf_transformation,[],[f27])).
% 23.61/3.52  
% 23.61/3.52  fof(f6,axiom,(
% 23.61/3.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f46,plain,(
% 23.61/3.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.61/3.52    inference(cnf_transformation,[],[f6])).
% 23.61/3.52  
% 23.61/3.52  fof(f77,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 23.61/3.52    inference(definition_unfolding,[],[f39,f46])).
% 23.61/3.52  
% 23.61/3.52  fof(f94,plain,(
% 23.61/3.52    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 23.61/3.52    inference(equality_resolution,[],[f77])).
% 23.61/3.52  
% 23.61/3.52  fof(f40,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 23.61/3.52    inference(cnf_transformation,[],[f27])).
% 23.61/3.52  
% 23.61/3.52  fof(f76,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 23.61/3.52    inference(definition_unfolding,[],[f40,f46])).
% 23.61/3.52  
% 23.61/3.52  fof(f92,plain,(
% 23.61/3.52    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 23.61/3.52    inference(equality_resolution,[],[f76])).
% 23.61/3.52  
% 23.61/3.52  fof(f93,plain,(
% 23.61/3.52    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 23.61/3.52    inference(equality_resolution,[],[f92])).
% 23.61/3.52  
% 23.61/3.52  fof(f14,axiom,(
% 23.61/3.52    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f21,plain,(
% 23.61/3.52    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 23.61/3.52    inference(ennf_transformation,[],[f14])).
% 23.61/3.52  
% 23.61/3.52  fof(f62,plain,(
% 23.61/3.52    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f21])).
% 23.61/3.52  
% 23.61/3.52  fof(f86,plain,(
% 23.61/3.52    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(definition_unfolding,[],[f62,f53])).
% 23.61/3.52  
% 23.61/3.52  fof(f60,plain,(
% 23.61/3.52    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f21])).
% 23.61/3.52  
% 23.61/3.52  fof(f88,plain,(
% 23.61/3.52    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(definition_unfolding,[],[f60,f53])).
% 23.61/3.52  
% 23.61/3.52  fof(f61,plain,(
% 23.61/3.52    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f21])).
% 23.61/3.52  
% 23.61/3.52  fof(f87,plain,(
% 23.61/3.52    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(definition_unfolding,[],[f61,f53])).
% 23.61/3.52  
% 23.61/3.52  fof(f15,axiom,(
% 23.61/3.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f63,plain,(
% 23.61/3.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f15])).
% 23.61/3.52  
% 23.61/3.52  fof(f41,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 23.61/3.52    inference(cnf_transformation,[],[f27])).
% 23.61/3.52  
% 23.61/3.52  fof(f75,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 23.61/3.52    inference(definition_unfolding,[],[f41,f46])).
% 23.61/3.52  
% 23.61/3.52  fof(f90,plain,(
% 23.61/3.52    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 23.61/3.52    inference(equality_resolution,[],[f75])).
% 23.61/3.52  
% 23.61/3.52  fof(f91,plain,(
% 23.61/3.52    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 23.61/3.52    inference(equality_resolution,[],[f90])).
% 23.61/3.52  
% 23.61/3.52  fof(f12,axiom,(
% 23.61/3.52    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f19,plain,(
% 23.61/3.52    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 23.61/3.52    inference(ennf_transformation,[],[f12])).
% 23.61/3.52  
% 23.61/3.52  fof(f31,plain,(
% 23.61/3.52    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 23.61/3.52    introduced(choice_axiom,[])).
% 23.61/3.52  
% 23.61/3.52  fof(f32,plain,(
% 23.61/3.52    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 23.61/3.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f31])).
% 23.61/3.52  
% 23.61/3.52  fof(f56,plain,(
% 23.61/3.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f32])).
% 23.61/3.52  
% 23.61/3.52  fof(f1,axiom,(
% 23.61/3.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f36,plain,(
% 23.61/3.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 23.61/3.52    inference(cnf_transformation,[],[f1])).
% 23.61/3.52  
% 23.61/3.52  fof(f3,axiom,(
% 23.61/3.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f38,plain,(
% 23.61/3.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.61/3.52    inference(cnf_transformation,[],[f3])).
% 23.61/3.52  
% 23.61/3.52  fof(f71,plain,(
% 23.61/3.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 23.61/3.52    inference(definition_unfolding,[],[f36,f38])).
% 23.61/3.52  
% 23.61/3.52  fof(f2,axiom,(
% 23.61/3.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f37,plain,(
% 23.61/3.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f2])).
% 23.61/3.52  
% 23.61/3.52  fof(f8,axiom,(
% 23.61/3.52    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f29,plain,(
% 23.61/3.52    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 23.61/3.52    inference(nnf_transformation,[],[f8])).
% 23.61/3.52  
% 23.61/3.52  fof(f30,plain,(
% 23.61/3.52    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 23.61/3.52    inference(flattening,[],[f29])).
% 23.61/3.52  
% 23.61/3.52  fof(f49,plain,(
% 23.61/3.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 23.61/3.52    inference(cnf_transformation,[],[f30])).
% 23.61/3.52  
% 23.61/3.52  fof(f82,plain,(
% 23.61/3.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)) )),
% 23.61/3.52    inference(definition_unfolding,[],[f49,f46,f46])).
% 23.61/3.52  
% 23.61/3.52  fof(f58,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f32])).
% 23.61/3.52  
% 23.61/3.52  fof(f83,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(definition_unfolding,[],[f58,f52])).
% 23.61/3.52  
% 23.61/3.52  fof(f7,axiom,(
% 23.61/3.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f28,plain,(
% 23.61/3.52    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 23.61/3.52    inference(nnf_transformation,[],[f7])).
% 23.61/3.52  
% 23.61/3.52  fof(f48,plain,(
% 23.61/3.52    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 23.61/3.52    inference(cnf_transformation,[],[f28])).
% 23.61/3.52  
% 23.61/3.52  fof(f5,axiom,(
% 23.61/3.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f45,plain,(
% 23.61/3.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.61/3.52    inference(cnf_transformation,[],[f5])).
% 23.61/3.52  
% 23.61/3.52  fof(f70,plain,(
% 23.61/3.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 23.61/3.52    inference(definition_unfolding,[],[f45,f46])).
% 23.61/3.52  
% 23.61/3.52  fof(f78,plain,(
% 23.61/3.52    ( ! [X0,X1] : (k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 23.61/3.52    inference(definition_unfolding,[],[f48,f70])).
% 23.61/3.52  
% 23.61/3.52  fof(f47,plain,(
% 23.61/3.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f28])).
% 23.61/3.52  
% 23.61/3.52  fof(f79,plain,(
% 23.61/3.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0) )),
% 23.61/3.52    inference(definition_unfolding,[],[f47,f70])).
% 23.61/3.52  
% 23.61/3.52  fof(f69,plain,(
% 23.61/3.52    k7_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5),
% 23.61/3.52    inference(cnf_transformation,[],[f35])).
% 23.61/3.52  
% 23.61/3.52  fof(f11,axiom,(
% 23.61/3.52    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 23.61/3.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.61/3.52  
% 23.61/3.52  fof(f18,plain,(
% 23.61/3.52    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 23.61/3.52    inference(ennf_transformation,[],[f11])).
% 23.61/3.52  
% 23.61/3.52  fof(f55,plain,(
% 23.61/3.52    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f18])).
% 23.61/3.52  
% 23.61/3.52  fof(f95,plain,(
% 23.61/3.52    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 23.61/3.52    inference(equality_resolution,[],[f55])).
% 23.61/3.52  
% 23.61/3.52  fof(f64,plain,(
% 23.61/3.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 23.61/3.52    inference(cnf_transformation,[],[f15])).
% 23.61/3.52  
% 23.61/3.52  fof(f57,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(cnf_transformation,[],[f32])).
% 23.61/3.52  
% 23.61/3.52  fof(f84,plain,(
% 23.61/3.52    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 23.61/3.52    inference(definition_unfolding,[],[f57,f52])).
% 23.61/3.52  
% 23.61/3.52  cnf(c_18,plain,
% 23.61/3.52      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 23.61/3.52      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2
% 23.61/3.52      | k1_xboole_0 = X3 ),
% 23.61/3.52      inference(cnf_transformation,[],[f85]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_25,negated_conjecture,
% 23.61/3.52      ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 23.61/3.52      inference(cnf_transformation,[],[f89]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_338,plain,
% 23.61/3.52      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 23.61/3.52      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 23.61/3.52      | sK5 != X3
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2 ),
% 23.61/3.52      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_339,plain,
% 23.61/3.52      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 23.61/3.52      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK5),k6_mcart_1(X0,X1,X2,sK5)),k7_mcart_1(X0,X1,X2,sK5)) = sK5
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2 ),
% 23.61/3.52      inference(unflattening,[status(thm)],[c_338]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1262,plain,
% 23.61/3.52      ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5
% 23.61/3.52      | sK4 = k1_xboole_0
% 23.61/3.52      | sK3 = k1_xboole_0
% 23.61/3.52      | sK2 = k1_xboole_0 ),
% 23.61/3.52      inference(equality_resolution,[status(thm)],[c_339]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_28,negated_conjecture,
% 23.61/3.52      ( k1_xboole_0 != sK2 ),
% 23.61/3.52      inference(cnf_transformation,[],[f65]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_27,negated_conjecture,
% 23.61/3.52      ( k1_xboole_0 != sK3 ),
% 23.61/3.52      inference(cnf_transformation,[],[f66]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_26,negated_conjecture,
% 23.61/3.52      ( k1_xboole_0 != sK4 ),
% 23.61/3.52      inference(cnf_transformation,[],[f67]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_7,plain,
% 23.61/3.52      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 23.61/3.52      inference(cnf_transformation,[],[f94]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_67,plain,
% 23.61/3.52      ( ~ r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 23.61/3.52      | k1_xboole_0 = k1_xboole_0 ),
% 23.61/3.52      inference(instantiation,[status(thm)],[c_7]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_6,plain,
% 23.61/3.52      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 23.61/3.52      inference(cnf_transformation,[],[f93]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_70,plain,
% 23.61/3.52      ( r2_hidden(k1_xboole_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 23.61/3.52      inference(instantiation,[status(thm)],[c_6]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_528,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1107,plain,
% 23.61/3.52      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 23.61/3.52      inference(instantiation,[status(thm)],[c_528]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1108,plain,
% 23.61/3.52      ( sK4 != k1_xboole_0
% 23.61/3.52      | k1_xboole_0 = sK4
% 23.61/3.52      | k1_xboole_0 != k1_xboole_0 ),
% 23.61/3.52      inference(instantiation,[status(thm)],[c_1107]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1109,plain,
% 23.61/3.52      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 23.61/3.52      inference(instantiation,[status(thm)],[c_528]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1110,plain,
% 23.61/3.52      ( sK3 != k1_xboole_0
% 23.61/3.52      | k1_xboole_0 = sK3
% 23.61/3.52      | k1_xboole_0 != k1_xboole_0 ),
% 23.61/3.52      inference(instantiation,[status(thm)],[c_1109]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1111,plain,
% 23.61/3.52      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 23.61/3.52      inference(instantiation,[status(thm)],[c_528]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1112,plain,
% 23.61/3.52      ( sK2 != k1_xboole_0
% 23.61/3.52      | k1_xboole_0 = sK2
% 23.61/3.52      | k1_xboole_0 != k1_xboole_0 ),
% 23.61/3.52      inference(instantiation,[status(thm)],[c_1111]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1617,plain,
% 23.61/3.52      ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5 ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_1262,c_28,c_27,c_26,c_67,c_70,c_1108,c_1110,c_1112]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_19,plain,
% 23.61/3.52      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 23.61/3.52      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2
% 23.61/3.52      | k1_xboole_0 = X3 ),
% 23.61/3.52      inference(cnf_transformation,[],[f86]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_320,plain,
% 23.61/3.52      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 23.61/3.52      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 23.61/3.52      | sK5 != X3
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2 ),
% 23.61/3.52      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_321,plain,
% 23.61/3.52      ( k7_mcart_1(X0,X1,X2,sK5) = k2_mcart_1(sK5)
% 23.61/3.52      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2 ),
% 23.61/3.52      inference(unflattening,[status(thm)],[c_320]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1174,plain,
% 23.61/3.52      ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)
% 23.61/3.52      | sK4 = k1_xboole_0
% 23.61/3.52      | sK3 = k1_xboole_0
% 23.61/3.52      | sK2 = k1_xboole_0 ),
% 23.61/3.52      inference(equality_resolution,[status(thm)],[c_321]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1451,plain,
% 23.61/3.52      ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_1174,c_28,c_27,c_26,c_67,c_70,c_1108,c_1110,c_1112]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_21,plain,
% 23.61/3.52      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 23.61/3.52      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2
% 23.61/3.52      | k1_xboole_0 = X3 ),
% 23.61/3.52      inference(cnf_transformation,[],[f88]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_284,plain,
% 23.61/3.52      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 23.61/3.52      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 23.61/3.52      | sK5 != X3
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2 ),
% 23.61/3.52      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_285,plain,
% 23.61/3.52      ( k5_mcart_1(X0,X1,X2,sK5) = k1_mcart_1(k1_mcart_1(sK5))
% 23.61/3.52      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2 ),
% 23.61/3.52      inference(unflattening,[status(thm)],[c_284]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1180,plain,
% 23.61/3.52      ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))
% 23.61/3.52      | sK4 = k1_xboole_0
% 23.61/3.52      | sK3 = k1_xboole_0
% 23.61/3.52      | sK2 = k1_xboole_0 ),
% 23.61/3.52      inference(equality_resolution,[status(thm)],[c_285]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1586,plain,
% 23.61/3.52      ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_1180,c_28,c_27,c_26,c_67,c_70,c_1108,c_1110,c_1112]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_20,plain,
% 23.61/3.52      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 23.61/3.52      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2
% 23.61/3.52      | k1_xboole_0 = X3 ),
% 23.61/3.52      inference(cnf_transformation,[],[f87]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_302,plain,
% 23.61/3.52      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 23.61/3.52      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 23.61/3.52      | sK5 != X3
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2 ),
% 23.61/3.52      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_303,plain,
% 23.61/3.52      ( k6_mcart_1(X0,X1,X2,sK5) = k2_mcart_1(k1_mcart_1(sK5))
% 23.61/3.52      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | k1_xboole_0 = X2 ),
% 23.61/3.52      inference(unflattening,[status(thm)],[c_302]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1256,plain,
% 23.61/3.52      ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))
% 23.61/3.52      | sK4 = k1_xboole_0
% 23.61/3.52      | sK3 = k1_xboole_0
% 23.61/3.52      | sK2 = k1_xboole_0 ),
% 23.61/3.52      inference(equality_resolution,[status(thm)],[c_303]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1611,plain,
% 23.61/3.52      ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_1256,c_28,c_27,c_26,c_67,c_70,c_1108,c_1110,c_1112]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1619,plain,
% 23.61/3.52      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5 ),
% 23.61/3.52      inference(light_normalisation,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_1617,c_1451,c_1586,c_1611]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_23,plain,
% 23.61/3.52      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 23.61/3.52      inference(cnf_transformation,[],[f63]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1621,plain,
% 23.61/3.52      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1619,c_23]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1657,plain,
% 23.61/3.52      ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5 ),
% 23.61/3.52      inference(demodulation,[status(thm)],[c_1621,c_1619]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_5,plain,
% 23.61/3.52      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 23.61/3.52      inference(cnf_transformation,[],[f91]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_913,plain,
% 23.61/3.52      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_17,plain,
% 23.61/3.52      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 23.61/3.52      inference(cnf_transformation,[],[f56]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_903,plain,
% 23.61/3.52      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_911,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | X0 = X2
% 23.61/3.52      | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_2413,plain,
% 23.61/3.52      ( k1_enumset1(X0,X0,X1) = k1_xboole_0
% 23.61/3.52      | sK1(k1_enumset1(X0,X0,X1)) = X0
% 23.61/3.52      | sK1(k1_enumset1(X0,X0,X1)) = X1 ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_903,c_911]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_69,plain,
% 23.61/3.52      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_0,plain,
% 23.61/3.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 23.61/3.52      inference(cnf_transformation,[],[f71]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1,plain,
% 23.61/3.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.61/3.52      inference(cnf_transformation,[],[f37]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_929,plain,
% 23.61/3.52      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.61/3.52      inference(light_normalisation,[status(thm)],[c_0,c_1]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_12,plain,
% 23.61/3.52      ( ~ r2_hidden(X0,X1)
% 23.61/3.52      | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) != k1_enumset1(X0,X0,X2) ),
% 23.61/3.52      inference(cnf_transformation,[],[f82]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_906,plain,
% 23.61/3.52      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) != k1_enumset1(X0,X0,X1)
% 23.61/3.52      | r2_hidden(X0,X2) != iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_2592,plain,
% 23.61/3.52      ( k1_enumset1(X0,X0,X1) != k1_xboole_0
% 23.61/3.52      | r2_hidden(X0,k1_enumset1(X0,X0,X1)) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_929,c_906]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_3702,plain,
% 23.61/3.52      ( sK1(k1_enumset1(X0,X0,X1)) = X0
% 23.61/3.52      | sK1(k1_enumset1(X0,X0,X1)) = X1 ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_2413,c_69,c_2592]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_15,plain,
% 23.61/3.52      ( ~ r2_hidden(X0,X1)
% 23.61/3.52      | k4_tarski(k4_tarski(X2,X0),X3) != sK1(X1)
% 23.61/3.52      | k1_xboole_0 = X1 ),
% 23.61/3.52      inference(cnf_transformation,[],[f83]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_905,plain,
% 23.61/3.52      ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
% 23.61/3.52      | k1_xboole_0 = X3
% 23.61/3.52      | r2_hidden(X1,X3) != iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_2302,plain,
% 23.61/3.52      ( k4_tarski(k1_mcart_1(sK5),X0) != sK1(X1)
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),X1) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1621,c_905]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_2471,plain,
% 23.61/3.52      ( sK1(X0) != sK5
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),X0) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1657,c_2302]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_3729,plain,
% 23.61/3.52      ( k1_enumset1(X0,X0,X1) = k1_xboole_0
% 23.61/3.52      | sK1(k1_enumset1(X0,X0,X1)) = X1
% 23.61/3.52      | sK5 != X0
% 23.61/3.52      | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,X1)) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_3702,c_2471]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_4318,plain,
% 23.61/3.52      ( sK1(k1_enumset1(X0,X0,X1)) = X1
% 23.61/3.52      | sK5 != X0
% 23.61/3.52      | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(X0,X0,X1)) != iProver_top ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_3729,c_69,c_2592]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_4325,plain,
% 23.61/3.52      ( sK1(k1_enumset1(sK5,sK5,X0)) = X0
% 23.61/3.52      | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(sK5,sK5,X0)) != iProver_top ),
% 23.61/3.52      inference(equality_resolution,[status(thm)],[c_4318]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_69039,plain,
% 23.61/3.52      ( sK1(k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5)))) = k2_mcart_1(k1_mcart_1(sK5)) ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_913,c_4325]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_69190,plain,
% 23.61/3.52      ( k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5))) = k1_xboole_0
% 23.61/3.52      | k4_tarski(k4_tarski(X0,X1),X2) != k2_mcart_1(k1_mcart_1(sK5))
% 23.61/3.52      | r2_hidden(X1,k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5)))) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_69039,c_905]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_2934,plain,
% 23.61/3.52      ( k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_2592,c_69]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_136681,plain,
% 23.61/3.52      ( k4_tarski(k4_tarski(X0,X1),X2) != k2_mcart_1(k1_mcart_1(sK5))
% 23.61/3.52      | r2_hidden(X1,k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5)))) != iProver_top ),
% 23.61/3.52      inference(forward_subsumption_resolution,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_69190,c_2934]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_136714,plain,
% 23.61/3.52      ( k4_tarski(k1_mcart_1(sK5),X0) != k2_mcart_1(k1_mcart_1(sK5))
% 23.61/3.52      | r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),k1_enumset1(sK5,sK5,k2_mcart_1(k1_mcart_1(sK5)))) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1621,c_136681]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_136777,plain,
% 23.61/3.52      ( k4_tarski(k1_mcart_1(sK5),X0) != k2_mcart_1(k1_mcart_1(sK5)) ),
% 23.61/3.52      inference(forward_subsumption_resolution,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_136714,c_913]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_136793,plain,
% 23.61/3.52      ( k2_mcart_1(k1_mcart_1(sK5)) != sK5 ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1657,c_136777]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_8,plain,
% 23.61/3.52      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k1_enumset1(X0,X0,X0)) = X1 ),
% 23.61/3.52      inference(cnf_transformation,[],[f78]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_910,plain,
% 23.61/3.52      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0
% 23.61/3.52      | r2_hidden(X1,X0) = iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_2412,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | X0 = X2
% 23.61/3.52      | k4_xboole_0(k1_enumset1(X2,X2,X1),k1_enumset1(X0,X0,X0)) = k1_enumset1(X2,X2,X1) ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_910,c_911]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_4143,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | X0 = X2
% 23.61/3.52      | r2_hidden(X2,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_2412,c_906]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_4197,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | k1_enumset1(X1,X1,X1) = k1_xboole_0
% 23.61/3.52      | sK1(k1_enumset1(X1,X1,X1)) = X1 ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_903,c_4143]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_9,plain,
% 23.61/3.52      ( ~ r2_hidden(X0,X1)
% 23.61/3.52      | k4_xboole_0(X1,k1_enumset1(X0,X0,X0)) != X1 ),
% 23.61/3.52      inference(cnf_transformation,[],[f79]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_909,plain,
% 23.61/3.52      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0
% 23.61/3.52      | r2_hidden(X1,X0) != iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_2375,plain,
% 23.61/3.52      ( k1_enumset1(X0,X0,X0) != k1_xboole_0
% 23.61/3.52      | r2_hidden(X0,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_929,c_909]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_912,plain,
% 23.61/3.52      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_2931,plain,
% 23.61/3.52      ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
% 23.61/3.52      inference(forward_subsumption_resolution,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_2375,c_912]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_4619,plain,
% 23.61/3.52      ( X0 = X1 | sK1(k1_enumset1(X0,X0,X0)) = X0 ),
% 23.61/3.52      inference(forward_subsumption_resolution,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_4197,c_2931]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_24,negated_conjecture,
% 23.61/3.52      ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 23.61/3.52      | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 23.61/3.52      | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
% 23.61/3.52      inference(cnf_transformation,[],[f69]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1454,plain,
% 23.61/3.52      ( k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 23.61/3.52      | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 23.61/3.52      | k2_mcart_1(sK5) = sK5 ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_24,c_1451]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1614,plain,
% 23.61/3.52      ( k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | k2_mcart_1(sK5) = sK5 ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1454,c_1611]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1616,plain,
% 23.61/3.52      ( k1_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | k2_mcart_1(sK5) = sK5 ),
% 23.61/3.52      inference(demodulation,[status(thm)],[c_1614,c_1586]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1658,plain,
% 23.61/3.52      ( k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5)
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | k2_mcart_1(sK5) = sK5 ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1616,c_1621]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_13,plain,
% 23.61/3.52      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 23.61/3.52      inference(cnf_transformation,[],[f95]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_22,plain,
% 23.61/3.52      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 23.61/3.52      inference(cnf_transformation,[],[f64]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_939,plain,
% 23.61/3.52      ( k4_tarski(X0,X1) != X1 ),
% 23.61/3.52      inference(light_normalisation,[status(thm)],[c_13,c_22]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1743,plain,
% 23.61/3.52      ( k2_mcart_1(sK5) != sK5 ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1657,c_939]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1864,plain,
% 23.61/3.52      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_1658,c_1743]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1865,plain,
% 23.61/3.52      ( k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5)
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
% 23.61/3.52      inference(renaming,[status(thm)],[c_1864]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_16,plain,
% 23.61/3.52      ( ~ r2_hidden(X0,X1)
% 23.61/3.52      | k4_tarski(k4_tarski(X0,X2),X3) != sK1(X1)
% 23.61/3.52      | k1_xboole_0 = X1 ),
% 23.61/3.52      inference(cnf_transformation,[],[f84]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_904,plain,
% 23.61/3.52      ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
% 23.61/3.52      | k1_xboole_0 = X3
% 23.61/3.52      | r2_hidden(X0,X3) != iProver_top ),
% 23.61/3.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1870,plain,
% 23.61/3.52      ( k4_tarski(k1_mcart_1(sK5),X0) != sK1(X1)
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | k1_xboole_0 = X1
% 23.61/3.52      | r2_hidden(sK5,X1) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1865,c_904]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_4632,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | k1_enumset1(X1,X1,X1) = k1_xboole_0
% 23.61/3.52      | k4_tarski(k1_mcart_1(sK5),X2) != X1
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | r2_hidden(sK5,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_4619,c_1870]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_102059,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | k4_tarski(k1_mcart_1(sK5),X2) != X0
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | r2_hidden(sK5,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 23.61/3.52      inference(forward_subsumption_resolution,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_4632,c_2931]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1655,plain,
% 23.61/3.52      ( k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | k2_mcart_1(sK5) = sK5 ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1616,c_1619]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1885,plain,
% 23.61/3.52      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5 ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_1655,c_1743]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1886,plain,
% 23.61/3.52      ( k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
% 23.61/3.52      inference(renaming,[status(thm)],[c_1885]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_1894,plain,
% 23.61/3.52      ( sK1(X0) != sK5
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | k1_xboole_0 = X0
% 23.61/3.52      | r2_hidden(sK5,X0) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_1886,c_904]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_4627,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | k1_enumset1(X1,X1,X1) = k1_xboole_0
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | sK5 != X1
% 23.61/3.52      | r2_hidden(sK5,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_4619,c_1894]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_4194,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | X2 = X1
% 23.61/3.52      | k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(X1,X1,X1) ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_910,c_4143]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_5260,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | X2 = X1
% 23.61/3.52      | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_4194,c_909]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_8022,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | k1_enumset1(X0,X0,X0) = k1_xboole_0
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | r2_hidden(sK5,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 23.61/3.52      inference(forward_subsumption_resolution,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_4627,c_5260]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_102061,plain,
% 23.61/3.52      ( X0 = X1
% 23.61/3.52      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 23.61/3.52      | r2_hidden(sK5,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 23.61/3.52      inference(global_propositional_subsumption,
% 23.61/3.52                [status(thm)],
% 23.61/3.52                [c_102059,c_2931,c_8022]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_102065,plain,
% 23.61/3.52      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5 | sK5 = X0 ),
% 23.61/3.52      inference(superposition,[status(thm)],[c_913,c_102061]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_102905,plain,
% 23.61/3.52      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5 | sK5 != sK5 ),
% 23.61/3.52      inference(equality_factoring,[status(thm)],[c_102065]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(c_102908,plain,
% 23.61/3.52      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
% 23.61/3.52      inference(equality_resolution_simp,[status(thm)],[c_102905]) ).
% 23.61/3.52  
% 23.61/3.52  cnf(contradiction,plain,
% 23.61/3.52      ( $false ),
% 23.61/3.52      inference(minisat,[status(thm)],[c_136793,c_102908]) ).
% 23.61/3.52  
% 23.61/3.52  
% 23.61/3.52  % SZS output end CNFRefutation for theBenchmark.p
% 23.61/3.52  
% 23.61/3.52  ------                               Statistics
% 23.61/3.52  
% 23.61/3.52  ------ General
% 23.61/3.52  
% 23.61/3.52  abstr_ref_over_cycles:                  0
% 23.61/3.52  abstr_ref_under_cycles:                 0
% 23.61/3.52  gc_basic_clause_elim:                   0
% 23.61/3.52  forced_gc_time:                         0
% 23.61/3.52  parsing_time:                           0.012
% 23.61/3.52  unif_index_cands_time:                  0.
% 23.61/3.52  unif_index_add_time:                    0.
% 23.61/3.52  orderings_time:                         0.
% 23.61/3.52  out_proof_time:                         0.014
% 23.61/3.52  total_time:                             2.762
% 23.61/3.52  num_of_symbols:                         49
% 23.61/3.52  num_of_terms:                           58363
% 23.61/3.52  
% 23.61/3.52  ------ Preprocessing
% 23.61/3.52  
% 23.61/3.52  num_of_splits:                          0
% 23.61/3.52  num_of_split_atoms:                     0
% 23.61/3.52  num_of_reused_defs:                     0
% 23.61/3.52  num_eq_ax_congr_red:                    21
% 23.61/3.52  num_of_sem_filtered_clauses:            1
% 23.61/3.52  num_of_subtypes:                        0
% 23.61/3.52  monotx_restored_types:                  0
% 23.61/3.52  sat_num_of_epr_types:                   0
% 23.61/3.52  sat_num_of_non_cyclic_types:            0
% 23.61/3.52  sat_guarded_non_collapsed_types:        0
% 23.61/3.52  num_pure_diseq_elim:                    0
% 23.61/3.52  simp_replaced_by:                       0
% 23.61/3.52  res_preprocessed:                       136
% 23.61/3.52  prep_upred:                             0
% 23.61/3.52  prep_unflattend:                        4
% 23.61/3.52  smt_new_axioms:                         0
% 23.61/3.52  pred_elim_cands:                        1
% 23.61/3.52  pred_elim:                              1
% 23.61/3.52  pred_elim_cl:                           1
% 23.61/3.52  pred_elim_cycles:                       3
% 23.61/3.52  merged_defs:                            8
% 23.61/3.52  merged_defs_ncl:                        0
% 23.61/3.52  bin_hyper_res:                          8
% 23.61/3.52  prep_cycles:                            4
% 23.61/3.52  pred_elim_time:                         0.004
% 23.61/3.52  splitting_time:                         0.
% 23.61/3.52  sem_filter_time:                        0.
% 23.61/3.52  monotx_time:                            0.001
% 23.61/3.52  subtype_inf_time:                       0.
% 23.61/3.52  
% 23.61/3.52  ------ Problem properties
% 23.61/3.52  
% 23.61/3.52  clauses:                                28
% 23.61/3.52  conjectures:                            4
% 23.61/3.52  epr:                                    3
% 23.61/3.52  horn:                                   18
% 23.61/3.52  ground:                                 4
% 23.61/3.52  unary:                                  11
% 23.61/3.52  binary:                                 5
% 23.61/3.52  lits:                                   66
% 23.61/3.52  lits_eq:                                51
% 23.61/3.52  fd_pure:                                0
% 23.61/3.52  fd_pseudo:                              0
% 23.61/3.52  fd_cond:                                7
% 23.61/3.52  fd_pseudo_cond:                         3
% 23.61/3.52  ac_symbols:                             0
% 23.61/3.52  
% 23.61/3.52  ------ Propositional Solver
% 23.61/3.52  
% 23.61/3.52  prop_solver_calls:                      30
% 23.61/3.52  prop_fast_solver_calls:                 7795
% 23.61/3.52  smt_solver_calls:                       0
% 23.61/3.52  smt_fast_solver_calls:                  0
% 23.61/3.52  prop_num_of_clauses:                    18416
% 23.61/3.52  prop_preprocess_simplified:             33034
% 23.61/3.52  prop_fo_subsumed:                       939
% 23.61/3.52  prop_solver_time:                       0.
% 23.61/3.52  smt_solver_time:                        0.
% 23.61/3.52  smt_fast_solver_time:                   0.
% 23.61/3.52  prop_fast_solver_time:                  0.
% 23.61/3.52  prop_unsat_core_time:                   0.001
% 23.61/3.52  
% 23.61/3.52  ------ QBF
% 23.61/3.52  
% 23.61/3.52  qbf_q_res:                              0
% 23.61/3.52  qbf_num_tautologies:                    0
% 23.61/3.52  qbf_prep_cycles:                        0
% 23.61/3.52  
% 23.61/3.52  ------ BMC1
% 23.61/3.52  
% 23.61/3.52  bmc1_current_bound:                     -1
% 23.61/3.52  bmc1_last_solved_bound:                 -1
% 23.61/3.52  bmc1_unsat_core_size:                   -1
% 23.61/3.52  bmc1_unsat_core_parents_size:           -1
% 23.61/3.52  bmc1_merge_next_fun:                    0
% 23.61/3.52  bmc1_unsat_core_clauses_time:           0.
% 23.61/3.52  
% 23.61/3.52  ------ Instantiation
% 23.61/3.52  
% 23.61/3.52  inst_num_of_clauses:                    4821
% 23.61/3.52  inst_num_in_passive:                    1228
% 23.61/3.52  inst_num_in_active:                     1643
% 23.61/3.52  inst_num_in_unprocessed:                1950
% 23.61/3.52  inst_num_of_loops:                      2020
% 23.61/3.52  inst_num_of_learning_restarts:          0
% 23.61/3.52  inst_num_moves_active_passive:          377
% 23.61/3.52  inst_lit_activity:                      0
% 23.61/3.52  inst_lit_activity_moves:                0
% 23.61/3.52  inst_num_tautologies:                   0
% 23.61/3.52  inst_num_prop_implied:                  0
% 23.61/3.52  inst_num_existing_simplified:           0
% 23.61/3.52  inst_num_eq_res_simplified:             0
% 23.61/3.52  inst_num_child_elim:                    0
% 23.61/3.52  inst_num_of_dismatching_blockings:      1479
% 23.61/3.52  inst_num_of_non_proper_insts:           5191
% 23.61/3.52  inst_num_of_duplicates:                 0
% 23.61/3.52  inst_inst_num_from_inst_to_res:         0
% 23.61/3.52  inst_dismatching_checking_time:         0.
% 23.61/3.52  
% 23.61/3.52  ------ Resolution
% 23.61/3.52  
% 23.61/3.52  res_num_of_clauses:                     0
% 23.61/3.52  res_num_in_passive:                     0
% 23.61/3.52  res_num_in_active:                      0
% 23.61/3.52  res_num_of_loops:                       140
% 23.61/3.52  res_forward_subset_subsumed:            206
% 23.61/3.52  res_backward_subset_subsumed:           0
% 23.61/3.52  res_forward_subsumed:                   0
% 23.61/3.52  res_backward_subsumed:                  0
% 23.61/3.52  res_forward_subsumption_resolution:     0
% 23.61/3.52  res_backward_subsumption_resolution:    0
% 23.61/3.52  res_clause_to_clause_subsumption:       101837
% 23.61/3.52  res_orphan_elimination:                 0
% 23.61/3.52  res_tautology_del:                      310
% 23.61/3.52  res_num_eq_res_simplified:              0
% 23.61/3.52  res_num_sel_changes:                    0
% 23.61/3.52  res_moves_from_active_to_pass:          0
% 23.61/3.52  
% 23.61/3.52  ------ Superposition
% 23.61/3.52  
% 23.61/3.52  sup_time_total:                         0.
% 23.61/3.52  sup_time_generating:                    0.
% 23.61/3.52  sup_time_sim_full:                      0.
% 23.61/3.52  sup_time_sim_immed:                     0.
% 23.61/3.52  
% 23.61/3.52  sup_num_of_clauses:                     2885
% 23.61/3.52  sup_num_in_active:                      360
% 23.61/3.52  sup_num_in_passive:                     2525
% 23.61/3.52  sup_num_of_loops:                       403
% 23.61/3.52  sup_fw_superposition:                   11599
% 23.61/3.52  sup_bw_superposition:                   17228
% 23.61/3.52  sup_immediate_simplified:               16700
% 23.61/3.52  sup_given_eliminated:                   21
% 23.61/3.52  comparisons_done:                       0
% 23.61/3.52  comparisons_avoided:                    351
% 23.61/3.52  
% 23.61/3.52  ------ Simplifications
% 23.61/3.52  
% 23.61/3.52  
% 23.61/3.52  sim_fw_subset_subsumed:                 6149
% 23.61/3.52  sim_bw_subset_subsumed:                 242
% 23.61/3.52  sim_fw_subsumed:                        8763
% 23.61/3.52  sim_bw_subsumed:                        1848
% 23.61/3.52  sim_fw_subsumption_res:                 959
% 23.61/3.52  sim_bw_subsumption_res:                 215
% 23.61/3.52  sim_tautology_del:                      1073
% 23.61/3.52  sim_eq_tautology_del:                   306
% 23.61/3.52  sim_eq_res_simp:                        50
% 23.61/3.52  sim_fw_demodulated:                     642
% 23.61/3.52  sim_bw_demodulated:                     5
% 23.61/3.52  sim_light_normalised:                   412
% 23.61/3.52  sim_joinable_taut:                      0
% 23.61/3.52  sim_joinable_simp:                      0
% 23.61/3.52  sim_ac_normalised:                      0
% 23.61/3.52  sim_smt_subsumption:                    0
% 23.61/3.52  
%------------------------------------------------------------------------------
