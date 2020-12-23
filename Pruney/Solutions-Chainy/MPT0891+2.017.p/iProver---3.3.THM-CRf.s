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
% DateTime   : Thu Dec  3 11:58:35 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  140 (1186 expanded)
%              Number of clauses        :   77 ( 387 expanded)
%              Number of leaves         :   16 ( 336 expanded)
%              Depth                    :   22
%              Number of atoms          :  479 (5592 expanded)
%              Number of equality atoms :  382 (4732 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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

fof(f27,plain,
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

fof(f29,plain,
    ( ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 )
    & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f28,f27])).

fof(f54,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f53,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f53,f39])).

fof(f50,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f35])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f23])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f38,f39])).

fof(f41,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f31])).

fof(f63,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f62])).

fof(f42,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f25])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_18,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_230,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_231,plain,
    ( k7_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(sK6)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_1502,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_231])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_53,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_54,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1046,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1458,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1459,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_1460,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1461,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_1462,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1463,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_1785,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1502,c_22,c_21,c_20,c_53,c_54,c_1459,c_1461,c_1463])).

cnf(c_1788,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_18,c_1785])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_212,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_213,plain,
    ( k6_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_1554,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_213])).

cnf(c_1859,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1554,c_22,c_21,c_20,c_53,c_54,c_1459,c_1461,c_1463])).

cnf(c_1862,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_1788,c_1859])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_194,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_195,plain,
    ( k5_mcart_1(X0,X1,X2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_194])).

cnf(c_1508,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_195])).

cnf(c_1829,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1508,c_22,c_21,c_20,c_53,c_54,c_1459,c_1461,c_1463])).

cnf(c_1864,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6 ),
    inference(demodulation,[status(thm)],[c_1862,c_1829])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1241,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1245,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2141,plain,
    ( sK1(k1_tarski(X0)) = X0
    | k1_tarski(X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1241,c_1245])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_248,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | sK6 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_249,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK6),k6_mcart_1(X0,X1,X2,sK6)),k7_mcart_1(X0,X1,X2,sK6)) = sK6
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_1560,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_249])).

cnf(c_1865,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_22,c_21,c_20,c_53,c_54,c_1459,c_1461,c_1463])).

cnf(c_1867,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_1865,c_1785,c_1829,c_1859])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1242,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2290,plain,
    ( sK1(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1867,c_1242])).

cnf(c_2505,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2141,c_2290])).

cnf(c_2771,plain,
    ( k1_tarski(sK6) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_tarski(sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2505])).

cnf(c_3200,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6
    | k1_tarski(sK6) = k1_xboole_0
    | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_2771])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1246,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3207,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
    | k2_mcart_1(sK6) = sK6
    | k1_tarski(sK6) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3200,c_1246])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1243,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2413,plain,
    ( sK1(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1867,c_1243])).

cnf(c_2689,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2141,c_2413])).

cnf(c_2777,plain,
    ( k1_tarski(sK6) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_tarski(sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2689])).

cnf(c_3514,plain,
    ( k2_mcart_1(sK6) = sK6
    | k1_tarski(sK6) = k1_xboole_0
    | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3207,c_2777])).

cnf(c_3791,plain,
    ( k2_mcart_1(sK6) = sK6
    | k1_tarski(sK6) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3514,c_1246])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1238,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2142,plain,
    ( sK2(k1_tarski(X0)) = X0
    | k1_tarski(X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1238,c_1245])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X2,X0) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1240,plain,
    ( k4_tarski(X0,X1) != sK2(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2215,plain,
    ( sK2(X0) != sK6
    | k1_xboole_0 = X0
    | r2_hidden(k2_mcart_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1867,c_1240])).

cnf(c_2632,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | sK6 != X0
    | r2_hidden(k2_mcart_1(sK6),k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2142,c_2215])).

cnf(c_2735,plain,
    ( k1_tarski(sK6) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK6),k1_tarski(sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2632])).

cnf(c_3794,plain,
    ( k1_tarski(sK6) = k1_xboole_0
    | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3791,c_2735])).

cnf(c_3968,plain,
    ( k1_tarski(sK6) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3794,c_1246])).

cnf(c_3976,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3968,c_1246])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1244,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1952,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1244])).

cnf(c_4087,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3976,c_1952])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:56:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.52/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/0.92  
% 2.52/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.92  
% 2.52/0.92  ------  iProver source info
% 2.52/0.92  
% 2.52/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.92  git: non_committed_changes: false
% 2.52/0.92  git: last_make_outside_of_git: false
% 2.52/0.92  
% 2.52/0.92  ------ 
% 2.52/0.92  
% 2.52/0.92  ------ Input Options
% 2.52/0.92  
% 2.52/0.92  --out_options                           all
% 2.52/0.92  --tptp_safe_out                         true
% 2.52/0.92  --problem_path                          ""
% 2.52/0.92  --include_path                          ""
% 2.52/0.92  --clausifier                            res/vclausify_rel
% 2.52/0.92  --clausifier_options                    --mode clausify
% 2.52/0.92  --stdin                                 false
% 2.52/0.92  --stats_out                             all
% 2.52/0.92  
% 2.52/0.92  ------ General Options
% 2.52/0.92  
% 2.52/0.92  --fof                                   false
% 2.52/0.92  --time_out_real                         305.
% 2.52/0.92  --time_out_virtual                      -1.
% 2.52/0.92  --symbol_type_check                     false
% 2.52/0.92  --clausify_out                          false
% 2.52/0.92  --sig_cnt_out                           false
% 2.52/0.92  --trig_cnt_out                          false
% 2.52/0.92  --trig_cnt_out_tolerance                1.
% 2.52/0.92  --trig_cnt_out_sk_spl                   false
% 2.52/0.92  --abstr_cl_out                          false
% 2.52/0.92  
% 2.52/0.92  ------ Global Options
% 2.52/0.92  
% 2.52/0.92  --schedule                              default
% 2.52/0.92  --add_important_lit                     false
% 2.52/0.92  --prop_solver_per_cl                    1000
% 2.52/0.92  --min_unsat_core                        false
% 2.52/0.92  --soft_assumptions                      false
% 2.52/0.92  --soft_lemma_size                       3
% 2.52/0.92  --prop_impl_unit_size                   0
% 2.52/0.92  --prop_impl_unit                        []
% 2.52/0.92  --share_sel_clauses                     true
% 2.52/0.92  --reset_solvers                         false
% 2.52/0.92  --bc_imp_inh                            [conj_cone]
% 2.52/0.92  --conj_cone_tolerance                   3.
% 2.52/0.92  --extra_neg_conj                        none
% 2.52/0.92  --large_theory_mode                     true
% 2.52/0.92  --prolific_symb_bound                   200
% 2.52/0.92  --lt_threshold                          2000
% 2.52/0.92  --clause_weak_htbl                      true
% 2.52/0.92  --gc_record_bc_elim                     false
% 2.52/0.92  
% 2.52/0.92  ------ Preprocessing Options
% 2.52/0.92  
% 2.52/0.92  --preprocessing_flag                    true
% 2.52/0.92  --time_out_prep_mult                    0.1
% 2.52/0.92  --splitting_mode                        input
% 2.52/0.92  --splitting_grd                         true
% 2.52/0.92  --splitting_cvd                         false
% 2.52/0.92  --splitting_cvd_svl                     false
% 2.52/0.92  --splitting_nvd                         32
% 2.52/0.92  --sub_typing                            true
% 2.52/0.92  --prep_gs_sim                           true
% 2.52/0.92  --prep_unflatten                        true
% 2.52/0.92  --prep_res_sim                          true
% 2.52/0.92  --prep_upred                            true
% 2.52/0.92  --prep_sem_filter                       exhaustive
% 2.52/0.92  --prep_sem_filter_out                   false
% 2.52/0.92  --pred_elim                             true
% 2.52/0.92  --res_sim_input                         true
% 2.52/0.92  --eq_ax_congr_red                       true
% 2.52/0.92  --pure_diseq_elim                       true
% 2.52/0.92  --brand_transform                       false
% 2.52/0.92  --non_eq_to_eq                          false
% 2.52/0.92  --prep_def_merge                        true
% 2.52/0.92  --prep_def_merge_prop_impl              false
% 2.52/0.92  --prep_def_merge_mbd                    true
% 2.52/0.92  --prep_def_merge_tr_red                 false
% 2.52/0.92  --prep_def_merge_tr_cl                  false
% 2.52/0.92  --smt_preprocessing                     true
% 2.52/0.92  --smt_ac_axioms                         fast
% 2.52/0.92  --preprocessed_out                      false
% 2.52/0.92  --preprocessed_stats                    false
% 2.52/0.92  
% 2.52/0.92  ------ Abstraction refinement Options
% 2.52/0.92  
% 2.52/0.92  --abstr_ref                             []
% 2.52/0.92  --abstr_ref_prep                        false
% 2.52/0.92  --abstr_ref_until_sat                   false
% 2.52/0.92  --abstr_ref_sig_restrict                funpre
% 2.52/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.92  --abstr_ref_under                       []
% 2.52/0.92  
% 2.52/0.92  ------ SAT Options
% 2.52/0.92  
% 2.52/0.92  --sat_mode                              false
% 2.52/0.92  --sat_fm_restart_options                ""
% 2.52/0.92  --sat_gr_def                            false
% 2.52/0.92  --sat_epr_types                         true
% 2.52/0.92  --sat_non_cyclic_types                  false
% 2.52/0.92  --sat_finite_models                     false
% 2.52/0.92  --sat_fm_lemmas                         false
% 2.52/0.92  --sat_fm_prep                           false
% 2.52/0.92  --sat_fm_uc_incr                        true
% 2.52/0.92  --sat_out_model                         small
% 2.52/0.92  --sat_out_clauses                       false
% 2.52/0.92  
% 2.52/0.92  ------ QBF Options
% 2.52/0.92  
% 2.52/0.92  --qbf_mode                              false
% 2.52/0.92  --qbf_elim_univ                         false
% 2.52/0.92  --qbf_dom_inst                          none
% 2.52/0.92  --qbf_dom_pre_inst                      false
% 2.52/0.92  --qbf_sk_in                             false
% 2.52/0.92  --qbf_pred_elim                         true
% 2.52/0.92  --qbf_split                             512
% 2.52/0.92  
% 2.52/0.92  ------ BMC1 Options
% 2.52/0.92  
% 2.52/0.92  --bmc1_incremental                      false
% 2.52/0.92  --bmc1_axioms                           reachable_all
% 2.52/0.92  --bmc1_min_bound                        0
% 2.52/0.92  --bmc1_max_bound                        -1
% 2.52/0.92  --bmc1_max_bound_default                -1
% 2.52/0.92  --bmc1_symbol_reachability              true
% 2.52/0.92  --bmc1_property_lemmas                  false
% 2.52/0.92  --bmc1_k_induction                      false
% 2.52/0.92  --bmc1_non_equiv_states                 false
% 2.52/0.92  --bmc1_deadlock                         false
% 2.52/0.92  --bmc1_ucm                              false
% 2.52/0.92  --bmc1_add_unsat_core                   none
% 2.52/0.92  --bmc1_unsat_core_children              false
% 2.52/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.92  --bmc1_out_stat                         full
% 2.52/0.92  --bmc1_ground_init                      false
% 2.52/0.92  --bmc1_pre_inst_next_state              false
% 2.52/0.92  --bmc1_pre_inst_state                   false
% 2.52/0.92  --bmc1_pre_inst_reach_state             false
% 2.52/0.92  --bmc1_out_unsat_core                   false
% 2.52/0.92  --bmc1_aig_witness_out                  false
% 2.52/0.92  --bmc1_verbose                          false
% 2.52/0.92  --bmc1_dump_clauses_tptp                false
% 2.52/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.92  --bmc1_dump_file                        -
% 2.52/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.92  --bmc1_ucm_extend_mode                  1
% 2.52/0.92  --bmc1_ucm_init_mode                    2
% 2.52/0.92  --bmc1_ucm_cone_mode                    none
% 2.52/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.92  --bmc1_ucm_relax_model                  4
% 2.52/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.92  --bmc1_ucm_layered_model                none
% 2.52/0.92  --bmc1_ucm_max_lemma_size               10
% 2.52/0.92  
% 2.52/0.92  ------ AIG Options
% 2.52/0.92  
% 2.52/0.92  --aig_mode                              false
% 2.52/0.92  
% 2.52/0.92  ------ Instantiation Options
% 2.52/0.92  
% 2.52/0.92  --instantiation_flag                    true
% 2.52/0.92  --inst_sos_flag                         false
% 2.52/0.92  --inst_sos_phase                        true
% 2.52/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.92  --inst_lit_sel_side                     num_symb
% 2.52/0.92  --inst_solver_per_active                1400
% 2.52/0.92  --inst_solver_calls_frac                1.
% 2.52/0.92  --inst_passive_queue_type               priority_queues
% 2.52/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.92  --inst_passive_queues_freq              [25;2]
% 2.52/0.92  --inst_dismatching                      true
% 2.52/0.92  --inst_eager_unprocessed_to_passive     true
% 2.52/0.92  --inst_prop_sim_given                   true
% 2.52/0.92  --inst_prop_sim_new                     false
% 2.52/0.92  --inst_subs_new                         false
% 2.52/0.92  --inst_eq_res_simp                      false
% 2.52/0.92  --inst_subs_given                       false
% 2.52/0.92  --inst_orphan_elimination               true
% 2.52/0.92  --inst_learning_loop_flag               true
% 2.52/0.92  --inst_learning_start                   3000
% 2.52/0.92  --inst_learning_factor                  2
% 2.52/0.92  --inst_start_prop_sim_after_learn       3
% 2.52/0.92  --inst_sel_renew                        solver
% 2.52/0.92  --inst_lit_activity_flag                true
% 2.52/0.92  --inst_restr_to_given                   false
% 2.52/0.92  --inst_activity_threshold               500
% 2.52/0.92  --inst_out_proof                        true
% 2.52/0.92  
% 2.52/0.92  ------ Resolution Options
% 2.52/0.92  
% 2.52/0.92  --resolution_flag                       true
% 2.52/0.92  --res_lit_sel                           adaptive
% 2.52/0.92  --res_lit_sel_side                      none
% 2.52/0.92  --res_ordering                          kbo
% 2.52/0.92  --res_to_prop_solver                    active
% 2.52/0.92  --res_prop_simpl_new                    false
% 2.52/0.92  --res_prop_simpl_given                  true
% 2.52/0.92  --res_passive_queue_type                priority_queues
% 2.52/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.92  --res_passive_queues_freq               [15;5]
% 2.52/0.92  --res_forward_subs                      full
% 2.52/0.92  --res_backward_subs                     full
% 2.52/0.92  --res_forward_subs_resolution           true
% 2.52/0.92  --res_backward_subs_resolution          true
% 2.52/0.92  --res_orphan_elimination                true
% 2.52/0.92  --res_time_limit                        2.
% 2.52/0.92  --res_out_proof                         true
% 2.52/0.92  
% 2.52/0.92  ------ Superposition Options
% 2.52/0.92  
% 2.52/0.92  --superposition_flag                    true
% 2.52/0.92  --sup_passive_queue_type                priority_queues
% 2.52/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.92  --demod_completeness_check              fast
% 2.52/0.92  --demod_use_ground                      true
% 2.52/0.92  --sup_to_prop_solver                    passive
% 2.52/0.92  --sup_prop_simpl_new                    true
% 2.52/0.92  --sup_prop_simpl_given                  true
% 2.52/0.92  --sup_fun_splitting                     false
% 2.52/0.92  --sup_smt_interval                      50000
% 2.52/0.92  
% 2.52/0.92  ------ Superposition Simplification Setup
% 2.52/0.92  
% 2.52/0.92  --sup_indices_passive                   []
% 2.52/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.92  --sup_full_bw                           [BwDemod]
% 2.52/0.92  --sup_immed_triv                        [TrivRules]
% 2.52/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.92  --sup_immed_bw_main                     []
% 2.52/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.92  
% 2.52/0.92  ------ Combination Options
% 2.52/0.92  
% 2.52/0.92  --comb_res_mult                         3
% 2.52/0.92  --comb_sup_mult                         2
% 2.52/0.92  --comb_inst_mult                        10
% 2.52/0.92  
% 2.52/0.92  ------ Debug Options
% 2.52/0.92  
% 2.52/0.92  --dbg_backtrace                         false
% 2.52/0.92  --dbg_dump_prop_clauses                 false
% 2.52/0.92  --dbg_dump_prop_clauses_file            -
% 2.52/0.92  --dbg_out_stat                          false
% 2.52/0.92  ------ Parsing...
% 2.52/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.92  
% 2.52/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.52/0.92  
% 2.52/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.92  
% 2.52/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/0.92  ------ Proving...
% 2.52/0.92  ------ Problem Properties 
% 2.52/0.92  
% 2.52/0.92  
% 2.52/0.92  clauses                                 22
% 2.52/0.92  conjectures                             4
% 2.52/0.92  EPR                                     3
% 2.52/0.92  Horn                                    13
% 2.52/0.92  unary                                   7
% 2.52/0.92  binary                                  3
% 2.52/0.92  lits                                    57
% 2.52/0.92  lits eq                                 46
% 2.52/0.92  fd_pure                                 0
% 2.52/0.92  fd_pseudo                               0
% 2.52/0.92  fd_cond                                 11
% 2.52/0.92  fd_pseudo_cond                          2
% 2.52/0.92  AC symbols                              0
% 2.52/0.92  
% 2.52/0.92  ------ Schedule dynamic 5 is on 
% 2.52/0.92  
% 2.52/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/0.92  
% 2.52/0.92  
% 2.52/0.92  ------ 
% 2.52/0.92  Current options:
% 2.52/0.92  ------ 
% 2.52/0.92  
% 2.52/0.92  ------ Input Options
% 2.52/0.92  
% 2.52/0.92  --out_options                           all
% 2.52/0.92  --tptp_safe_out                         true
% 2.52/0.92  --problem_path                          ""
% 2.52/0.92  --include_path                          ""
% 2.52/0.92  --clausifier                            res/vclausify_rel
% 2.52/0.92  --clausifier_options                    --mode clausify
% 2.52/0.92  --stdin                                 false
% 2.52/0.92  --stats_out                             all
% 2.52/0.92  
% 2.52/0.92  ------ General Options
% 2.52/0.92  
% 2.52/0.92  --fof                                   false
% 2.52/0.92  --time_out_real                         305.
% 2.52/0.92  --time_out_virtual                      -1.
% 2.52/0.92  --symbol_type_check                     false
% 2.52/0.92  --clausify_out                          false
% 2.52/0.92  --sig_cnt_out                           false
% 2.52/0.92  --trig_cnt_out                          false
% 2.52/0.92  --trig_cnt_out_tolerance                1.
% 2.52/0.92  --trig_cnt_out_sk_spl                   false
% 2.52/0.92  --abstr_cl_out                          false
% 2.52/0.92  
% 2.52/0.92  ------ Global Options
% 2.52/0.92  
% 2.52/0.92  --schedule                              default
% 2.52/0.92  --add_important_lit                     false
% 2.52/0.92  --prop_solver_per_cl                    1000
% 2.52/0.92  --min_unsat_core                        false
% 2.52/0.92  --soft_assumptions                      false
% 2.52/0.92  --soft_lemma_size                       3
% 2.52/0.92  --prop_impl_unit_size                   0
% 2.52/0.92  --prop_impl_unit                        []
% 2.52/0.92  --share_sel_clauses                     true
% 2.52/0.92  --reset_solvers                         false
% 2.52/0.92  --bc_imp_inh                            [conj_cone]
% 2.52/0.92  --conj_cone_tolerance                   3.
% 2.52/0.92  --extra_neg_conj                        none
% 2.52/0.92  --large_theory_mode                     true
% 2.52/0.92  --prolific_symb_bound                   200
% 2.52/0.92  --lt_threshold                          2000
% 2.52/0.92  --clause_weak_htbl                      true
% 2.52/0.92  --gc_record_bc_elim                     false
% 2.52/0.92  
% 2.52/0.92  ------ Preprocessing Options
% 2.52/0.92  
% 2.52/0.92  --preprocessing_flag                    true
% 2.52/0.92  --time_out_prep_mult                    0.1
% 2.52/0.92  --splitting_mode                        input
% 2.52/0.92  --splitting_grd                         true
% 2.52/0.92  --splitting_cvd                         false
% 2.52/0.92  --splitting_cvd_svl                     false
% 2.52/0.92  --splitting_nvd                         32
% 2.52/0.92  --sub_typing                            true
% 2.52/0.92  --prep_gs_sim                           true
% 2.52/0.92  --prep_unflatten                        true
% 2.52/0.92  --prep_res_sim                          true
% 2.52/0.92  --prep_upred                            true
% 2.52/0.92  --prep_sem_filter                       exhaustive
% 2.52/0.92  --prep_sem_filter_out                   false
% 2.52/0.92  --pred_elim                             true
% 2.52/0.92  --res_sim_input                         true
% 2.52/0.92  --eq_ax_congr_red                       true
% 2.52/0.92  --pure_diseq_elim                       true
% 2.52/0.92  --brand_transform                       false
% 2.52/0.92  --non_eq_to_eq                          false
% 2.52/0.92  --prep_def_merge                        true
% 2.52/0.92  --prep_def_merge_prop_impl              false
% 2.52/0.92  --prep_def_merge_mbd                    true
% 2.52/0.92  --prep_def_merge_tr_red                 false
% 2.52/0.92  --prep_def_merge_tr_cl                  false
% 2.52/0.92  --smt_preprocessing                     true
% 2.52/0.92  --smt_ac_axioms                         fast
% 2.52/0.92  --preprocessed_out                      false
% 2.52/0.92  --preprocessed_stats                    false
% 2.52/0.92  
% 2.52/0.92  ------ Abstraction refinement Options
% 2.52/0.92  
% 2.52/0.92  --abstr_ref                             []
% 2.52/0.92  --abstr_ref_prep                        false
% 2.52/0.92  --abstr_ref_until_sat                   false
% 2.52/0.92  --abstr_ref_sig_restrict                funpre
% 2.52/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.92  --abstr_ref_under                       []
% 2.52/0.92  
% 2.52/0.92  ------ SAT Options
% 2.52/0.92  
% 2.52/0.92  --sat_mode                              false
% 2.52/0.92  --sat_fm_restart_options                ""
% 2.52/0.92  --sat_gr_def                            false
% 2.52/0.92  --sat_epr_types                         true
% 2.52/0.92  --sat_non_cyclic_types                  false
% 2.52/0.92  --sat_finite_models                     false
% 2.52/0.92  --sat_fm_lemmas                         false
% 2.52/0.92  --sat_fm_prep                           false
% 2.52/0.92  --sat_fm_uc_incr                        true
% 2.52/0.92  --sat_out_model                         small
% 2.52/0.92  --sat_out_clauses                       false
% 2.52/0.92  
% 2.52/0.92  ------ QBF Options
% 2.52/0.92  
% 2.52/0.92  --qbf_mode                              false
% 2.52/0.92  --qbf_elim_univ                         false
% 2.52/0.92  --qbf_dom_inst                          none
% 2.52/0.92  --qbf_dom_pre_inst                      false
% 2.52/0.92  --qbf_sk_in                             false
% 2.52/0.92  --qbf_pred_elim                         true
% 2.52/0.92  --qbf_split                             512
% 2.52/0.92  
% 2.52/0.92  ------ BMC1 Options
% 2.52/0.92  
% 2.52/0.92  --bmc1_incremental                      false
% 2.52/0.92  --bmc1_axioms                           reachable_all
% 2.52/0.92  --bmc1_min_bound                        0
% 2.52/0.92  --bmc1_max_bound                        -1
% 2.52/0.92  --bmc1_max_bound_default                -1
% 2.52/0.92  --bmc1_symbol_reachability              true
% 2.52/0.92  --bmc1_property_lemmas                  false
% 2.52/0.92  --bmc1_k_induction                      false
% 2.52/0.92  --bmc1_non_equiv_states                 false
% 2.52/0.92  --bmc1_deadlock                         false
% 2.52/0.92  --bmc1_ucm                              false
% 2.52/0.92  --bmc1_add_unsat_core                   none
% 2.52/0.92  --bmc1_unsat_core_children              false
% 2.52/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.92  --bmc1_out_stat                         full
% 2.52/0.92  --bmc1_ground_init                      false
% 2.52/0.92  --bmc1_pre_inst_next_state              false
% 2.52/0.92  --bmc1_pre_inst_state                   false
% 2.52/0.92  --bmc1_pre_inst_reach_state             false
% 2.52/0.92  --bmc1_out_unsat_core                   false
% 2.52/0.92  --bmc1_aig_witness_out                  false
% 2.52/0.92  --bmc1_verbose                          false
% 2.52/0.92  --bmc1_dump_clauses_tptp                false
% 2.52/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.92  --bmc1_dump_file                        -
% 2.52/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.92  --bmc1_ucm_extend_mode                  1
% 2.52/0.92  --bmc1_ucm_init_mode                    2
% 2.52/0.92  --bmc1_ucm_cone_mode                    none
% 2.52/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.92  --bmc1_ucm_relax_model                  4
% 2.52/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.92  --bmc1_ucm_layered_model                none
% 2.52/0.92  --bmc1_ucm_max_lemma_size               10
% 2.52/0.92  
% 2.52/0.92  ------ AIG Options
% 2.52/0.92  
% 2.52/0.92  --aig_mode                              false
% 2.52/0.92  
% 2.52/0.92  ------ Instantiation Options
% 2.52/0.92  
% 2.52/0.92  --instantiation_flag                    true
% 2.52/0.92  --inst_sos_flag                         false
% 2.52/0.92  --inst_sos_phase                        true
% 2.52/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.92  --inst_lit_sel_side                     none
% 2.52/0.92  --inst_solver_per_active                1400
% 2.52/0.92  --inst_solver_calls_frac                1.
% 2.52/0.92  --inst_passive_queue_type               priority_queues
% 2.52/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.92  --inst_passive_queues_freq              [25;2]
% 2.52/0.92  --inst_dismatching                      true
% 2.52/0.92  --inst_eager_unprocessed_to_passive     true
% 2.52/0.92  --inst_prop_sim_given                   true
% 2.52/0.92  --inst_prop_sim_new                     false
% 2.52/0.92  --inst_subs_new                         false
% 2.52/0.92  --inst_eq_res_simp                      false
% 2.52/0.92  --inst_subs_given                       false
% 2.52/0.92  --inst_orphan_elimination               true
% 2.52/0.92  --inst_learning_loop_flag               true
% 2.52/0.92  --inst_learning_start                   3000
% 2.52/0.92  --inst_learning_factor                  2
% 2.52/0.92  --inst_start_prop_sim_after_learn       3
% 2.52/0.92  --inst_sel_renew                        solver
% 2.52/0.92  --inst_lit_activity_flag                true
% 2.52/0.92  --inst_restr_to_given                   false
% 2.52/0.92  --inst_activity_threshold               500
% 2.52/0.92  --inst_out_proof                        true
% 2.52/0.92  
% 2.52/0.92  ------ Resolution Options
% 2.52/0.92  
% 2.52/0.92  --resolution_flag                       false
% 2.52/0.92  --res_lit_sel                           adaptive
% 2.52/0.92  --res_lit_sel_side                      none
% 2.52/0.92  --res_ordering                          kbo
% 2.52/0.92  --res_to_prop_solver                    active
% 2.52/0.92  --res_prop_simpl_new                    false
% 2.52/0.92  --res_prop_simpl_given                  true
% 2.52/0.92  --res_passive_queue_type                priority_queues
% 2.52/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.92  --res_passive_queues_freq               [15;5]
% 2.52/0.92  --res_forward_subs                      full
% 2.52/0.92  --res_backward_subs                     full
% 2.52/0.92  --res_forward_subs_resolution           true
% 2.52/0.92  --res_backward_subs_resolution          true
% 2.52/0.92  --res_orphan_elimination                true
% 2.52/0.92  --res_time_limit                        2.
% 2.52/0.92  --res_out_proof                         true
% 2.52/0.92  
% 2.52/0.92  ------ Superposition Options
% 2.52/0.92  
% 2.52/0.92  --superposition_flag                    true
% 2.52/0.92  --sup_passive_queue_type                priority_queues
% 2.52/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.92  --demod_completeness_check              fast
% 2.52/0.92  --demod_use_ground                      true
% 2.52/0.92  --sup_to_prop_solver                    passive
% 2.52/0.92  --sup_prop_simpl_new                    true
% 2.52/0.92  --sup_prop_simpl_given                  true
% 2.52/0.92  --sup_fun_splitting                     false
% 2.52/0.92  --sup_smt_interval                      50000
% 2.52/0.92  
% 2.52/0.92  ------ Superposition Simplification Setup
% 2.52/0.92  
% 2.52/0.92  --sup_indices_passive                   []
% 2.52/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.92  --sup_full_bw                           [BwDemod]
% 2.52/0.92  --sup_immed_triv                        [TrivRules]
% 2.52/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.92  --sup_immed_bw_main                     []
% 2.52/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.92  
% 2.52/0.92  ------ Combination Options
% 2.52/0.92  
% 2.52/0.92  --comb_res_mult                         3
% 2.52/0.92  --comb_sup_mult                         2
% 2.52/0.92  --comb_inst_mult                        10
% 2.52/0.92  
% 2.52/0.92  ------ Debug Options
% 2.52/0.92  
% 2.52/0.92  --dbg_backtrace                         false
% 2.52/0.92  --dbg_dump_prop_clauses                 false
% 2.52/0.92  --dbg_dump_prop_clauses_file            -
% 2.52/0.92  --dbg_out_stat                          false
% 2.52/0.92  
% 2.52/0.92  
% 2.52/0.92  
% 2.52/0.92  
% 2.52/0.92  ------ Proving...
% 2.52/0.92  
% 2.52/0.92  
% 2.52/0.92  % SZS status Theorem for theBenchmark.p
% 2.52/0.92  
% 2.52/0.92   Resolution empty clause
% 2.52/0.92  
% 2.52/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.92  
% 2.52/0.92  fof(f10,conjecture,(
% 2.52/0.92    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f11,negated_conjecture,(
% 2.52/0.92    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.52/0.92    inference(negated_conjecture,[],[f10])).
% 2.52/0.92  
% 2.52/0.92  fof(f16,plain,(
% 2.52/0.92    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.52/0.92    inference(ennf_transformation,[],[f11])).
% 2.52/0.92  
% 2.52/0.92  fof(f28,plain,(
% 2.52/0.92    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK6) = sK6 | k6_mcart_1(X0,X1,X2,sK6) = sK6 | k5_mcart_1(X0,X1,X2,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.52/0.92    introduced(choice_axiom,[])).
% 2.52/0.92  
% 2.52/0.92  fof(f27,plain,(
% 2.52/0.92    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK3,sK4,sK5,X3) = X3 | k6_mcart_1(sK3,sK4,sK5,X3) = X3 | k5_mcart_1(sK3,sK4,sK5,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3)),
% 2.52/0.92    introduced(choice_axiom,[])).
% 2.52/0.92  
% 2.52/0.92  fof(f29,plain,(
% 2.52/0.92    ((k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6) & m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3),
% 2.52/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f28,f27])).
% 2.52/0.92  
% 2.52/0.92  fof(f54,plain,(
% 2.52/0.92    k7_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6 | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6),
% 2.52/0.92    inference(cnf_transformation,[],[f29])).
% 2.52/0.92  
% 2.52/0.92  fof(f8,axiom,(
% 2.52/0.92    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f14,plain,(
% 2.52/0.92    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.52/0.92    inference(ennf_transformation,[],[f8])).
% 2.52/0.92  
% 2.52/0.92  fof(f46,plain,(
% 2.52/0.92    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f14])).
% 2.52/0.92  
% 2.52/0.92  fof(f5,axiom,(
% 2.52/0.92    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f39,plain,(
% 2.52/0.92    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.52/0.92    inference(cnf_transformation,[],[f5])).
% 2.52/0.92  
% 2.52/0.92  fof(f58,plain,(
% 2.52/0.92    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(definition_unfolding,[],[f46,f39])).
% 2.52/0.92  
% 2.52/0.92  fof(f53,plain,(
% 2.52/0.92    m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.52/0.92    inference(cnf_transformation,[],[f29])).
% 2.52/0.92  
% 2.52/0.92  fof(f61,plain,(
% 2.52/0.92    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.52/0.92    inference(definition_unfolding,[],[f53,f39])).
% 2.52/0.92  
% 2.52/0.92  fof(f50,plain,(
% 2.52/0.92    k1_xboole_0 != sK3),
% 2.52/0.92    inference(cnf_transformation,[],[f29])).
% 2.52/0.92  
% 2.52/0.92  fof(f51,plain,(
% 2.52/0.92    k1_xboole_0 != sK4),
% 2.52/0.92    inference(cnf_transformation,[],[f29])).
% 2.52/0.92  
% 2.52/0.92  fof(f52,plain,(
% 2.52/0.92    k1_xboole_0 != sK5),
% 2.52/0.92    inference(cnf_transformation,[],[f29])).
% 2.52/0.92  
% 2.52/0.92  fof(f2,axiom,(
% 2.52/0.92    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f21,plain,(
% 2.52/0.92    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.52/0.92    inference(nnf_transformation,[],[f2])).
% 2.52/0.92  
% 2.52/0.92  fof(f22,plain,(
% 2.52/0.92    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.52/0.92    inference(flattening,[],[f21])).
% 2.52/0.92  
% 2.52/0.92  fof(f34,plain,(
% 2.52/0.92    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f22])).
% 2.52/0.92  
% 2.52/0.92  fof(f35,plain,(
% 2.52/0.92    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f22])).
% 2.52/0.92  
% 2.52/0.92  fof(f66,plain,(
% 2.52/0.92    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.52/0.92    inference(equality_resolution,[],[f35])).
% 2.52/0.92  
% 2.52/0.92  fof(f45,plain,(
% 2.52/0.92    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f14])).
% 2.52/0.92  
% 2.52/0.92  fof(f59,plain,(
% 2.52/0.92    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(definition_unfolding,[],[f45,f39])).
% 2.52/0.92  
% 2.52/0.92  fof(f44,plain,(
% 2.52/0.92    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f14])).
% 2.52/0.92  
% 2.52/0.92  fof(f60,plain,(
% 2.52/0.92    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(definition_unfolding,[],[f44,f39])).
% 2.52/0.92  
% 2.52/0.92  fof(f6,axiom,(
% 2.52/0.92    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f12,plain,(
% 2.52/0.92    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.52/0.92    inference(ennf_transformation,[],[f6])).
% 2.52/0.92  
% 2.52/0.92  fof(f23,plain,(
% 2.52/0.92    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 2.52/0.92    introduced(choice_axiom,[])).
% 2.52/0.92  
% 2.52/0.92  fof(f24,plain,(
% 2.52/0.92    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 2.52/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f23])).
% 2.52/0.92  
% 2.52/0.92  fof(f40,plain,(
% 2.52/0.92    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f24])).
% 2.52/0.92  
% 2.52/0.92  fof(f1,axiom,(
% 2.52/0.92    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f17,plain,(
% 2.52/0.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.52/0.92    inference(nnf_transformation,[],[f1])).
% 2.52/0.92  
% 2.52/0.92  fof(f18,plain,(
% 2.52/0.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.52/0.92    inference(rectify,[],[f17])).
% 2.52/0.92  
% 2.52/0.92  fof(f19,plain,(
% 2.52/0.92    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.52/0.92    introduced(choice_axiom,[])).
% 2.52/0.92  
% 2.52/0.92  fof(f20,plain,(
% 2.52/0.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.52/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 2.52/0.92  
% 2.52/0.92  fof(f30,plain,(
% 2.52/0.92    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.52/0.92    inference(cnf_transformation,[],[f20])).
% 2.52/0.92  
% 2.52/0.92  fof(f64,plain,(
% 2.52/0.92    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.52/0.92    inference(equality_resolution,[],[f30])).
% 2.52/0.92  
% 2.52/0.92  fof(f7,axiom,(
% 2.52/0.92    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f13,plain,(
% 2.52/0.92    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.52/0.92    inference(ennf_transformation,[],[f7])).
% 2.52/0.92  
% 2.52/0.92  fof(f43,plain,(
% 2.52/0.92    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f13])).
% 2.52/0.92  
% 2.52/0.92  fof(f4,axiom,(
% 2.52/0.92    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f38,plain,(
% 2.52/0.92    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.52/0.92    inference(cnf_transformation,[],[f4])).
% 2.52/0.92  
% 2.52/0.92  fof(f57,plain,(
% 2.52/0.92    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(definition_unfolding,[],[f43,f38,f39])).
% 2.52/0.92  
% 2.52/0.92  fof(f41,plain,(
% 2.52/0.92    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f24])).
% 2.52/0.92  
% 2.52/0.92  fof(f56,plain,(
% 2.52/0.92    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(definition_unfolding,[],[f41,f38])).
% 2.52/0.92  
% 2.52/0.92  fof(f31,plain,(
% 2.52/0.92    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.52/0.92    inference(cnf_transformation,[],[f20])).
% 2.52/0.92  
% 2.52/0.92  fof(f62,plain,(
% 2.52/0.92    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.52/0.92    inference(equality_resolution,[],[f31])).
% 2.52/0.92  
% 2.52/0.92  fof(f63,plain,(
% 2.52/0.92    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.52/0.92    inference(equality_resolution,[],[f62])).
% 2.52/0.92  
% 2.52/0.92  fof(f42,plain,(
% 2.52/0.92    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f24])).
% 2.52/0.92  
% 2.52/0.92  fof(f55,plain,(
% 2.52/0.92    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(definition_unfolding,[],[f42,f38])).
% 2.52/0.92  
% 2.52/0.92  fof(f9,axiom,(
% 2.52/0.92    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f15,plain,(
% 2.52/0.92    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.52/0.92    inference(ennf_transformation,[],[f9])).
% 2.52/0.92  
% 2.52/0.92  fof(f25,plain,(
% 2.52/0.92    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 2.52/0.92    introduced(choice_axiom,[])).
% 2.52/0.92  
% 2.52/0.92  fof(f26,plain,(
% 2.52/0.92    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 2.52/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f25])).
% 2.52/0.92  
% 2.52/0.92  fof(f47,plain,(
% 2.52/0.92    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f26])).
% 2.52/0.92  
% 2.52/0.92  fof(f49,plain,(
% 2.52/0.92    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 2.52/0.92    inference(cnf_transformation,[],[f26])).
% 2.52/0.92  
% 2.52/0.92  fof(f36,plain,(
% 2.52/0.92    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.52/0.92    inference(cnf_transformation,[],[f22])).
% 2.52/0.92  
% 2.52/0.92  fof(f65,plain,(
% 2.52/0.92    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.52/0.92    inference(equality_resolution,[],[f36])).
% 2.52/0.92  
% 2.52/0.92  fof(f3,axiom,(
% 2.52/0.92    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.92  
% 2.52/0.92  fof(f37,plain,(
% 2.52/0.92    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.52/0.92    inference(cnf_transformation,[],[f3])).
% 2.52/0.92  
% 2.52/0.92  cnf(c_18,negated_conjecture,
% 2.52/0.92      ( k7_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 2.52/0.92      | k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 2.52/0.92      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6 ),
% 2.52/0.92      inference(cnf_transformation,[],[f54]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_12,plain,
% 2.52/0.92      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.52/0.92      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.52/0.92      | k1_xboole_0 = X2
% 2.52/0.92      | k1_xboole_0 = X1
% 2.52/0.92      | k1_xboole_0 = X3 ),
% 2.52/0.92      inference(cnf_transformation,[],[f58]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_19,negated_conjecture,
% 2.52/0.92      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 2.52/0.92      inference(cnf_transformation,[],[f61]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_230,plain,
% 2.52/0.92      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.52/0.92      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 2.52/0.92      | sK6 != X3
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | k1_xboole_0 = X2
% 2.52/0.92      | k1_xboole_0 = X1 ),
% 2.52/0.92      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_231,plain,
% 2.52/0.92      ( k7_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(sK6)
% 2.52/0.92      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 2.52/0.92      | k1_xboole_0 = X1
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | k1_xboole_0 = X2 ),
% 2.52/0.92      inference(unflattening,[status(thm)],[c_230]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1502,plain,
% 2.52/0.92      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
% 2.52/0.92      | sK5 = k1_xboole_0
% 2.52/0.92      | sK4 = k1_xboole_0
% 2.52/0.92      | sK3 = k1_xboole_0 ),
% 2.52/0.92      inference(equality_resolution,[status(thm)],[c_231]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_22,negated_conjecture,
% 2.52/0.92      ( k1_xboole_0 != sK3 ),
% 2.52/0.92      inference(cnf_transformation,[],[f50]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_21,negated_conjecture,
% 2.52/0.92      ( k1_xboole_0 != sK4 ),
% 2.52/0.92      inference(cnf_transformation,[],[f51]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_20,negated_conjecture,
% 2.52/0.92      ( k1_xboole_0 != sK5 ),
% 2.52/0.92      inference(cnf_transformation,[],[f52]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_6,plain,
% 2.52/0.92      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.52/0.92      | k1_xboole_0 = X1
% 2.52/0.92      | k1_xboole_0 = X0 ),
% 2.52/0.92      inference(cnf_transformation,[],[f34]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_53,plain,
% 2.52/0.92      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.52/0.92      | k1_xboole_0 = k1_xboole_0 ),
% 2.52/0.92      inference(instantiation,[status(thm)],[c_6]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_5,plain,
% 2.52/0.92      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.52/0.92      inference(cnf_transformation,[],[f66]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_54,plain,
% 2.52/0.92      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.52/0.92      inference(instantiation,[status(thm)],[c_5]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1046,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1458,plain,
% 2.52/0.92      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.52/0.92      inference(instantiation,[status(thm)],[c_1046]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1459,plain,
% 2.52/0.92      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 2.52/0.92      inference(instantiation,[status(thm)],[c_1458]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1460,plain,
% 2.52/0.92      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.52/0.92      inference(instantiation,[status(thm)],[c_1046]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1461,plain,
% 2.52/0.92      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.52/0.92      inference(instantiation,[status(thm)],[c_1460]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1462,plain,
% 2.52/0.92      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.52/0.92      inference(instantiation,[status(thm)],[c_1046]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1463,plain,
% 2.52/0.92      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.52/0.92      inference(instantiation,[status(thm)],[c_1462]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1785,plain,
% 2.52/0.92      ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
% 2.52/0.92      inference(global_propositional_subsumption,
% 2.52/0.92                [status(thm)],
% 2.52/0.92                [c_1502,c_22,c_21,c_20,c_53,c_54,c_1459,c_1461,c_1463]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1788,plain,
% 2.52/0.92      ( k6_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 2.52/0.92      | k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 2.52/0.92      | k2_mcart_1(sK6) = sK6 ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_18,c_1785]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_13,plain,
% 2.52/0.92      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.52/0.92      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.52/0.92      | k1_xboole_0 = X2
% 2.52/0.92      | k1_xboole_0 = X1
% 2.52/0.92      | k1_xboole_0 = X3 ),
% 2.52/0.92      inference(cnf_transformation,[],[f59]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_212,plain,
% 2.52/0.92      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.52/0.92      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 2.52/0.92      | sK6 != X3
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | k1_xboole_0 = X2
% 2.52/0.92      | k1_xboole_0 = X1 ),
% 2.52/0.92      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_213,plain,
% 2.52/0.92      ( k6_mcart_1(X0,X1,X2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 2.52/0.92      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 2.52/0.92      | k1_xboole_0 = X1
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | k1_xboole_0 = X2 ),
% 2.52/0.92      inference(unflattening,[status(thm)],[c_212]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1554,plain,
% 2.52/0.92      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 2.52/0.92      | sK5 = k1_xboole_0
% 2.52/0.92      | sK4 = k1_xboole_0
% 2.52/0.92      | sK3 = k1_xboole_0 ),
% 2.52/0.92      inference(equality_resolution,[status(thm)],[c_213]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1859,plain,
% 2.52/0.92      ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
% 2.52/0.92      inference(global_propositional_subsumption,
% 2.52/0.92                [status(thm)],
% 2.52/0.92                [c_1554,c_22,c_21,c_20,c_53,c_54,c_1459,c_1461,c_1463]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1862,plain,
% 2.52/0.92      ( k5_mcart_1(sK3,sK4,sK5,sK6) = sK6
% 2.52/0.92      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 2.52/0.92      | k2_mcart_1(sK6) = sK6 ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_1788,c_1859]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_14,plain,
% 2.52/0.92      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.52/0.92      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.52/0.92      | k1_xboole_0 = X2
% 2.52/0.92      | k1_xboole_0 = X1
% 2.52/0.92      | k1_xboole_0 = X3 ),
% 2.52/0.92      inference(cnf_transformation,[],[f60]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_194,plain,
% 2.52/0.92      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.52/0.92      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 2.52/0.92      | sK6 != X3
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | k1_xboole_0 = X2
% 2.52/0.92      | k1_xboole_0 = X1 ),
% 2.52/0.92      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_195,plain,
% 2.52/0.92      ( k5_mcart_1(X0,X1,X2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 2.52/0.92      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 2.52/0.92      | k1_xboole_0 = X1
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | k1_xboole_0 = X2 ),
% 2.52/0.92      inference(unflattening,[status(thm)],[c_194]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1508,plain,
% 2.52/0.92      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 2.52/0.92      | sK5 = k1_xboole_0
% 2.52/0.92      | sK4 = k1_xboole_0
% 2.52/0.92      | sK3 = k1_xboole_0 ),
% 2.52/0.92      inference(equality_resolution,[status(thm)],[c_195]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1829,plain,
% 2.52/0.92      ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
% 2.52/0.92      inference(global_propositional_subsumption,
% 2.52/0.92                [status(thm)],
% 2.52/0.92                [c_1508,c_22,c_21,c_20,c_53,c_54,c_1459,c_1461,c_1463]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1864,plain,
% 2.52/0.92      ( k1_mcart_1(k1_mcart_1(sK6)) = sK6
% 2.52/0.92      | k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 2.52/0.92      | k2_mcart_1(sK6) = sK6 ),
% 2.52/0.92      inference(demodulation,[status(thm)],[c_1862,c_1829]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_10,plain,
% 2.52/0.92      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.52/0.92      inference(cnf_transformation,[],[f40]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1241,plain,
% 2.52/0.92      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.52/0.92      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_3,plain,
% 2.52/0.92      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 2.52/0.92      inference(cnf_transformation,[],[f64]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1245,plain,
% 2.52/0.92      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 2.52/0.92      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2141,plain,
% 2.52/0.92      ( sK1(k1_tarski(X0)) = X0 | k1_tarski(X0) = k1_xboole_0 ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_1241,c_1245]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_11,plain,
% 2.52/0.92      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.52/0.92      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 2.52/0.92      | k1_xboole_0 = X2
% 2.52/0.92      | k1_xboole_0 = X1
% 2.52/0.92      | k1_xboole_0 = X3 ),
% 2.52/0.92      inference(cnf_transformation,[],[f57]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_248,plain,
% 2.52/0.92      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 2.52/0.92      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 2.52/0.92      | sK6 != X3
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | k1_xboole_0 = X2
% 2.52/0.92      | k1_xboole_0 = X1 ),
% 2.52/0.92      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_249,plain,
% 2.52/0.92      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK6),k6_mcart_1(X0,X1,X2,sK6)),k7_mcart_1(X0,X1,X2,sK6)) = sK6
% 2.52/0.92      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
% 2.52/0.92      | k1_xboole_0 = X1
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | k1_xboole_0 = X2 ),
% 2.52/0.92      inference(unflattening,[status(thm)],[c_248]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1560,plain,
% 2.52/0.92      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6
% 2.52/0.92      | sK5 = k1_xboole_0
% 2.52/0.92      | sK4 = k1_xboole_0
% 2.52/0.92      | sK3 = k1_xboole_0 ),
% 2.52/0.92      inference(equality_resolution,[status(thm)],[c_249]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1865,plain,
% 2.52/0.92      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK6),k6_mcart_1(sK3,sK4,sK5,sK6)),k7_mcart_1(sK3,sK4,sK5,sK6)) = sK6 ),
% 2.52/0.92      inference(global_propositional_subsumption,
% 2.52/0.92                [status(thm)],
% 2.52/0.92                [c_1560,c_22,c_21,c_20,c_53,c_54,c_1459,c_1461,c_1463]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1867,plain,
% 2.52/0.92      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))),k2_mcart_1(sK6)) = sK6 ),
% 2.52/0.92      inference(light_normalisation,
% 2.52/0.92                [status(thm)],
% 2.52/0.92                [c_1865,c_1785,c_1829,c_1859]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_9,plain,
% 2.52/0.92      ( ~ r2_hidden(X0,X1)
% 2.52/0.92      | k4_tarski(k4_tarski(X0,X2),X3) != sK1(X1)
% 2.52/0.92      | k1_xboole_0 = X1 ),
% 2.52/0.92      inference(cnf_transformation,[],[f56]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1242,plain,
% 2.52/0.92      ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
% 2.52/0.92      | k1_xboole_0 = X3
% 2.52/0.92      | r2_hidden(X0,X3) != iProver_top ),
% 2.52/0.92      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2290,plain,
% 2.52/0.92      ( sK1(X0) != sK6
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_1867,c_1242]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2505,plain,
% 2.52/0.92      ( k1_tarski(X0) = k1_xboole_0
% 2.52/0.92      | sK6 != X0
% 2.52/0.92      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_tarski(X0)) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_2141,c_2290]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2771,plain,
% 2.52/0.92      ( k1_tarski(sK6) = k1_xboole_0
% 2.52/0.92      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_tarski(sK6)) != iProver_top ),
% 2.52/0.92      inference(equality_resolution,[status(thm)],[c_2505]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_3200,plain,
% 2.52/0.92      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 2.52/0.92      | k2_mcart_1(sK6) = sK6
% 2.52/0.92      | k1_tarski(sK6) = k1_xboole_0
% 2.52/0.92      | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_1864,c_2771]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2,plain,
% 2.52/0.92      ( r2_hidden(X0,k1_tarski(X0)) ),
% 2.52/0.92      inference(cnf_transformation,[],[f63]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1246,plain,
% 2.52/0.92      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 2.52/0.92      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_3207,plain,
% 2.52/0.92      ( k2_mcart_1(k1_mcart_1(sK6)) = sK6
% 2.52/0.92      | k2_mcart_1(sK6) = sK6
% 2.52/0.92      | k1_tarski(sK6) = k1_xboole_0 ),
% 2.52/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_3200,c_1246]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_8,plain,
% 2.52/0.92      ( ~ r2_hidden(X0,X1)
% 2.52/0.92      | k4_tarski(k4_tarski(X2,X0),X3) != sK1(X1)
% 2.52/0.92      | k1_xboole_0 = X1 ),
% 2.52/0.92      inference(cnf_transformation,[],[f55]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1243,plain,
% 2.52/0.92      ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
% 2.52/0.92      | k1_xboole_0 = X3
% 2.52/0.92      | r2_hidden(X1,X3) != iProver_top ),
% 2.52/0.92      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2413,plain,
% 2.52/0.92      ( sK1(X0) != sK6
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_1867,c_1243]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2689,plain,
% 2.52/0.92      ( k1_tarski(X0) = k1_xboole_0
% 2.52/0.92      | sK6 != X0
% 2.52/0.92      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_tarski(X0)) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_2141,c_2413]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2777,plain,
% 2.52/0.92      ( k1_tarski(sK6) = k1_xboole_0
% 2.52/0.92      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_tarski(sK6)) != iProver_top ),
% 2.52/0.92      inference(equality_resolution,[status(thm)],[c_2689]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_3514,plain,
% 2.52/0.92      ( k2_mcart_1(sK6) = sK6
% 2.52/0.92      | k1_tarski(sK6) = k1_xboole_0
% 2.52/0.92      | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_3207,c_2777]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_3791,plain,
% 2.52/0.92      ( k2_mcart_1(sK6) = sK6 | k1_tarski(sK6) = k1_xboole_0 ),
% 2.52/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_3514,c_1246]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_17,plain,
% 2.52/0.92      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.52/0.92      inference(cnf_transformation,[],[f47]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1238,plain,
% 2.52/0.92      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.52/0.92      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2142,plain,
% 2.52/0.92      ( sK2(k1_tarski(X0)) = X0 | k1_tarski(X0) = k1_xboole_0 ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_1238,c_1245]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_15,plain,
% 2.52/0.92      ( ~ r2_hidden(X0,X1) | k4_tarski(X2,X0) != sK2(X1) | k1_xboole_0 = X1 ),
% 2.52/0.92      inference(cnf_transformation,[],[f49]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1240,plain,
% 2.52/0.92      ( k4_tarski(X0,X1) != sK2(X2)
% 2.52/0.92      | k1_xboole_0 = X2
% 2.52/0.92      | r2_hidden(X1,X2) != iProver_top ),
% 2.52/0.92      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2215,plain,
% 2.52/0.92      ( sK2(X0) != sK6
% 2.52/0.92      | k1_xboole_0 = X0
% 2.52/0.92      | r2_hidden(k2_mcart_1(sK6),X0) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_1867,c_1240]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2632,plain,
% 2.52/0.92      ( k1_tarski(X0) = k1_xboole_0
% 2.52/0.92      | sK6 != X0
% 2.52/0.92      | r2_hidden(k2_mcart_1(sK6),k1_tarski(X0)) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_2142,c_2215]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_2735,plain,
% 2.52/0.92      ( k1_tarski(sK6) = k1_xboole_0
% 2.52/0.92      | r2_hidden(k2_mcart_1(sK6),k1_tarski(sK6)) != iProver_top ),
% 2.52/0.92      inference(equality_resolution,[status(thm)],[c_2632]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_3794,plain,
% 2.52/0.92      ( k1_tarski(sK6) = k1_xboole_0
% 2.52/0.92      | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_3791,c_2735]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_3968,plain,
% 2.52/0.92      ( k1_tarski(sK6) = k1_xboole_0 ),
% 2.52/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_3794,c_1246]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_3976,plain,
% 2.52/0.92      ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_3968,c_1246]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_4,plain,
% 2.52/0.92      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.52/0.92      inference(cnf_transformation,[],[f65]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_7,plain,
% 2.52/0.92      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.52/0.92      inference(cnf_transformation,[],[f37]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1244,plain,
% 2.52/0.92      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.52/0.92      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_1952,plain,
% 2.52/0.92      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.52/0.92      inference(superposition,[status(thm)],[c_4,c_1244]) ).
% 2.52/0.92  
% 2.52/0.92  cnf(c_4087,plain,
% 2.52/0.92      ( $false ),
% 2.52/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_3976,c_1952]) ).
% 2.52/0.92  
% 2.52/0.92  
% 2.52/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/0.92  
% 2.52/0.92  ------                               Statistics
% 2.52/0.92  
% 2.52/0.92  ------ General
% 2.52/0.92  
% 2.52/0.92  abstr_ref_over_cycles:                  0
% 2.52/0.92  abstr_ref_under_cycles:                 0
% 2.52/0.92  gc_basic_clause_elim:                   0
% 2.52/0.92  forced_gc_time:                         0
% 2.52/0.92  parsing_time:                           0.011
% 2.52/0.92  unif_index_cands_time:                  0.
% 2.52/0.92  unif_index_add_time:                    0.
% 2.52/0.92  orderings_time:                         0.
% 2.52/0.92  out_proof_time:                         0.009
% 2.52/0.92  total_time:                             0.15
% 2.52/0.92  num_of_symbols:                         49
% 2.52/0.92  num_of_terms:                           4470
% 2.52/0.92  
% 2.52/0.92  ------ Preprocessing
% 2.52/0.92  
% 2.52/0.92  num_of_splits:                          0
% 2.52/0.92  num_of_split_atoms:                     0
% 2.52/0.92  num_of_reused_defs:                     0
% 2.52/0.92  num_eq_ax_congr_red:                    15
% 2.52/0.92  num_of_sem_filtered_clauses:            1
% 2.52/0.92  num_of_subtypes:                        0
% 2.52/0.92  monotx_restored_types:                  0
% 2.52/0.92  sat_num_of_epr_types:                   0
% 2.52/0.92  sat_num_of_non_cyclic_types:            0
% 2.52/0.92  sat_guarded_non_collapsed_types:        0
% 2.52/0.92  num_pure_diseq_elim:                    0
% 2.52/0.92  simp_replaced_by:                       0
% 2.52/0.92  res_preprocessed:                       110
% 2.52/0.92  prep_upred:                             0
% 2.52/0.92  prep_unflattend:                        96
% 2.52/0.92  smt_new_axioms:                         0
% 2.52/0.92  pred_elim_cands:                        1
% 2.52/0.92  pred_elim:                              1
% 2.52/0.92  pred_elim_cl:                           1
% 2.52/0.92  pred_elim_cycles:                       3
% 2.52/0.92  merged_defs:                            0
% 2.52/0.92  merged_defs_ncl:                        0
% 2.52/0.92  bin_hyper_res:                          0
% 2.52/0.92  prep_cycles:                            4
% 2.52/0.92  pred_elim_time:                         0.012
% 2.52/0.92  splitting_time:                         0.
% 2.52/0.92  sem_filter_time:                        0.
% 2.52/0.92  monotx_time:                            0.
% 2.52/0.92  subtype_inf_time:                       0.
% 2.52/0.92  
% 2.52/0.92  ------ Problem properties
% 2.52/0.92  
% 2.52/0.92  clauses:                                22
% 2.52/0.92  conjectures:                            4
% 2.52/0.92  epr:                                    3
% 2.52/0.92  horn:                                   13
% 2.52/0.92  ground:                                 4
% 2.52/0.92  unary:                                  7
% 2.52/0.92  binary:                                 3
% 2.52/0.92  lits:                                   57
% 2.52/0.92  lits_eq:                                46
% 2.52/0.92  fd_pure:                                0
% 2.52/0.92  fd_pseudo:                              0
% 2.52/0.92  fd_cond:                                11
% 2.52/0.92  fd_pseudo_cond:                         2
% 2.52/0.92  ac_symbols:                             0
% 2.52/0.92  
% 2.52/0.92  ------ Propositional Solver
% 2.52/0.92  
% 2.52/0.92  prop_solver_calls:                      27
% 2.52/0.92  prop_fast_solver_calls:                 990
% 2.52/0.92  smt_solver_calls:                       0
% 2.52/0.92  smt_fast_solver_calls:                  0
% 2.52/0.92  prop_num_of_clauses:                    1461
% 2.52/0.92  prop_preprocess_simplified:             4814
% 2.52/0.92  prop_fo_subsumed:                       12
% 2.52/0.92  prop_solver_time:                       0.
% 2.52/0.92  smt_solver_time:                        0.
% 2.52/0.92  smt_fast_solver_time:                   0.
% 2.52/0.92  prop_fast_solver_time:                  0.
% 2.52/0.92  prop_unsat_core_time:                   0.
% 2.52/0.92  
% 2.52/0.92  ------ QBF
% 2.52/0.92  
% 2.52/0.92  qbf_q_res:                              0
% 2.52/0.92  qbf_num_tautologies:                    0
% 2.52/0.92  qbf_prep_cycles:                        0
% 2.52/0.92  
% 2.52/0.92  ------ BMC1
% 2.52/0.92  
% 2.52/0.92  bmc1_current_bound:                     -1
% 2.52/0.92  bmc1_last_solved_bound:                 -1
% 2.52/0.92  bmc1_unsat_core_size:                   -1
% 2.52/0.92  bmc1_unsat_core_parents_size:           -1
% 2.52/0.92  bmc1_merge_next_fun:                    0
% 2.52/0.92  bmc1_unsat_core_clauses_time:           0.
% 2.52/0.92  
% 2.52/0.92  ------ Instantiation
% 2.52/0.92  
% 2.52/0.92  inst_num_of_clauses:                    668
% 2.52/0.92  inst_num_in_passive:                    181
% 2.52/0.92  inst_num_in_active:                     379
% 2.52/0.92  inst_num_in_unprocessed:                108
% 2.52/0.92  inst_num_of_loops:                      380
% 2.52/0.92  inst_num_of_learning_restarts:          0
% 2.52/0.92  inst_num_moves_active_passive:          0
% 2.52/0.92  inst_lit_activity:                      0
% 2.52/0.92  inst_lit_activity_moves:                0
% 2.52/0.92  inst_num_tautologies:                   0
% 2.52/0.92  inst_num_prop_implied:                  0
% 2.52/0.92  inst_num_existing_simplified:           0
% 2.52/0.92  inst_num_eq_res_simplified:             0
% 2.52/0.92  inst_num_child_elim:                    0
% 2.52/0.92  inst_num_of_dismatching_blockings:      62
% 2.52/0.92  inst_num_of_non_proper_insts:           732
% 2.52/0.92  inst_num_of_duplicates:                 0
% 2.52/0.92  inst_inst_num_from_inst_to_res:         0
% 2.52/0.92  inst_dismatching_checking_time:         0.
% 2.52/0.92  
% 2.52/0.92  ------ Resolution
% 2.52/0.92  
% 2.52/0.92  res_num_of_clauses:                     0
% 2.52/0.92  res_num_in_passive:                     0
% 2.52/0.92  res_num_in_active:                      0
% 2.52/0.92  res_num_of_loops:                       114
% 2.52/0.92  res_forward_subset_subsumed:            16
% 2.52/0.92  res_backward_subset_subsumed:           0
% 2.52/0.92  res_forward_subsumed:                   0
% 2.52/0.92  res_backward_subsumed:                  0
% 2.52/0.92  res_forward_subsumption_resolution:     0
% 2.52/0.92  res_backward_subsumption_resolution:    0
% 2.52/0.92  res_clause_to_clause_subsumption:       391
% 2.52/0.92  res_orphan_elimination:                 0
% 2.52/0.92  res_tautology_del:                      18
% 2.52/0.92  res_num_eq_res_simplified:              0
% 2.52/0.92  res_num_sel_changes:                    0
% 2.52/0.92  res_moves_from_active_to_pass:          0
% 2.52/0.92  
% 2.52/0.92  ------ Superposition
% 2.52/0.92  
% 2.52/0.92  sup_time_total:                         0.
% 2.52/0.92  sup_time_generating:                    0.
% 2.52/0.92  sup_time_sim_full:                      0.
% 2.52/0.92  sup_time_sim_immed:                     0.
% 2.52/0.92  
% 2.52/0.92  sup_num_of_clauses:                     77
% 2.52/0.92  sup_num_in_active:                      59
% 2.52/0.92  sup_num_in_passive:                     18
% 2.52/0.92  sup_num_of_loops:                       74
% 2.52/0.92  sup_fw_superposition:                   60
% 2.52/0.92  sup_bw_superposition:                   73
% 2.52/0.92  sup_immediate_simplified:               45
% 2.52/0.92  sup_given_eliminated:                   0
% 2.52/0.92  comparisons_done:                       0
% 2.52/0.92  comparisons_avoided:                    24
% 2.52/0.92  
% 2.52/0.92  ------ Simplifications
% 2.52/0.92  
% 2.52/0.92  
% 2.52/0.92  sim_fw_subset_subsumed:                 21
% 2.52/0.92  sim_bw_subset_subsumed:                 12
% 2.52/0.92  sim_fw_subsumed:                        16
% 2.52/0.92  sim_bw_subsumed:                        4
% 2.52/0.92  sim_fw_subsumption_res:                 7
% 2.52/0.92  sim_bw_subsumption_res:                 0
% 2.52/0.92  sim_tautology_del:                      0
% 2.52/0.92  sim_eq_tautology_del:                   20
% 2.52/0.92  sim_eq_res_simp:                        0
% 2.52/0.92  sim_fw_demodulated:                     1
% 2.52/0.92  sim_bw_demodulated:                     5
% 2.52/0.92  sim_light_normalised:                   4
% 2.52/0.92  sim_joinable_taut:                      0
% 2.52/0.92  sim_joinable_simp:                      0
% 2.52/0.92  sim_ac_normalised:                      0
% 2.52/0.92  sim_smt_subsumption:                    0
% 2.52/0.92  
%------------------------------------------------------------------------------
