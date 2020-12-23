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
% DateTime   : Thu Dec  3 11:58:34 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  141 (2017 expanded)
%              Number of clauses        :   77 ( 659 expanded)
%              Number of leaves         :   16 ( 580 expanded)
%              Depth                    :   28
%              Number of atoms          :  458 (9495 expanded)
%              Number of equality atoms :  380 (8190 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f30])).

fof(f63,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f62])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f37,f38])).

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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f27,f26])).

fof(f53,plain,(
    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f53,f38])).

fof(f50,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f34])).

fof(f9,axiom,(
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

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f38])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f40])).

fof(f49,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f37])).

fof(f43,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X4,X2,X0,X3] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_836,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_831,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_835,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2129,plain,
    ( sK1(k1_tarski(X0)) = X0
    | k1_tarski(X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_831,c_835])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_224,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | sK5 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_225,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK5),k6_mcart_1(X0,X1,X2,sK5)),k7_mcart_1(X0,X1,X2,sK5)) = sK5
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_1119,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_225])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_51,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_52,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_683,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1016,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_1017,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_1018,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_1019,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_1020,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_1021,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_1430,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1119,c_23,c_22,c_21,c_51,c_52,c_1017,c_1019,c_1021])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_206,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | sK5 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_207,plain,
    ( k7_mcart_1(X0,X1,X2,sK5) = k2_mcart_1(sK5)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_1071,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_207])).

cnf(c_1356,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1071,c_23,c_22,c_21,c_51,c_52,c_1017,c_1019,c_1021])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_170,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | sK5 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_171,plain,
    ( k5_mcart_1(X0,X1,X2,sK5) = k1_mcart_1(k1_mcart_1(sK5))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_170])).

cnf(c_1077,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_171])).

cnf(c_1394,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1077,c_23,c_22,c_21,c_51,c_52,c_1017,c_1019,c_1021])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_188,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | sK5 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_189,plain,
    ( k6_mcart_1(X0,X1,X2,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_1113,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_189])).

cnf(c_1424,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1113,c_23,c_22,c_21,c_51,c_52,c_1017,c_1019,c_1021])).

cnf(c_1432,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_1430,c_1356,c_1394,c_1424])).

cnf(c_18,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1434,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
    inference(superposition,[status(thm)],[c_1432,c_18])).

cnf(c_1470,plain,
    ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_1434,c_1432])).

cnf(c_19,negated_conjecture,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1359,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_19,c_1356])).

cnf(c_1427,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1359,c_1424])).

cnf(c_1429,plain,
    ( k1_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_1427,c_1394])).

cnf(c_1468,plain,
    ( k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1429,c_1432])).

cnf(c_8,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_17,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_860,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_8,c_17])).

cnf(c_1684,plain,
    ( k2_mcart_1(sK5) != sK5 ),
    inference(superposition,[status(thm)],[c_1470,c_860])).

cnf(c_1825,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1468,c_1684])).

cnf(c_1826,plain,
    ( k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
    inference(renaming,[status(thm)],[c_1825])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X0,X2),X3) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_832,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1834,plain,
    ( sK1(X0) != sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k1_xboole_0 = X0
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1826,c_832])).

cnf(c_2364,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k1_tarski(X0) = k1_xboole_0
    | sK5 != X0
    | r2_hidden(sK5,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2129,c_1834])).

cnf(c_3193,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k1_tarski(X0) = k1_xboole_0
    | r2_hidden(sK5,k1_tarski(X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2364,c_835])).

cnf(c_3197,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
    | k1_tarski(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_836,c_3193])).

cnf(c_3377,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_mcart_1(sK5)
    | k1_tarski(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3197,c_1434])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k4_tarski(X2,X0),X3) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_833,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3522,plain,
    ( k4_tarski(k1_mcart_1(sK5),X0) != sK1(X1)
    | k1_tarski(sK5) = k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(sK5,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3377,c_833])).

cnf(c_3702,plain,
    ( sK1(X0) != sK5
    | k1_tarski(sK5) = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_3522])).

cnf(c_3718,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | k1_tarski(sK5) = k1_xboole_0
    | sK5 != X0
    | r2_hidden(sK5,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2129,c_3702])).

cnf(c_3806,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | k1_tarski(sK5) = k1_xboole_0
    | r2_hidden(sK5,k1_tarski(X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3718,c_835])).

cnf(c_3810,plain,
    ( k1_tarski(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_836,c_3806])).

cnf(c_3979,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3810,c_836])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_834,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2081,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_834])).

cnf(c_4075,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3979,c_2081])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:27:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.80/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/0.97  
% 2.80/0.97  ------  iProver source info
% 2.80/0.97  
% 2.80/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.80/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/0.97  git: non_committed_changes: false
% 2.80/0.97  git: last_make_outside_of_git: false
% 2.80/0.97  
% 2.80/0.97  ------ 
% 2.80/0.97  
% 2.80/0.97  ------ Input Options
% 2.80/0.97  
% 2.80/0.97  --out_options                           all
% 2.80/0.97  --tptp_safe_out                         true
% 2.80/0.97  --problem_path                          ""
% 2.80/0.97  --include_path                          ""
% 2.80/0.97  --clausifier                            res/vclausify_rel
% 2.80/0.97  --clausifier_options                    --mode clausify
% 2.80/0.97  --stdin                                 false
% 2.80/0.97  --stats_out                             all
% 2.80/0.97  
% 2.80/0.97  ------ General Options
% 2.80/0.97  
% 2.80/0.97  --fof                                   false
% 2.80/0.97  --time_out_real                         305.
% 2.80/0.97  --time_out_virtual                      -1.
% 2.80/0.97  --symbol_type_check                     false
% 2.80/0.97  --clausify_out                          false
% 2.80/0.97  --sig_cnt_out                           false
% 2.80/0.97  --trig_cnt_out                          false
% 2.80/0.97  --trig_cnt_out_tolerance                1.
% 2.80/0.97  --trig_cnt_out_sk_spl                   false
% 2.80/0.97  --abstr_cl_out                          false
% 2.80/0.97  
% 2.80/0.97  ------ Global Options
% 2.80/0.97  
% 2.80/0.97  --schedule                              default
% 2.80/0.97  --add_important_lit                     false
% 2.80/0.97  --prop_solver_per_cl                    1000
% 2.80/0.97  --min_unsat_core                        false
% 2.80/0.97  --soft_assumptions                      false
% 2.80/0.97  --soft_lemma_size                       3
% 2.80/0.97  --prop_impl_unit_size                   0
% 2.80/0.97  --prop_impl_unit                        []
% 2.80/0.97  --share_sel_clauses                     true
% 2.80/0.97  --reset_solvers                         false
% 2.80/0.97  --bc_imp_inh                            [conj_cone]
% 2.80/0.97  --conj_cone_tolerance                   3.
% 2.80/0.97  --extra_neg_conj                        none
% 2.80/0.97  --large_theory_mode                     true
% 2.80/0.97  --prolific_symb_bound                   200
% 2.80/0.97  --lt_threshold                          2000
% 2.80/0.97  --clause_weak_htbl                      true
% 2.80/0.97  --gc_record_bc_elim                     false
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing Options
% 2.80/0.97  
% 2.80/0.97  --preprocessing_flag                    true
% 2.80/0.97  --time_out_prep_mult                    0.1
% 2.80/0.97  --splitting_mode                        input
% 2.80/0.97  --splitting_grd                         true
% 2.80/0.97  --splitting_cvd                         false
% 2.80/0.97  --splitting_cvd_svl                     false
% 2.80/0.97  --splitting_nvd                         32
% 2.80/0.97  --sub_typing                            true
% 2.80/0.97  --prep_gs_sim                           true
% 2.80/0.97  --prep_unflatten                        true
% 2.80/0.97  --prep_res_sim                          true
% 2.80/0.97  --prep_upred                            true
% 2.80/0.97  --prep_sem_filter                       exhaustive
% 2.80/0.97  --prep_sem_filter_out                   false
% 2.80/0.97  --pred_elim                             true
% 2.80/0.97  --res_sim_input                         true
% 2.80/0.97  --eq_ax_congr_red                       true
% 2.80/0.97  --pure_diseq_elim                       true
% 2.80/0.97  --brand_transform                       false
% 2.80/0.97  --non_eq_to_eq                          false
% 2.80/0.97  --prep_def_merge                        true
% 2.80/0.97  --prep_def_merge_prop_impl              false
% 2.80/0.97  --prep_def_merge_mbd                    true
% 2.80/0.97  --prep_def_merge_tr_red                 false
% 2.80/0.97  --prep_def_merge_tr_cl                  false
% 2.80/0.97  --smt_preprocessing                     true
% 2.80/0.97  --smt_ac_axioms                         fast
% 2.80/0.97  --preprocessed_out                      false
% 2.80/0.97  --preprocessed_stats                    false
% 2.80/0.97  
% 2.80/0.97  ------ Abstraction refinement Options
% 2.80/0.97  
% 2.80/0.97  --abstr_ref                             []
% 2.80/0.97  --abstr_ref_prep                        false
% 2.80/0.97  --abstr_ref_until_sat                   false
% 2.80/0.97  --abstr_ref_sig_restrict                funpre
% 2.80/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.97  --abstr_ref_under                       []
% 2.80/0.97  
% 2.80/0.97  ------ SAT Options
% 2.80/0.97  
% 2.80/0.97  --sat_mode                              false
% 2.80/0.97  --sat_fm_restart_options                ""
% 2.80/0.97  --sat_gr_def                            false
% 2.80/0.97  --sat_epr_types                         true
% 2.80/0.97  --sat_non_cyclic_types                  false
% 2.80/0.97  --sat_finite_models                     false
% 2.80/0.97  --sat_fm_lemmas                         false
% 2.80/0.97  --sat_fm_prep                           false
% 2.80/0.97  --sat_fm_uc_incr                        true
% 2.80/0.97  --sat_out_model                         small
% 2.80/0.97  --sat_out_clauses                       false
% 2.80/0.97  
% 2.80/0.97  ------ QBF Options
% 2.80/0.97  
% 2.80/0.97  --qbf_mode                              false
% 2.80/0.97  --qbf_elim_univ                         false
% 2.80/0.97  --qbf_dom_inst                          none
% 2.80/0.97  --qbf_dom_pre_inst                      false
% 2.80/0.97  --qbf_sk_in                             false
% 2.80/0.97  --qbf_pred_elim                         true
% 2.80/0.97  --qbf_split                             512
% 2.80/0.97  
% 2.80/0.97  ------ BMC1 Options
% 2.80/0.97  
% 2.80/0.97  --bmc1_incremental                      false
% 2.80/0.97  --bmc1_axioms                           reachable_all
% 2.80/0.97  --bmc1_min_bound                        0
% 2.80/0.97  --bmc1_max_bound                        -1
% 2.80/0.97  --bmc1_max_bound_default                -1
% 2.80/0.97  --bmc1_symbol_reachability              true
% 2.80/0.97  --bmc1_property_lemmas                  false
% 2.80/0.97  --bmc1_k_induction                      false
% 2.80/0.97  --bmc1_non_equiv_states                 false
% 2.80/0.97  --bmc1_deadlock                         false
% 2.80/0.97  --bmc1_ucm                              false
% 2.80/0.97  --bmc1_add_unsat_core                   none
% 2.80/0.97  --bmc1_unsat_core_children              false
% 2.80/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.97  --bmc1_out_stat                         full
% 2.80/0.97  --bmc1_ground_init                      false
% 2.80/0.97  --bmc1_pre_inst_next_state              false
% 2.80/0.97  --bmc1_pre_inst_state                   false
% 2.80/0.97  --bmc1_pre_inst_reach_state             false
% 2.80/0.97  --bmc1_out_unsat_core                   false
% 2.80/0.97  --bmc1_aig_witness_out                  false
% 2.80/0.97  --bmc1_verbose                          false
% 2.80/0.97  --bmc1_dump_clauses_tptp                false
% 2.80/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.97  --bmc1_dump_file                        -
% 2.80/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.97  --bmc1_ucm_extend_mode                  1
% 2.80/0.97  --bmc1_ucm_init_mode                    2
% 2.80/0.97  --bmc1_ucm_cone_mode                    none
% 2.80/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.97  --bmc1_ucm_relax_model                  4
% 2.80/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.97  --bmc1_ucm_layered_model                none
% 2.80/0.97  --bmc1_ucm_max_lemma_size               10
% 2.80/0.97  
% 2.80/0.97  ------ AIG Options
% 2.80/0.97  
% 2.80/0.97  --aig_mode                              false
% 2.80/0.97  
% 2.80/0.97  ------ Instantiation Options
% 2.80/0.97  
% 2.80/0.97  --instantiation_flag                    true
% 2.80/0.97  --inst_sos_flag                         false
% 2.80/0.97  --inst_sos_phase                        true
% 2.80/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel_side                     num_symb
% 2.80/0.97  --inst_solver_per_active                1400
% 2.80/0.97  --inst_solver_calls_frac                1.
% 2.80/0.97  --inst_passive_queue_type               priority_queues
% 2.80/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.97  --inst_passive_queues_freq              [25;2]
% 2.80/0.97  --inst_dismatching                      true
% 2.80/0.97  --inst_eager_unprocessed_to_passive     true
% 2.80/0.97  --inst_prop_sim_given                   true
% 2.80/0.97  --inst_prop_sim_new                     false
% 2.80/0.97  --inst_subs_new                         false
% 2.80/0.97  --inst_eq_res_simp                      false
% 2.80/0.97  --inst_subs_given                       false
% 2.80/0.97  --inst_orphan_elimination               true
% 2.80/0.97  --inst_learning_loop_flag               true
% 2.80/0.97  --inst_learning_start                   3000
% 2.80/0.97  --inst_learning_factor                  2
% 2.80/0.97  --inst_start_prop_sim_after_learn       3
% 2.80/0.97  --inst_sel_renew                        solver
% 2.80/0.97  --inst_lit_activity_flag                true
% 2.80/0.97  --inst_restr_to_given                   false
% 2.80/0.97  --inst_activity_threshold               500
% 2.80/0.97  --inst_out_proof                        true
% 2.80/0.97  
% 2.80/0.97  ------ Resolution Options
% 2.80/0.97  
% 2.80/0.97  --resolution_flag                       true
% 2.80/0.97  --res_lit_sel                           adaptive
% 2.80/0.97  --res_lit_sel_side                      none
% 2.80/0.97  --res_ordering                          kbo
% 2.80/0.97  --res_to_prop_solver                    active
% 2.80/0.97  --res_prop_simpl_new                    false
% 2.80/0.97  --res_prop_simpl_given                  true
% 2.80/0.97  --res_passive_queue_type                priority_queues
% 2.80/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.97  --res_passive_queues_freq               [15;5]
% 2.80/0.97  --res_forward_subs                      full
% 2.80/0.97  --res_backward_subs                     full
% 2.80/0.97  --res_forward_subs_resolution           true
% 2.80/0.97  --res_backward_subs_resolution          true
% 2.80/0.97  --res_orphan_elimination                true
% 2.80/0.97  --res_time_limit                        2.
% 2.80/0.97  --res_out_proof                         true
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Options
% 2.80/0.97  
% 2.80/0.97  --superposition_flag                    true
% 2.80/0.97  --sup_passive_queue_type                priority_queues
% 2.80/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.97  --demod_completeness_check              fast
% 2.80/0.97  --demod_use_ground                      true
% 2.80/0.97  --sup_to_prop_solver                    passive
% 2.80/0.97  --sup_prop_simpl_new                    true
% 2.80/0.97  --sup_prop_simpl_given                  true
% 2.80/0.97  --sup_fun_splitting                     false
% 2.80/0.97  --sup_smt_interval                      50000
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Simplification Setup
% 2.80/0.97  
% 2.80/0.97  --sup_indices_passive                   []
% 2.80/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_full_bw                           [BwDemod]
% 2.80/0.97  --sup_immed_triv                        [TrivRules]
% 2.80/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_immed_bw_main                     []
% 2.80/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  
% 2.80/0.97  ------ Combination Options
% 2.80/0.97  
% 2.80/0.97  --comb_res_mult                         3
% 2.80/0.97  --comb_sup_mult                         2
% 2.80/0.97  --comb_inst_mult                        10
% 2.80/0.97  
% 2.80/0.97  ------ Debug Options
% 2.80/0.97  
% 2.80/0.97  --dbg_backtrace                         false
% 2.80/0.97  --dbg_dump_prop_clauses                 false
% 2.80/0.97  --dbg_dump_prop_clauses_file            -
% 2.80/0.97  --dbg_out_stat                          false
% 2.80/0.97  ------ Parsing...
% 2.80/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/0.97  ------ Proving...
% 2.80/0.97  ------ Problem Properties 
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  clauses                                 23
% 2.80/0.97  conjectures                             4
% 2.80/0.97  EPR                                     3
% 2.80/0.97  Horn                                    15
% 2.80/0.97  unary                                   11
% 2.80/0.97  binary                                  2
% 2.80/0.97  lits                                    53
% 2.80/0.97  lits eq                                 45
% 2.80/0.97  fd_pure                                 0
% 2.80/0.97  fd_pseudo                               0
% 2.80/0.97  fd_cond                                 8
% 2.80/0.97  fd_pseudo_cond                          2
% 2.80/0.97  AC symbols                              0
% 2.80/0.97  
% 2.80/0.97  ------ Schedule dynamic 5 is on 
% 2.80/0.97  
% 2.80/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  ------ 
% 2.80/0.97  Current options:
% 2.80/0.97  ------ 
% 2.80/0.97  
% 2.80/0.97  ------ Input Options
% 2.80/0.97  
% 2.80/0.97  --out_options                           all
% 2.80/0.97  --tptp_safe_out                         true
% 2.80/0.97  --problem_path                          ""
% 2.80/0.97  --include_path                          ""
% 2.80/0.97  --clausifier                            res/vclausify_rel
% 2.80/0.97  --clausifier_options                    --mode clausify
% 2.80/0.97  --stdin                                 false
% 2.80/0.97  --stats_out                             all
% 2.80/0.97  
% 2.80/0.97  ------ General Options
% 2.80/0.97  
% 2.80/0.97  --fof                                   false
% 2.80/0.97  --time_out_real                         305.
% 2.80/0.97  --time_out_virtual                      -1.
% 2.80/0.97  --symbol_type_check                     false
% 2.80/0.97  --clausify_out                          false
% 2.80/0.97  --sig_cnt_out                           false
% 2.80/0.97  --trig_cnt_out                          false
% 2.80/0.97  --trig_cnt_out_tolerance                1.
% 2.80/0.97  --trig_cnt_out_sk_spl                   false
% 2.80/0.97  --abstr_cl_out                          false
% 2.80/0.97  
% 2.80/0.97  ------ Global Options
% 2.80/0.97  
% 2.80/0.97  --schedule                              default
% 2.80/0.97  --add_important_lit                     false
% 2.80/0.97  --prop_solver_per_cl                    1000
% 2.80/0.97  --min_unsat_core                        false
% 2.80/0.97  --soft_assumptions                      false
% 2.80/0.97  --soft_lemma_size                       3
% 2.80/0.97  --prop_impl_unit_size                   0
% 2.80/0.97  --prop_impl_unit                        []
% 2.80/0.97  --share_sel_clauses                     true
% 2.80/0.97  --reset_solvers                         false
% 2.80/0.97  --bc_imp_inh                            [conj_cone]
% 2.80/0.97  --conj_cone_tolerance                   3.
% 2.80/0.97  --extra_neg_conj                        none
% 2.80/0.97  --large_theory_mode                     true
% 2.80/0.97  --prolific_symb_bound                   200
% 2.80/0.97  --lt_threshold                          2000
% 2.80/0.97  --clause_weak_htbl                      true
% 2.80/0.97  --gc_record_bc_elim                     false
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing Options
% 2.80/0.97  
% 2.80/0.97  --preprocessing_flag                    true
% 2.80/0.97  --time_out_prep_mult                    0.1
% 2.80/0.97  --splitting_mode                        input
% 2.80/0.97  --splitting_grd                         true
% 2.80/0.97  --splitting_cvd                         false
% 2.80/0.97  --splitting_cvd_svl                     false
% 2.80/0.97  --splitting_nvd                         32
% 2.80/0.97  --sub_typing                            true
% 2.80/0.97  --prep_gs_sim                           true
% 2.80/0.97  --prep_unflatten                        true
% 2.80/0.97  --prep_res_sim                          true
% 2.80/0.97  --prep_upred                            true
% 2.80/0.97  --prep_sem_filter                       exhaustive
% 2.80/0.97  --prep_sem_filter_out                   false
% 2.80/0.97  --pred_elim                             true
% 2.80/0.97  --res_sim_input                         true
% 2.80/0.97  --eq_ax_congr_red                       true
% 2.80/0.97  --pure_diseq_elim                       true
% 2.80/0.97  --brand_transform                       false
% 2.80/0.97  --non_eq_to_eq                          false
% 2.80/0.97  --prep_def_merge                        true
% 2.80/0.97  --prep_def_merge_prop_impl              false
% 2.80/0.97  --prep_def_merge_mbd                    true
% 2.80/0.97  --prep_def_merge_tr_red                 false
% 2.80/0.97  --prep_def_merge_tr_cl                  false
% 2.80/0.97  --smt_preprocessing                     true
% 2.80/0.97  --smt_ac_axioms                         fast
% 2.80/0.97  --preprocessed_out                      false
% 2.80/0.97  --preprocessed_stats                    false
% 2.80/0.97  
% 2.80/0.97  ------ Abstraction refinement Options
% 2.80/0.97  
% 2.80/0.97  --abstr_ref                             []
% 2.80/0.97  --abstr_ref_prep                        false
% 2.80/0.97  --abstr_ref_until_sat                   false
% 2.80/0.97  --abstr_ref_sig_restrict                funpre
% 2.80/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.97  --abstr_ref_under                       []
% 2.80/0.97  
% 2.80/0.97  ------ SAT Options
% 2.80/0.97  
% 2.80/0.97  --sat_mode                              false
% 2.80/0.97  --sat_fm_restart_options                ""
% 2.80/0.97  --sat_gr_def                            false
% 2.80/0.97  --sat_epr_types                         true
% 2.80/0.97  --sat_non_cyclic_types                  false
% 2.80/0.97  --sat_finite_models                     false
% 2.80/0.97  --sat_fm_lemmas                         false
% 2.80/0.97  --sat_fm_prep                           false
% 2.80/0.97  --sat_fm_uc_incr                        true
% 2.80/0.97  --sat_out_model                         small
% 2.80/0.97  --sat_out_clauses                       false
% 2.80/0.97  
% 2.80/0.97  ------ QBF Options
% 2.80/0.97  
% 2.80/0.97  --qbf_mode                              false
% 2.80/0.97  --qbf_elim_univ                         false
% 2.80/0.97  --qbf_dom_inst                          none
% 2.80/0.97  --qbf_dom_pre_inst                      false
% 2.80/0.97  --qbf_sk_in                             false
% 2.80/0.97  --qbf_pred_elim                         true
% 2.80/0.97  --qbf_split                             512
% 2.80/0.97  
% 2.80/0.97  ------ BMC1 Options
% 2.80/0.97  
% 2.80/0.97  --bmc1_incremental                      false
% 2.80/0.97  --bmc1_axioms                           reachable_all
% 2.80/0.97  --bmc1_min_bound                        0
% 2.80/0.97  --bmc1_max_bound                        -1
% 2.80/0.97  --bmc1_max_bound_default                -1
% 2.80/0.97  --bmc1_symbol_reachability              true
% 2.80/0.97  --bmc1_property_lemmas                  false
% 2.80/0.97  --bmc1_k_induction                      false
% 2.80/0.97  --bmc1_non_equiv_states                 false
% 2.80/0.97  --bmc1_deadlock                         false
% 2.80/0.97  --bmc1_ucm                              false
% 2.80/0.97  --bmc1_add_unsat_core                   none
% 2.80/0.97  --bmc1_unsat_core_children              false
% 2.80/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.97  --bmc1_out_stat                         full
% 2.80/0.97  --bmc1_ground_init                      false
% 2.80/0.97  --bmc1_pre_inst_next_state              false
% 2.80/0.97  --bmc1_pre_inst_state                   false
% 2.80/0.97  --bmc1_pre_inst_reach_state             false
% 2.80/0.97  --bmc1_out_unsat_core                   false
% 2.80/0.97  --bmc1_aig_witness_out                  false
% 2.80/0.97  --bmc1_verbose                          false
% 2.80/0.97  --bmc1_dump_clauses_tptp                false
% 2.80/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.97  --bmc1_dump_file                        -
% 2.80/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.97  --bmc1_ucm_extend_mode                  1
% 2.80/0.97  --bmc1_ucm_init_mode                    2
% 2.80/0.97  --bmc1_ucm_cone_mode                    none
% 2.80/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.97  --bmc1_ucm_relax_model                  4
% 2.80/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.97  --bmc1_ucm_layered_model                none
% 2.80/0.97  --bmc1_ucm_max_lemma_size               10
% 2.80/0.97  
% 2.80/0.97  ------ AIG Options
% 2.80/0.97  
% 2.80/0.97  --aig_mode                              false
% 2.80/0.97  
% 2.80/0.97  ------ Instantiation Options
% 2.80/0.97  
% 2.80/0.97  --instantiation_flag                    true
% 2.80/0.97  --inst_sos_flag                         false
% 2.80/0.97  --inst_sos_phase                        true
% 2.80/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.97  --inst_lit_sel_side                     none
% 2.80/0.97  --inst_solver_per_active                1400
% 2.80/0.97  --inst_solver_calls_frac                1.
% 2.80/0.97  --inst_passive_queue_type               priority_queues
% 2.80/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.97  --inst_passive_queues_freq              [25;2]
% 2.80/0.97  --inst_dismatching                      true
% 2.80/0.97  --inst_eager_unprocessed_to_passive     true
% 2.80/0.97  --inst_prop_sim_given                   true
% 2.80/0.97  --inst_prop_sim_new                     false
% 2.80/0.97  --inst_subs_new                         false
% 2.80/0.97  --inst_eq_res_simp                      false
% 2.80/0.97  --inst_subs_given                       false
% 2.80/0.97  --inst_orphan_elimination               true
% 2.80/0.97  --inst_learning_loop_flag               true
% 2.80/0.97  --inst_learning_start                   3000
% 2.80/0.97  --inst_learning_factor                  2
% 2.80/0.97  --inst_start_prop_sim_after_learn       3
% 2.80/0.97  --inst_sel_renew                        solver
% 2.80/0.97  --inst_lit_activity_flag                true
% 2.80/0.97  --inst_restr_to_given                   false
% 2.80/0.97  --inst_activity_threshold               500
% 2.80/0.97  --inst_out_proof                        true
% 2.80/0.97  
% 2.80/0.97  ------ Resolution Options
% 2.80/0.97  
% 2.80/0.97  --resolution_flag                       false
% 2.80/0.97  --res_lit_sel                           adaptive
% 2.80/0.97  --res_lit_sel_side                      none
% 2.80/0.97  --res_ordering                          kbo
% 2.80/0.97  --res_to_prop_solver                    active
% 2.80/0.97  --res_prop_simpl_new                    false
% 2.80/0.97  --res_prop_simpl_given                  true
% 2.80/0.97  --res_passive_queue_type                priority_queues
% 2.80/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.97  --res_passive_queues_freq               [15;5]
% 2.80/0.97  --res_forward_subs                      full
% 2.80/0.97  --res_backward_subs                     full
% 2.80/0.97  --res_forward_subs_resolution           true
% 2.80/0.97  --res_backward_subs_resolution          true
% 2.80/0.97  --res_orphan_elimination                true
% 2.80/0.97  --res_time_limit                        2.
% 2.80/0.97  --res_out_proof                         true
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Options
% 2.80/0.97  
% 2.80/0.97  --superposition_flag                    true
% 2.80/0.97  --sup_passive_queue_type                priority_queues
% 2.80/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.97  --demod_completeness_check              fast
% 2.80/0.97  --demod_use_ground                      true
% 2.80/0.97  --sup_to_prop_solver                    passive
% 2.80/0.97  --sup_prop_simpl_new                    true
% 2.80/0.97  --sup_prop_simpl_given                  true
% 2.80/0.97  --sup_fun_splitting                     false
% 2.80/0.97  --sup_smt_interval                      50000
% 2.80/0.97  
% 2.80/0.97  ------ Superposition Simplification Setup
% 2.80/0.97  
% 2.80/0.97  --sup_indices_passive                   []
% 2.80/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_full_bw                           [BwDemod]
% 2.80/0.97  --sup_immed_triv                        [TrivRules]
% 2.80/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_immed_bw_main                     []
% 2.80/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.97  
% 2.80/0.97  ------ Combination Options
% 2.80/0.97  
% 2.80/0.97  --comb_res_mult                         3
% 2.80/0.97  --comb_sup_mult                         2
% 2.80/0.97  --comb_inst_mult                        10
% 2.80/0.97  
% 2.80/0.97  ------ Debug Options
% 2.80/0.97  
% 2.80/0.97  --dbg_backtrace                         false
% 2.80/0.97  --dbg_dump_prop_clauses                 false
% 2.80/0.97  --dbg_dump_prop_clauses_file            -
% 2.80/0.97  --dbg_out_stat                          false
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  ------ Proving...
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  % SZS status Theorem for theBenchmark.p
% 2.80/0.97  
% 2.80/0.97   Resolution empty clause
% 2.80/0.97  
% 2.80/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  fof(f1,axiom,(
% 2.80/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f18,plain,(
% 2.80/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.80/0.97    inference(nnf_transformation,[],[f1])).
% 2.80/0.97  
% 2.80/0.97  fof(f19,plain,(
% 2.80/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.80/0.97    inference(rectify,[],[f18])).
% 2.80/0.97  
% 2.80/0.97  fof(f20,plain,(
% 2.80/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f21,plain,(
% 2.80/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 2.80/0.97  
% 2.80/0.97  fof(f30,plain,(
% 2.80/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.80/0.97    inference(cnf_transformation,[],[f21])).
% 2.80/0.97  
% 2.80/0.97  fof(f62,plain,(
% 2.80/0.97    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.80/0.97    inference(equality_resolution,[],[f30])).
% 2.80/0.97  
% 2.80/0.97  fof(f63,plain,(
% 2.80/0.97    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.80/0.97    inference(equality_resolution,[],[f62])).
% 2.80/0.97  
% 2.80/0.97  fof(f7,axiom,(
% 2.80/0.97    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f14,plain,(
% 2.80/0.97    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.80/0.97    inference(ennf_transformation,[],[f7])).
% 2.80/0.97  
% 2.80/0.97  fof(f24,plain,(
% 2.80/0.97    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f25,plain,(
% 2.80/0.97    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 2.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f24])).
% 2.80/0.97  
% 2.80/0.97  fof(f41,plain,(
% 2.80/0.97    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f25])).
% 2.80/0.97  
% 2.80/0.97  fof(f29,plain,(
% 2.80/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.80/0.97    inference(cnf_transformation,[],[f21])).
% 2.80/0.97  
% 2.80/0.97  fof(f64,plain,(
% 2.80/0.97    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.80/0.97    inference(equality_resolution,[],[f29])).
% 2.80/0.97  
% 2.80/0.97  fof(f8,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f15,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.80/0.97    inference(ennf_transformation,[],[f8])).
% 2.80/0.97  
% 2.80/0.97  fof(f44,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f15])).
% 2.80/0.97  
% 2.80/0.97  fof(f4,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f37,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f4])).
% 2.80/0.97  
% 2.80/0.97  fof(f5,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f38,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.80/0.97    inference(cnf_transformation,[],[f5])).
% 2.80/0.97  
% 2.80/0.97  fof(f57,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(definition_unfolding,[],[f44,f37,f38])).
% 2.80/0.97  
% 2.80/0.97  fof(f11,conjecture,(
% 2.80/0.97    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f12,negated_conjecture,(
% 2.80/0.97    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.80/0.97    inference(negated_conjecture,[],[f11])).
% 2.80/0.97  
% 2.80/0.97  fof(f17,plain,(
% 2.80/0.97    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.80/0.97    inference(ennf_transformation,[],[f12])).
% 2.80/0.97  
% 2.80/0.97  fof(f27,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK5) = sK5 | k6_mcart_1(X0,X1,X2,sK5) = sK5 | k5_mcart_1(X0,X1,X2,sK5) = sK5) & m1_subset_1(sK5,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f26,plain,(
% 2.80/0.97    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK2,sK3,sK4,X3) = X3 | k6_mcart_1(sK2,sK3,sK4,X3) = X3 | k5_mcart_1(sK2,sK3,sK4,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2)),
% 2.80/0.97    introduced(choice_axiom,[])).
% 2.80/0.97  
% 2.80/0.97  fof(f28,plain,(
% 2.80/0.97    ((k7_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5) & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2),
% 2.80/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f27,f26])).
% 2.80/0.97  
% 2.80/0.97  fof(f53,plain,(
% 2.80/0.97    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))),
% 2.80/0.97    inference(cnf_transformation,[],[f28])).
% 2.80/0.97  
% 2.80/0.97  fof(f61,plain,(
% 2.80/0.97    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.80/0.97    inference(definition_unfolding,[],[f53,f38])).
% 2.80/0.97  
% 2.80/0.97  fof(f50,plain,(
% 2.80/0.97    k1_xboole_0 != sK2),
% 2.80/0.97    inference(cnf_transformation,[],[f28])).
% 2.80/0.97  
% 2.80/0.97  fof(f51,plain,(
% 2.80/0.97    k1_xboole_0 != sK3),
% 2.80/0.97    inference(cnf_transformation,[],[f28])).
% 2.80/0.97  
% 2.80/0.97  fof(f52,plain,(
% 2.80/0.97    k1_xboole_0 != sK4),
% 2.80/0.97    inference(cnf_transformation,[],[f28])).
% 2.80/0.97  
% 2.80/0.97  fof(f2,axiom,(
% 2.80/0.97    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f22,plain,(
% 2.80/0.97    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.80/0.97    inference(nnf_transformation,[],[f2])).
% 2.80/0.97  
% 2.80/0.97  fof(f23,plain,(
% 2.80/0.97    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.80/0.97    inference(flattening,[],[f22])).
% 2.80/0.97  
% 2.80/0.97  fof(f33,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f23])).
% 2.80/0.97  
% 2.80/0.97  fof(f34,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f23])).
% 2.80/0.97  
% 2.80/0.97  fof(f66,plain,(
% 2.80/0.97    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.80/0.97    inference(equality_resolution,[],[f34])).
% 2.80/0.97  
% 2.80/0.97  fof(f9,axiom,(
% 2.80/0.97    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f16,plain,(
% 2.80/0.97    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.80/0.97    inference(ennf_transformation,[],[f9])).
% 2.80/0.97  
% 2.80/0.97  fof(f47,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f16])).
% 2.80/0.97  
% 2.80/0.97  fof(f58,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(definition_unfolding,[],[f47,f38])).
% 2.80/0.97  
% 2.80/0.97  fof(f45,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f16])).
% 2.80/0.97  
% 2.80/0.97  fof(f60,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(definition_unfolding,[],[f45,f38])).
% 2.80/0.97  
% 2.80/0.97  fof(f46,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f16])).
% 2.80/0.97  
% 2.80/0.97  fof(f59,plain,(
% 2.80/0.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(definition_unfolding,[],[f46,f38])).
% 2.80/0.97  
% 2.80/0.97  fof(f10,axiom,(
% 2.80/0.97    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f48,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f10])).
% 2.80/0.97  
% 2.80/0.97  fof(f54,plain,(
% 2.80/0.97    k7_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5 | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5),
% 2.80/0.97    inference(cnf_transformation,[],[f28])).
% 2.80/0.97  
% 2.80/0.97  fof(f6,axiom,(
% 2.80/0.97    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f13,plain,(
% 2.80/0.97    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 2.80/0.97    inference(ennf_transformation,[],[f6])).
% 2.80/0.97  
% 2.80/0.97  fof(f40,plain,(
% 2.80/0.97    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f13])).
% 2.80/0.97  
% 2.80/0.97  fof(f67,plain,(
% 2.80/0.97    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 2.80/0.97    inference(equality_resolution,[],[f40])).
% 2.80/0.97  
% 2.80/0.97  fof(f49,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.80/0.97    inference(cnf_transformation,[],[f10])).
% 2.80/0.97  
% 2.80/0.97  fof(f42,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f25])).
% 2.80/0.97  
% 2.80/0.97  fof(f56,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(definition_unfolding,[],[f42,f37])).
% 2.80/0.97  
% 2.80/0.97  fof(f43,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(cnf_transformation,[],[f25])).
% 2.80/0.97  
% 2.80/0.97  fof(f55,plain,(
% 2.80/0.97    ( ! [X4,X2,X0,X3] : (k4_tarski(k4_tarski(X2,X3),X4) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 2.80/0.97    inference(definition_unfolding,[],[f43,f37])).
% 2.80/0.97  
% 2.80/0.97  fof(f35,plain,(
% 2.80/0.97    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.80/0.97    inference(cnf_transformation,[],[f23])).
% 2.80/0.97  
% 2.80/0.97  fof(f65,plain,(
% 2.80/0.97    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.80/0.97    inference(equality_resolution,[],[f35])).
% 2.80/0.97  
% 2.80/0.97  fof(f3,axiom,(
% 2.80/0.97    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.80/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.97  
% 2.80/0.97  fof(f36,plain,(
% 2.80/0.97    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.80/0.97    inference(cnf_transformation,[],[f3])).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2,plain,
% 2.80/0.97      ( r2_hidden(X0,k1_tarski(X0)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_836,plain,
% 2.80/0.97      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_12,plain,
% 2.80/0.97      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.80/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_831,plain,
% 2.80/0.97      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3,plain,
% 2.80/0.97      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 2.80/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_835,plain,
% 2.80/0.97      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2129,plain,
% 2.80/0.97      ( sK1(k1_tarski(X0)) = X0 | k1_tarski(X0) = k1_xboole_0 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_831,c_835]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_13,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.80/0.97      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 2.80/0.97      | k1_xboole_0 = X2
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | k1_xboole_0 = X3 ),
% 2.80/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_20,negated_conjecture,
% 2.80/0.97      ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_224,plain,
% 2.80/0.97      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 2.80/0.97      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 2.80/0.97      | sK5 != X3
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | k1_xboole_0 = X2
% 2.80/0.97      | k1_xboole_0 = X1 ),
% 2.80/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_225,plain,
% 2.80/0.97      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,sK5),k6_mcart_1(X0,X1,X2,sK5)),k7_mcart_1(X0,X1,X2,sK5)) = sK5
% 2.80/0.97      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | k1_xboole_0 = X2 ),
% 2.80/0.97      inference(unflattening,[status(thm)],[c_224]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1119,plain,
% 2.80/0.97      ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5
% 2.80/0.97      | sK4 = k1_xboole_0
% 2.80/0.97      | sK3 = k1_xboole_0
% 2.80/0.97      | sK2 = k1_xboole_0 ),
% 2.80/0.97      inference(equality_resolution,[status(thm)],[c_225]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_23,negated_conjecture,
% 2.80/0.97      ( k1_xboole_0 != sK2 ),
% 2.80/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_22,negated_conjecture,
% 2.80/0.97      ( k1_xboole_0 != sK3 ),
% 2.80/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_21,negated_conjecture,
% 2.80/0.97      ( k1_xboole_0 != sK4 ),
% 2.80/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_6,plain,
% 2.80/0.97      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | k1_xboole_0 = X0 ),
% 2.80/0.97      inference(cnf_transformation,[],[f33]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_51,plain,
% 2.80/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.80/0.97      | k1_xboole_0 = k1_xboole_0 ),
% 2.80/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_5,plain,
% 2.80/0.97      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.80/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_52,plain,
% 2.80/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.80/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_683,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1016,plain,
% 2.80/0.97      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.80/0.97      inference(instantiation,[status(thm)],[c_683]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1017,plain,
% 2.80/0.97      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.80/0.97      inference(instantiation,[status(thm)],[c_1016]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1018,plain,
% 2.80/0.97      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.80/0.97      inference(instantiation,[status(thm)],[c_683]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1019,plain,
% 2.80/0.97      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.80/0.97      inference(instantiation,[status(thm)],[c_1018]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1020,plain,
% 2.80/0.97      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.80/0.97      inference(instantiation,[status(thm)],[c_683]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1021,plain,
% 2.80/0.97      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 2.80/0.97      inference(instantiation,[status(thm)],[c_1020]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1430,plain,
% 2.80/0.97      ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) = sK5 ),
% 2.80/0.97      inference(global_propositional_subsumption,
% 2.80/0.97                [status(thm)],
% 2.80/0.97                [c_1119,c_23,c_22,c_21,c_51,c_52,c_1017,c_1019,c_1021]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_14,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.80/0.97      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.80/0.97      | k1_xboole_0 = X2
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | k1_xboole_0 = X3 ),
% 2.80/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_206,plain,
% 2.80/0.97      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.80/0.97      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 2.80/0.97      | sK5 != X3
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | k1_xboole_0 = X2
% 2.80/0.97      | k1_xboole_0 = X1 ),
% 2.80/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_207,plain,
% 2.80/0.97      ( k7_mcart_1(X0,X1,X2,sK5) = k2_mcart_1(sK5)
% 2.80/0.97      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | k1_xboole_0 = X2 ),
% 2.80/0.97      inference(unflattening,[status(thm)],[c_206]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1071,plain,
% 2.80/0.97      ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)
% 2.80/0.97      | sK4 = k1_xboole_0
% 2.80/0.97      | sK3 = k1_xboole_0
% 2.80/0.97      | sK2 = k1_xboole_0 ),
% 2.80/0.97      inference(equality_resolution,[status(thm)],[c_207]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1356,plain,
% 2.80/0.97      ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) ),
% 2.80/0.97      inference(global_propositional_subsumption,
% 2.80/0.97                [status(thm)],
% 2.80/0.97                [c_1071,c_23,c_22,c_21,c_51,c_52,c_1017,c_1019,c_1021]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_16,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.80/0.97      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.80/0.97      | k1_xboole_0 = X2
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | k1_xboole_0 = X3 ),
% 2.80/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_170,plain,
% 2.80/0.97      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.80/0.97      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 2.80/0.97      | sK5 != X3
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | k1_xboole_0 = X2
% 2.80/0.97      | k1_xboole_0 = X1 ),
% 2.80/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_171,plain,
% 2.80/0.97      ( k5_mcart_1(X0,X1,X2,sK5) = k1_mcart_1(k1_mcart_1(sK5))
% 2.80/0.97      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | k1_xboole_0 = X2 ),
% 2.80/0.97      inference(unflattening,[status(thm)],[c_170]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1077,plain,
% 2.80/0.97      ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))
% 2.80/0.97      | sK4 = k1_xboole_0
% 2.80/0.97      | sK3 = k1_xboole_0
% 2.80/0.97      | sK2 = k1_xboole_0 ),
% 2.80/0.97      inference(equality_resolution,[status(thm)],[c_171]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1394,plain,
% 2.80/0.97      ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) ),
% 2.80/0.97      inference(global_propositional_subsumption,
% 2.80/0.97                [status(thm)],
% 2.80/0.97                [c_1077,c_23,c_22,c_21,c_51,c_52,c_1017,c_1019,c_1021]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_15,plain,
% 2.80/0.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.80/0.97      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.80/0.97      | k1_xboole_0 = X2
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | k1_xboole_0 = X3 ),
% 2.80/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_188,plain,
% 2.80/0.97      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.80/0.97      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 2.80/0.97      | sK5 != X3
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | k1_xboole_0 = X2
% 2.80/0.97      | k1_xboole_0 = X1 ),
% 2.80/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_189,plain,
% 2.80/0.97      ( k6_mcart_1(X0,X1,X2,sK5) = k2_mcart_1(k1_mcart_1(sK5))
% 2.80/0.97      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | k1_xboole_0 = X2 ),
% 2.80/0.97      inference(unflattening,[status(thm)],[c_188]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1113,plain,
% 2.80/0.97      ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))
% 2.80/0.97      | sK4 = k1_xboole_0
% 2.80/0.97      | sK3 = k1_xboole_0
% 2.80/0.97      | sK2 = k1_xboole_0 ),
% 2.80/0.97      inference(equality_resolution,[status(thm)],[c_189]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1424,plain,
% 2.80/0.97      ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
% 2.80/0.97      inference(global_propositional_subsumption,
% 2.80/0.97                [status(thm)],
% 2.80/0.97                [c_1113,c_23,c_22,c_21,c_51,c_52,c_1017,c_1019,c_1021]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1432,plain,
% 2.80/0.97      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5 ),
% 2.80/0.97      inference(light_normalisation,
% 2.80/0.97                [status(thm)],
% 2.80/0.97                [c_1430,c_1356,c_1394,c_1424]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_18,plain,
% 2.80/0.97      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 2.80/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1434,plain,
% 2.80/0.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5) ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_1432,c_18]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1470,plain,
% 2.80/0.97      ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5 ),
% 2.80/0.97      inference(demodulation,[status(thm)],[c_1434,c_1432]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_19,negated_conjecture,
% 2.80/0.97      ( k7_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 2.80/0.97      | k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 2.80/0.97      | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5 ),
% 2.80/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1359,plain,
% 2.80/0.97      ( k6_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 2.80/0.97      | k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 2.80/0.97      | k2_mcart_1(sK5) = sK5 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_19,c_1356]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1427,plain,
% 2.80/0.97      ( k5_mcart_1(sK2,sK3,sK4,sK5) = sK5
% 2.80/0.97      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 2.80/0.97      | k2_mcart_1(sK5) = sK5 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_1359,c_1424]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1429,plain,
% 2.80/0.97      ( k1_mcart_1(k1_mcart_1(sK5)) = sK5
% 2.80/0.97      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 2.80/0.97      | k2_mcart_1(sK5) = sK5 ),
% 2.80/0.97      inference(demodulation,[status(thm)],[c_1427,c_1394]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1468,plain,
% 2.80/0.97      ( k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5
% 2.80/0.97      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 2.80/0.97      | k2_mcart_1(sK5) = sK5 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_1429,c_1432]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_8,plain,
% 2.80/0.97      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 2.80/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_17,plain,
% 2.80/0.97      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 2.80/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_860,plain,
% 2.80/0.97      ( k4_tarski(X0,X1) != X1 ),
% 2.80/0.97      inference(light_normalisation,[status(thm)],[c_8,c_17]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1684,plain,
% 2.80/0.97      ( k2_mcart_1(sK5) != sK5 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_1470,c_860]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1825,plain,
% 2.80/0.97      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 2.80/0.97      | k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5 ),
% 2.80/0.97      inference(global_propositional_subsumption,[status(thm)],[c_1468,c_1684]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1826,plain,
% 2.80/0.97      ( k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) = sK5
% 2.80/0.97      | k2_mcart_1(k1_mcart_1(sK5)) = sK5 ),
% 2.80/0.97      inference(renaming,[status(thm)],[c_1825]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_11,plain,
% 2.80/0.97      ( ~ r2_hidden(X0,X1)
% 2.80/0.97      | k4_tarski(k4_tarski(X0,X2),X3) != sK1(X1)
% 2.80/0.97      | k1_xboole_0 = X1 ),
% 2.80/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_832,plain,
% 2.80/0.97      ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
% 2.80/0.97      | k1_xboole_0 = X3
% 2.80/0.97      | r2_hidden(X0,X3) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_1834,plain,
% 2.80/0.97      ( sK1(X0) != sK5
% 2.80/0.97      | k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | r2_hidden(sK5,X0) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_1826,c_832]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2364,plain,
% 2.80/0.97      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 2.80/0.97      | k1_tarski(X0) = k1_xboole_0
% 2.80/0.97      | sK5 != X0
% 2.80/0.97      | r2_hidden(sK5,k1_tarski(X0)) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_2129,c_1834]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3193,plain,
% 2.80/0.97      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5
% 2.80/0.97      | k1_tarski(X0) = k1_xboole_0
% 2.80/0.97      | r2_hidden(sK5,k1_tarski(X0)) != iProver_top ),
% 2.80/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_2364,c_835]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3197,plain,
% 2.80/0.97      ( k2_mcart_1(k1_mcart_1(sK5)) = sK5 | k1_tarski(sK5) = k1_xboole_0 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_836,c_3193]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3377,plain,
% 2.80/0.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5) = k1_mcart_1(sK5)
% 2.80/0.97      | k1_tarski(sK5) = k1_xboole_0 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_3197,c_1434]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_10,plain,
% 2.80/0.97      ( ~ r2_hidden(X0,X1)
% 2.80/0.97      | k4_tarski(k4_tarski(X2,X0),X3) != sK1(X1)
% 2.80/0.97      | k1_xboole_0 = X1 ),
% 2.80/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_833,plain,
% 2.80/0.97      ( k4_tarski(k4_tarski(X0,X1),X2) != sK1(X3)
% 2.80/0.97      | k1_xboole_0 = X3
% 2.80/0.97      | r2_hidden(X1,X3) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3522,plain,
% 2.80/0.97      ( k4_tarski(k1_mcart_1(sK5),X0) != sK1(X1)
% 2.80/0.97      | k1_tarski(sK5) = k1_xboole_0
% 2.80/0.97      | k1_xboole_0 = X1
% 2.80/0.97      | r2_hidden(sK5,X1) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_3377,c_833]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3702,plain,
% 2.80/0.97      ( sK1(X0) != sK5
% 2.80/0.97      | k1_tarski(sK5) = k1_xboole_0
% 2.80/0.97      | k1_xboole_0 = X0
% 2.80/0.97      | r2_hidden(sK5,X0) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_1470,c_3522]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3718,plain,
% 2.80/0.97      ( k1_tarski(X0) = k1_xboole_0
% 2.80/0.97      | k1_tarski(sK5) = k1_xboole_0
% 2.80/0.97      | sK5 != X0
% 2.80/0.97      | r2_hidden(sK5,k1_tarski(X0)) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_2129,c_3702]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3806,plain,
% 2.80/0.97      ( k1_tarski(X0) = k1_xboole_0
% 2.80/0.97      | k1_tarski(sK5) = k1_xboole_0
% 2.80/0.97      | r2_hidden(sK5,k1_tarski(X0)) != iProver_top ),
% 2.80/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_3718,c_835]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3810,plain,
% 2.80/0.97      ( k1_tarski(sK5) = k1_xboole_0 ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_836,c_3806]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_3979,plain,
% 2.80/0.97      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_3810,c_836]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_4,plain,
% 2.80/0.97      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.80/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_7,plain,
% 2.80/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.80/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_834,plain,
% 2.80/0.97      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.80/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_2081,plain,
% 2.80/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.80/0.97      inference(superposition,[status(thm)],[c_4,c_834]) ).
% 2.80/0.97  
% 2.80/0.97  cnf(c_4075,plain,
% 2.80/0.97      ( $false ),
% 2.80/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_3979,c_2081]) ).
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/0.97  
% 2.80/0.97  ------                               Statistics
% 2.80/0.97  
% 2.80/0.97  ------ General
% 2.80/0.97  
% 2.80/0.97  abstr_ref_over_cycles:                  0
% 2.80/0.97  abstr_ref_under_cycles:                 0
% 2.80/0.97  gc_basic_clause_elim:                   0
% 2.80/0.97  forced_gc_time:                         0
% 2.80/0.97  parsing_time:                           0.009
% 2.80/0.97  unif_index_cands_time:                  0.
% 2.80/0.97  unif_index_add_time:                    0.
% 2.80/0.97  orderings_time:                         0.
% 2.80/0.97  out_proof_time:                         0.008
% 2.80/0.97  total_time:                             0.165
% 2.80/0.97  num_of_symbols:                         48
% 2.80/0.97  num_of_terms:                           4876
% 2.80/0.97  
% 2.80/0.97  ------ Preprocessing
% 2.80/0.97  
% 2.80/0.97  num_of_splits:                          0
% 2.80/0.97  num_of_split_atoms:                     0
% 2.80/0.97  num_of_reused_defs:                     0
% 2.80/0.97  num_eq_ax_congr_red:                    12
% 2.80/0.97  num_of_sem_filtered_clauses:            1
% 2.80/0.97  num_of_subtypes:                        0
% 2.80/0.97  monotx_restored_types:                  0
% 2.80/0.97  sat_num_of_epr_types:                   0
% 2.80/0.97  sat_num_of_non_cyclic_types:            0
% 2.80/0.97  sat_guarded_non_collapsed_types:        0
% 2.80/0.97  num_pure_diseq_elim:                    0
% 2.80/0.97  simp_replaced_by:                       0
% 2.80/0.97  res_preprocessed:                       114
% 2.80/0.97  prep_upred:                             0
% 2.80/0.97  prep_unflattend:                        48
% 2.80/0.97  smt_new_axioms:                         0
% 2.80/0.97  pred_elim_cands:                        1
% 2.80/0.97  pred_elim:                              1
% 2.80/0.97  pred_elim_cl:                           1
% 2.80/0.97  pred_elim_cycles:                       3
% 2.80/0.97  merged_defs:                            0
% 2.80/0.97  merged_defs_ncl:                        0
% 2.80/0.97  bin_hyper_res:                          0
% 2.80/0.97  prep_cycles:                            4
% 2.80/0.97  pred_elim_time:                         0.008
% 2.80/0.97  splitting_time:                         0.
% 2.80/0.97  sem_filter_time:                        0.
% 2.80/0.97  monotx_time:                            0.001
% 2.80/0.97  subtype_inf_time:                       0.
% 2.80/0.97  
% 2.80/0.97  ------ Problem properties
% 2.80/0.97  
% 2.80/0.97  clauses:                                23
% 2.80/0.97  conjectures:                            4
% 2.80/0.97  epr:                                    3
% 2.80/0.97  horn:                                   15
% 2.80/0.97  ground:                                 4
% 2.80/0.97  unary:                                  11
% 2.80/0.97  binary:                                 2
% 2.80/0.97  lits:                                   53
% 2.80/0.97  lits_eq:                                45
% 2.80/0.97  fd_pure:                                0
% 2.80/0.97  fd_pseudo:                              0
% 2.80/0.97  fd_cond:                                8
% 2.80/0.97  fd_pseudo_cond:                         2
% 2.80/0.97  ac_symbols:                             0
% 2.80/0.97  
% 2.80/0.97  ------ Propositional Solver
% 2.80/0.97  
% 2.80/0.97  prop_solver_calls:                      27
% 2.80/0.97  prop_fast_solver_calls:                 923
% 2.80/0.97  smt_solver_calls:                       0
% 2.80/0.97  smt_fast_solver_calls:                  0
% 2.80/0.97  prop_num_of_clauses:                    1660
% 2.80/0.97  prop_preprocess_simplified:             4819
% 2.80/0.97  prop_fo_subsumed:                       18
% 2.80/0.97  prop_solver_time:                       0.
% 2.80/0.97  smt_solver_time:                        0.
% 2.80/0.97  smt_fast_solver_time:                   0.
% 2.80/0.97  prop_fast_solver_time:                  0.
% 2.80/0.97  prop_unsat_core_time:                   0.
% 2.80/0.97  
% 2.80/0.97  ------ QBF
% 2.80/0.97  
% 2.80/0.97  qbf_q_res:                              0
% 2.80/0.97  qbf_num_tautologies:                    0
% 2.80/0.97  qbf_prep_cycles:                        0
% 2.80/0.97  
% 2.80/0.97  ------ BMC1
% 2.80/0.97  
% 2.80/0.97  bmc1_current_bound:                     -1
% 2.80/0.97  bmc1_last_solved_bound:                 -1
% 2.80/0.97  bmc1_unsat_core_size:                   -1
% 2.80/0.97  bmc1_unsat_core_parents_size:           -1
% 2.80/0.97  bmc1_merge_next_fun:                    0
% 2.80/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.80/0.97  
% 2.80/0.97  ------ Instantiation
% 2.80/0.97  
% 2.80/0.97  inst_num_of_clauses:                    754
% 2.80/0.97  inst_num_in_passive:                    177
% 2.80/0.97  inst_num_in_active:                     413
% 2.80/0.97  inst_num_in_unprocessed:                164
% 2.80/0.97  inst_num_of_loops:                      420
% 2.80/0.97  inst_num_of_learning_restarts:          0
% 2.80/0.97  inst_num_moves_active_passive:          6
% 2.80/0.97  inst_lit_activity:                      0
% 2.80/0.97  inst_lit_activity_moves:                0
% 2.80/0.97  inst_num_tautologies:                   0
% 2.80/0.97  inst_num_prop_implied:                  0
% 2.80/0.97  inst_num_existing_simplified:           0
% 2.80/0.97  inst_num_eq_res_simplified:             0
% 2.80/0.97  inst_num_child_elim:                    0
% 2.80/0.97  inst_num_of_dismatching_blockings:      96
% 2.80/0.97  inst_num_of_non_proper_insts:           911
% 2.80/0.97  inst_num_of_duplicates:                 0
% 2.80/0.97  inst_inst_num_from_inst_to_res:         0
% 2.80/0.97  inst_dismatching_checking_time:         0.
% 2.80/0.97  
% 2.80/0.97  ------ Resolution
% 2.80/0.97  
% 2.80/0.97  res_num_of_clauses:                     0
% 2.80/0.97  res_num_in_passive:                     0
% 2.80/0.97  res_num_in_active:                      0
% 2.80/0.97  res_num_of_loops:                       118
% 2.80/0.97  res_forward_subset_subsumed:            40
% 2.80/0.97  res_backward_subset_subsumed:           0
% 2.80/0.97  res_forward_subsumed:                   0
% 2.80/0.97  res_backward_subsumed:                  0
% 2.80/0.97  res_forward_subsumption_resolution:     0
% 2.80/0.97  res_backward_subsumption_resolution:    0
% 2.80/0.97  res_clause_to_clause_subsumption:       507
% 2.80/0.97  res_orphan_elimination:                 0
% 2.80/0.97  res_tautology_del:                      15
% 2.80/0.97  res_num_eq_res_simplified:              0
% 2.80/0.97  res_num_sel_changes:                    0
% 2.80/0.97  res_moves_from_active_to_pass:          0
% 2.80/0.97  
% 2.80/0.97  ------ Superposition
% 2.80/0.97  
% 2.80/0.97  sup_time_total:                         0.
% 2.80/0.97  sup_time_generating:                    0.
% 2.80/0.97  sup_time_sim_full:                      0.
% 2.80/0.97  sup_time_sim_immed:                     0.
% 2.80/0.97  
% 2.80/0.97  sup_num_of_clauses:                     90
% 2.80/0.97  sup_num_in_active:                      75
% 2.80/0.97  sup_num_in_passive:                     15
% 2.80/0.97  sup_num_of_loops:                       82
% 2.80/0.97  sup_fw_superposition:                   62
% 2.80/0.97  sup_bw_superposition:                   81
% 2.80/0.97  sup_immediate_simplified:               45
% 2.80/0.97  sup_given_eliminated:                   0
% 2.80/0.97  comparisons_done:                       0
% 2.80/0.97  comparisons_avoided:                    27
% 2.80/0.97  
% 2.80/0.97  ------ Simplifications
% 2.80/0.97  
% 2.80/0.97  
% 2.80/0.97  sim_fw_subset_subsumed:                 26
% 2.80/0.97  sim_bw_subset_subsumed:                 4
% 2.80/0.97  sim_fw_subsumed:                        16
% 2.80/0.97  sim_bw_subsumed:                        2
% 2.80/0.97  sim_fw_subsumption_res:                 7
% 2.80/0.97  sim_bw_subsumption_res:                 0
% 2.80/0.97  sim_tautology_del:                      0
% 2.80/0.97  sim_eq_tautology_del:                   18
% 2.80/0.97  sim_eq_res_simp:                        0
% 2.80/0.97  sim_fw_demodulated:                     1
% 2.80/0.97  sim_bw_demodulated:                     4
% 2.80/0.97  sim_light_normalised:                   5
% 2.80/0.97  sim_joinable_taut:                      0
% 2.80/0.97  sim_joinable_simp:                      0
% 2.80/0.97  sim_ac_normalised:                      0
% 2.80/0.97  sim_smt_subsumption:                    0
% 2.80/0.97  
%------------------------------------------------------------------------------
