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
% DateTime   : Thu Dec  3 11:59:14 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :  145 (1550 expanded)
%              Number of clauses        :   91 ( 489 expanded)
%              Number of leaves         :   15 ( 440 expanded)
%              Depth                    :   25
%              Number of atoms          :  446 (7658 expanded)
%              Number of equality atoms :  192 (1223 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
            | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
            | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
          & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5)
          | ~ r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4)
          | ~ r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3) )
        & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5))
        & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
              & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X2)) )
     => ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6)
              | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
              | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
            & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6))
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & m1_subset_1(sK6,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5)
                  | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5))
                & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK5,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
                  & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f29,f28,f27,f26])).

fof(f49,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f49,f40])).

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

fof(f20,plain,(
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

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f51,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f50,f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
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

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1368,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1373,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3632,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1368,c_1373])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1372,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5759,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1368,c_1372])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1371,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3639,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1368,c_1371])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1370,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3919,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3639,c_1370])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1524,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1525,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1524])).

cnf(c_1614,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1618,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1614])).

cnf(c_4930,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3919,c_24,c_1525,c_1618])).

cnf(c_4931,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4930])).

cnf(c_6260,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5759,c_4931])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1615,plain,
    ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1616,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1615])).

cnf(c_6528,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6260,c_24,c_1525,c_1616])).

cnf(c_6529,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_6528])).

cnf(c_6536,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_6529])).

cnf(c_1521,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6537,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6536])).

cnf(c_6539,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6536,c_24,c_1522])).

cnf(c_6540,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6539])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1367,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_154,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_155,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_155,c_8])).

cnf(c_1364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_5740,plain,
    ( r2_hidden(sK3,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_1364])).

cnf(c_6545,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k1_xboole_0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6540,c_5740])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_326,plain,
    ( ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_327,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_421,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | v1_xboole_0(k1_xboole_0)
    | X2 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_327])).

cnf(c_422,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_308,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_309,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_430,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_422,c_309])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1377,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1379,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1892,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1379])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_155,c_5])).

cnf(c_1363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_2939,plain,
    ( r1_xboole_0(sK6,sK3) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_1363])).

cnf(c_1522,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1521])).

cnf(c_1583,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1584,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_3663,plain,
    ( r1_xboole_0(sK6,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2939,c_24,c_1522,c_1584])).

cnf(c_8112,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1892,c_3663])).

cnf(c_11476,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6540,c_8112])).

cnf(c_11477,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11476])).

cnf(c_12004,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6545,c_432,c_11476])).

cnf(c_12005,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_12004])).

cnf(c_12014,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12005,c_1370])).

cnf(c_432,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1366,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2940,plain,
    ( r1_xboole_0(sK5,sK2) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1363])).

cnf(c_1778,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1779,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1778])).

cnf(c_3782,plain,
    ( r1_xboole_0(sK5,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2940,c_24,c_1525,c_1616,c_1779])).

cnf(c_8113,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1892,c_3782])).

cnf(c_12008,plain,
    ( sK1 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12005,c_8113])).

cnf(c_12052,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12014,c_432,c_12008])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1365,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2941,plain,
    ( r1_xboole_0(sK4,sK1) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_1363])).

cnf(c_1762,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1763,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_3790,plain,
    ( r1_xboole_0(sK4,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2941,c_24,c_1525,c_1618,c_1763])).

cnf(c_8114,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1892,c_3790])).

cnf(c_12055,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12052,c_8114])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12055,c_432])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:30:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.57/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/0.99  
% 2.57/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.57/0.99  
% 2.57/0.99  ------  iProver source info
% 2.57/0.99  
% 2.57/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.57/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.57/0.99  git: non_committed_changes: false
% 2.57/0.99  git: last_make_outside_of_git: false
% 2.57/0.99  
% 2.57/0.99  ------ 
% 2.57/0.99  
% 2.57/0.99  ------ Input Options
% 2.57/0.99  
% 2.57/0.99  --out_options                           all
% 2.57/0.99  --tptp_safe_out                         true
% 2.57/0.99  --problem_path                          ""
% 2.57/0.99  --include_path                          ""
% 2.57/0.99  --clausifier                            res/vclausify_rel
% 2.57/0.99  --clausifier_options                    --mode clausify
% 2.57/0.99  --stdin                                 false
% 2.57/0.99  --stats_out                             all
% 2.57/0.99  
% 2.57/0.99  ------ General Options
% 2.57/0.99  
% 2.57/0.99  --fof                                   false
% 2.57/0.99  --time_out_real                         305.
% 2.57/0.99  --time_out_virtual                      -1.
% 2.57/0.99  --symbol_type_check                     false
% 2.57/0.99  --clausify_out                          false
% 2.57/0.99  --sig_cnt_out                           false
% 2.57/0.99  --trig_cnt_out                          false
% 2.57/0.99  --trig_cnt_out_tolerance                1.
% 2.57/0.99  --trig_cnt_out_sk_spl                   false
% 2.57/0.99  --abstr_cl_out                          false
% 2.57/0.99  
% 2.57/0.99  ------ Global Options
% 2.57/0.99  
% 2.57/0.99  --schedule                              default
% 2.57/0.99  --add_important_lit                     false
% 2.57/0.99  --prop_solver_per_cl                    1000
% 2.57/0.99  --min_unsat_core                        false
% 2.57/0.99  --soft_assumptions                      false
% 2.57/0.99  --soft_lemma_size                       3
% 2.57/0.99  --prop_impl_unit_size                   0
% 2.57/0.99  --prop_impl_unit                        []
% 2.57/0.99  --share_sel_clauses                     true
% 2.57/0.99  --reset_solvers                         false
% 2.57/0.99  --bc_imp_inh                            [conj_cone]
% 2.57/0.99  --conj_cone_tolerance                   3.
% 2.57/0.99  --extra_neg_conj                        none
% 2.57/0.99  --large_theory_mode                     true
% 2.57/0.99  --prolific_symb_bound                   200
% 2.57/0.99  --lt_threshold                          2000
% 2.57/0.99  --clause_weak_htbl                      true
% 2.57/0.99  --gc_record_bc_elim                     false
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing Options
% 2.57/0.99  
% 2.57/0.99  --preprocessing_flag                    true
% 2.57/0.99  --time_out_prep_mult                    0.1
% 2.57/0.99  --splitting_mode                        input
% 2.57/0.99  --splitting_grd                         true
% 2.57/0.99  --splitting_cvd                         false
% 2.57/0.99  --splitting_cvd_svl                     false
% 2.57/0.99  --splitting_nvd                         32
% 2.57/0.99  --sub_typing                            true
% 2.57/0.99  --prep_gs_sim                           true
% 2.57/0.99  --prep_unflatten                        true
% 2.57/0.99  --prep_res_sim                          true
% 2.57/0.99  --prep_upred                            true
% 2.57/0.99  --prep_sem_filter                       exhaustive
% 2.57/0.99  --prep_sem_filter_out                   false
% 2.57/0.99  --pred_elim                             true
% 2.57/0.99  --res_sim_input                         true
% 2.57/0.99  --eq_ax_congr_red                       true
% 2.57/0.99  --pure_diseq_elim                       true
% 2.57/0.99  --brand_transform                       false
% 2.57/0.99  --non_eq_to_eq                          false
% 2.57/0.99  --prep_def_merge                        true
% 2.57/0.99  --prep_def_merge_prop_impl              false
% 2.57/0.99  --prep_def_merge_mbd                    true
% 2.57/0.99  --prep_def_merge_tr_red                 false
% 2.57/0.99  --prep_def_merge_tr_cl                  false
% 2.57/0.99  --smt_preprocessing                     true
% 2.57/0.99  --smt_ac_axioms                         fast
% 2.57/0.99  --preprocessed_out                      false
% 2.57/0.99  --preprocessed_stats                    false
% 2.57/0.99  
% 2.57/0.99  ------ Abstraction refinement Options
% 2.57/0.99  
% 2.57/0.99  --abstr_ref                             []
% 2.57/0.99  --abstr_ref_prep                        false
% 2.57/0.99  --abstr_ref_until_sat                   false
% 2.57/0.99  --abstr_ref_sig_restrict                funpre
% 2.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/0.99  --abstr_ref_under                       []
% 2.57/0.99  
% 2.57/0.99  ------ SAT Options
% 2.57/0.99  
% 2.57/0.99  --sat_mode                              false
% 2.57/0.99  --sat_fm_restart_options                ""
% 2.57/0.99  --sat_gr_def                            false
% 2.57/0.99  --sat_epr_types                         true
% 2.57/0.99  --sat_non_cyclic_types                  false
% 2.57/0.99  --sat_finite_models                     false
% 2.57/0.99  --sat_fm_lemmas                         false
% 2.57/0.99  --sat_fm_prep                           false
% 2.57/0.99  --sat_fm_uc_incr                        true
% 2.57/0.99  --sat_out_model                         small
% 2.57/0.99  --sat_out_clauses                       false
% 2.57/0.99  
% 2.57/0.99  ------ QBF Options
% 2.57/0.99  
% 2.57/0.99  --qbf_mode                              false
% 2.57/0.99  --qbf_elim_univ                         false
% 2.57/0.99  --qbf_dom_inst                          none
% 2.57/0.99  --qbf_dom_pre_inst                      false
% 2.57/0.99  --qbf_sk_in                             false
% 2.57/0.99  --qbf_pred_elim                         true
% 2.57/0.99  --qbf_split                             512
% 2.57/0.99  
% 2.57/0.99  ------ BMC1 Options
% 2.57/0.99  
% 2.57/0.99  --bmc1_incremental                      false
% 2.57/0.99  --bmc1_axioms                           reachable_all
% 2.57/0.99  --bmc1_min_bound                        0
% 2.57/0.99  --bmc1_max_bound                        -1
% 2.57/0.99  --bmc1_max_bound_default                -1
% 2.57/0.99  --bmc1_symbol_reachability              true
% 2.57/0.99  --bmc1_property_lemmas                  false
% 2.57/0.99  --bmc1_k_induction                      false
% 2.57/0.99  --bmc1_non_equiv_states                 false
% 2.57/0.99  --bmc1_deadlock                         false
% 2.57/0.99  --bmc1_ucm                              false
% 2.57/0.99  --bmc1_add_unsat_core                   none
% 2.57/0.99  --bmc1_unsat_core_children              false
% 2.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/0.99  --bmc1_out_stat                         full
% 2.57/0.99  --bmc1_ground_init                      false
% 2.57/0.99  --bmc1_pre_inst_next_state              false
% 2.57/0.99  --bmc1_pre_inst_state                   false
% 2.57/0.99  --bmc1_pre_inst_reach_state             false
% 2.57/0.99  --bmc1_out_unsat_core                   false
% 2.57/0.99  --bmc1_aig_witness_out                  false
% 2.57/0.99  --bmc1_verbose                          false
% 2.57/0.99  --bmc1_dump_clauses_tptp                false
% 2.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.57/0.99  --bmc1_dump_file                        -
% 2.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.57/0.99  --bmc1_ucm_extend_mode                  1
% 2.57/0.99  --bmc1_ucm_init_mode                    2
% 2.57/0.99  --bmc1_ucm_cone_mode                    none
% 2.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.57/0.99  --bmc1_ucm_relax_model                  4
% 2.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/0.99  --bmc1_ucm_layered_model                none
% 2.57/0.99  --bmc1_ucm_max_lemma_size               10
% 2.57/0.99  
% 2.57/0.99  ------ AIG Options
% 2.57/0.99  
% 2.57/0.99  --aig_mode                              false
% 2.57/0.99  
% 2.57/0.99  ------ Instantiation Options
% 2.57/0.99  
% 2.57/0.99  --instantiation_flag                    true
% 2.57/0.99  --inst_sos_flag                         false
% 2.57/0.99  --inst_sos_phase                        true
% 2.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/0.99  --inst_lit_sel_side                     num_symb
% 2.57/0.99  --inst_solver_per_active                1400
% 2.57/0.99  --inst_solver_calls_frac                1.
% 2.57/0.99  --inst_passive_queue_type               priority_queues
% 2.57/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/0.99  --inst_passive_queues_freq              [25;2]
% 2.57/0.99  --inst_dismatching                      true
% 2.57/0.99  --inst_eager_unprocessed_to_passive     true
% 2.57/0.99  --inst_prop_sim_given                   true
% 2.57/0.99  --inst_prop_sim_new                     false
% 2.57/0.99  --inst_subs_new                         false
% 2.57/0.99  --inst_eq_res_simp                      false
% 2.57/0.99  --inst_subs_given                       false
% 2.57/0.99  --inst_orphan_elimination               true
% 2.57/0.99  --inst_learning_loop_flag               true
% 2.57/0.99  --inst_learning_start                   3000
% 2.57/0.99  --inst_learning_factor                  2
% 2.57/0.99  --inst_start_prop_sim_after_learn       3
% 2.57/0.99  --inst_sel_renew                        solver
% 2.57/0.99  --inst_lit_activity_flag                true
% 2.57/0.99  --inst_restr_to_given                   false
% 2.57/0.99  --inst_activity_threshold               500
% 2.57/0.99  --inst_out_proof                        true
% 2.57/0.99  
% 2.57/0.99  ------ Resolution Options
% 2.57/0.99  
% 2.57/0.99  --resolution_flag                       true
% 2.57/0.99  --res_lit_sel                           adaptive
% 2.57/0.99  --res_lit_sel_side                      none
% 2.57/0.99  --res_ordering                          kbo
% 2.57/0.99  --res_to_prop_solver                    active
% 2.57/0.99  --res_prop_simpl_new                    false
% 2.57/0.99  --res_prop_simpl_given                  true
% 2.57/0.99  --res_passive_queue_type                priority_queues
% 2.57/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/0.99  --res_passive_queues_freq               [15;5]
% 2.57/0.99  --res_forward_subs                      full
% 2.57/0.99  --res_backward_subs                     full
% 2.57/0.99  --res_forward_subs_resolution           true
% 2.57/0.99  --res_backward_subs_resolution          true
% 2.57/0.99  --res_orphan_elimination                true
% 2.57/0.99  --res_time_limit                        2.
% 2.57/0.99  --res_out_proof                         true
% 2.57/0.99  
% 2.57/0.99  ------ Superposition Options
% 2.57/0.99  
% 2.57/0.99  --superposition_flag                    true
% 2.57/0.99  --sup_passive_queue_type                priority_queues
% 2.57/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.57/0.99  --demod_completeness_check              fast
% 2.57/0.99  --demod_use_ground                      true
% 2.57/0.99  --sup_to_prop_solver                    passive
% 2.57/0.99  --sup_prop_simpl_new                    true
% 2.57/0.99  --sup_prop_simpl_given                  true
% 2.57/0.99  --sup_fun_splitting                     false
% 2.57/0.99  --sup_smt_interval                      50000
% 2.57/0.99  
% 2.57/0.99  ------ Superposition Simplification Setup
% 2.57/0.99  
% 2.57/0.99  --sup_indices_passive                   []
% 2.57/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.99  --sup_full_bw                           [BwDemod]
% 2.57/0.99  --sup_immed_triv                        [TrivRules]
% 2.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.99  --sup_immed_bw_main                     []
% 2.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.99  
% 2.57/0.99  ------ Combination Options
% 2.57/0.99  
% 2.57/0.99  --comb_res_mult                         3
% 2.57/0.99  --comb_sup_mult                         2
% 2.57/0.99  --comb_inst_mult                        10
% 2.57/0.99  
% 2.57/0.99  ------ Debug Options
% 2.57/0.99  
% 2.57/0.99  --dbg_backtrace                         false
% 2.57/0.99  --dbg_dump_prop_clauses                 false
% 2.57/0.99  --dbg_dump_prop_clauses_file            -
% 2.57/0.99  --dbg_out_stat                          false
% 2.57/0.99  ------ Parsing...
% 2.57/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.57/0.99  ------ Proving...
% 2.57/0.99  ------ Problem Properties 
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  clauses                                 20
% 2.57/0.99  conjectures                             6
% 2.57/0.99  EPR                                     4
% 2.57/0.99  Horn                                    15
% 2.57/0.99  unary                                   8
% 2.57/0.99  binary                                  6
% 2.57/0.99  lits                                    44
% 2.57/0.99  lits eq                                 12
% 2.57/0.99  fd_pure                                 0
% 2.57/0.99  fd_pseudo                               0
% 2.57/0.99  fd_cond                                 3
% 2.57/0.99  fd_pseudo_cond                          0
% 2.57/0.99  AC symbols                              0
% 2.57/0.99  
% 2.57/0.99  ------ Schedule dynamic 5 is on 
% 2.57/0.99  
% 2.57/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  ------ 
% 2.57/0.99  Current options:
% 2.57/0.99  ------ 
% 2.57/0.99  
% 2.57/0.99  ------ Input Options
% 2.57/0.99  
% 2.57/0.99  --out_options                           all
% 2.57/0.99  --tptp_safe_out                         true
% 2.57/0.99  --problem_path                          ""
% 2.57/0.99  --include_path                          ""
% 2.57/0.99  --clausifier                            res/vclausify_rel
% 2.57/0.99  --clausifier_options                    --mode clausify
% 2.57/0.99  --stdin                                 false
% 2.57/0.99  --stats_out                             all
% 2.57/0.99  
% 2.57/0.99  ------ General Options
% 2.57/0.99  
% 2.57/0.99  --fof                                   false
% 2.57/0.99  --time_out_real                         305.
% 2.57/0.99  --time_out_virtual                      -1.
% 2.57/0.99  --symbol_type_check                     false
% 2.57/0.99  --clausify_out                          false
% 2.57/0.99  --sig_cnt_out                           false
% 2.57/0.99  --trig_cnt_out                          false
% 2.57/0.99  --trig_cnt_out_tolerance                1.
% 2.57/0.99  --trig_cnt_out_sk_spl                   false
% 2.57/0.99  --abstr_cl_out                          false
% 2.57/0.99  
% 2.57/0.99  ------ Global Options
% 2.57/0.99  
% 2.57/0.99  --schedule                              default
% 2.57/0.99  --add_important_lit                     false
% 2.57/0.99  --prop_solver_per_cl                    1000
% 2.57/0.99  --min_unsat_core                        false
% 2.57/0.99  --soft_assumptions                      false
% 2.57/0.99  --soft_lemma_size                       3
% 2.57/0.99  --prop_impl_unit_size                   0
% 2.57/0.99  --prop_impl_unit                        []
% 2.57/0.99  --share_sel_clauses                     true
% 2.57/0.99  --reset_solvers                         false
% 2.57/0.99  --bc_imp_inh                            [conj_cone]
% 2.57/0.99  --conj_cone_tolerance                   3.
% 2.57/0.99  --extra_neg_conj                        none
% 2.57/0.99  --large_theory_mode                     true
% 2.57/0.99  --prolific_symb_bound                   200
% 2.57/0.99  --lt_threshold                          2000
% 2.57/0.99  --clause_weak_htbl                      true
% 2.57/0.99  --gc_record_bc_elim                     false
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing Options
% 2.57/0.99  
% 2.57/0.99  --preprocessing_flag                    true
% 2.57/0.99  --time_out_prep_mult                    0.1
% 2.57/0.99  --splitting_mode                        input
% 2.57/0.99  --splitting_grd                         true
% 2.57/0.99  --splitting_cvd                         false
% 2.57/0.99  --splitting_cvd_svl                     false
% 2.57/0.99  --splitting_nvd                         32
% 2.57/0.99  --sub_typing                            true
% 2.57/0.99  --prep_gs_sim                           true
% 2.57/0.99  --prep_unflatten                        true
% 2.57/0.99  --prep_res_sim                          true
% 2.57/0.99  --prep_upred                            true
% 2.57/0.99  --prep_sem_filter                       exhaustive
% 2.57/0.99  --prep_sem_filter_out                   false
% 2.57/0.99  --pred_elim                             true
% 2.57/0.99  --res_sim_input                         true
% 2.57/0.99  --eq_ax_congr_red                       true
% 2.57/0.99  --pure_diseq_elim                       true
% 2.57/0.99  --brand_transform                       false
% 2.57/0.99  --non_eq_to_eq                          false
% 2.57/0.99  --prep_def_merge                        true
% 2.57/0.99  --prep_def_merge_prop_impl              false
% 2.57/0.99  --prep_def_merge_mbd                    true
% 2.57/0.99  --prep_def_merge_tr_red                 false
% 2.57/0.99  --prep_def_merge_tr_cl                  false
% 2.57/0.99  --smt_preprocessing                     true
% 2.57/0.99  --smt_ac_axioms                         fast
% 2.57/0.99  --preprocessed_out                      false
% 2.57/0.99  --preprocessed_stats                    false
% 2.57/0.99  
% 2.57/0.99  ------ Abstraction refinement Options
% 2.57/0.99  
% 2.57/0.99  --abstr_ref                             []
% 2.57/0.99  --abstr_ref_prep                        false
% 2.57/0.99  --abstr_ref_until_sat                   false
% 2.57/0.99  --abstr_ref_sig_restrict                funpre
% 2.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/0.99  --abstr_ref_under                       []
% 2.57/0.99  
% 2.57/0.99  ------ SAT Options
% 2.57/0.99  
% 2.57/0.99  --sat_mode                              false
% 2.57/0.99  --sat_fm_restart_options                ""
% 2.57/0.99  --sat_gr_def                            false
% 2.57/0.99  --sat_epr_types                         true
% 2.57/0.99  --sat_non_cyclic_types                  false
% 2.57/0.99  --sat_finite_models                     false
% 2.57/0.99  --sat_fm_lemmas                         false
% 2.57/0.99  --sat_fm_prep                           false
% 2.57/0.99  --sat_fm_uc_incr                        true
% 2.57/0.99  --sat_out_model                         small
% 2.57/0.99  --sat_out_clauses                       false
% 2.57/0.99  
% 2.57/0.99  ------ QBF Options
% 2.57/0.99  
% 2.57/0.99  --qbf_mode                              false
% 2.57/0.99  --qbf_elim_univ                         false
% 2.57/0.99  --qbf_dom_inst                          none
% 2.57/0.99  --qbf_dom_pre_inst                      false
% 2.57/0.99  --qbf_sk_in                             false
% 2.57/0.99  --qbf_pred_elim                         true
% 2.57/0.99  --qbf_split                             512
% 2.57/0.99  
% 2.57/0.99  ------ BMC1 Options
% 2.57/0.99  
% 2.57/0.99  --bmc1_incremental                      false
% 2.57/0.99  --bmc1_axioms                           reachable_all
% 2.57/0.99  --bmc1_min_bound                        0
% 2.57/0.99  --bmc1_max_bound                        -1
% 2.57/0.99  --bmc1_max_bound_default                -1
% 2.57/0.99  --bmc1_symbol_reachability              true
% 2.57/1.00  --bmc1_property_lemmas                  false
% 2.57/1.00  --bmc1_k_induction                      false
% 2.57/1.00  --bmc1_non_equiv_states                 false
% 2.57/1.00  --bmc1_deadlock                         false
% 2.57/1.00  --bmc1_ucm                              false
% 2.57/1.00  --bmc1_add_unsat_core                   none
% 2.57/1.00  --bmc1_unsat_core_children              false
% 2.57/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/1.00  --bmc1_out_stat                         full
% 2.57/1.00  --bmc1_ground_init                      false
% 2.57/1.00  --bmc1_pre_inst_next_state              false
% 2.57/1.00  --bmc1_pre_inst_state                   false
% 2.57/1.00  --bmc1_pre_inst_reach_state             false
% 2.57/1.00  --bmc1_out_unsat_core                   false
% 2.57/1.00  --bmc1_aig_witness_out                  false
% 2.57/1.00  --bmc1_verbose                          false
% 2.57/1.00  --bmc1_dump_clauses_tptp                false
% 2.57/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.57/1.00  --bmc1_dump_file                        -
% 2.57/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.57/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.57/1.00  --bmc1_ucm_extend_mode                  1
% 2.57/1.00  --bmc1_ucm_init_mode                    2
% 2.57/1.00  --bmc1_ucm_cone_mode                    none
% 2.57/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.57/1.00  --bmc1_ucm_relax_model                  4
% 2.57/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.57/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/1.00  --bmc1_ucm_layered_model                none
% 2.57/1.00  --bmc1_ucm_max_lemma_size               10
% 2.57/1.00  
% 2.57/1.00  ------ AIG Options
% 2.57/1.00  
% 2.57/1.00  --aig_mode                              false
% 2.57/1.00  
% 2.57/1.00  ------ Instantiation Options
% 2.57/1.00  
% 2.57/1.00  --instantiation_flag                    true
% 2.57/1.00  --inst_sos_flag                         false
% 2.57/1.00  --inst_sos_phase                        true
% 2.57/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/1.00  --inst_lit_sel_side                     none
% 2.57/1.00  --inst_solver_per_active                1400
% 2.57/1.00  --inst_solver_calls_frac                1.
% 2.57/1.00  --inst_passive_queue_type               priority_queues
% 2.57/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/1.00  --inst_passive_queues_freq              [25;2]
% 2.57/1.00  --inst_dismatching                      true
% 2.57/1.00  --inst_eager_unprocessed_to_passive     true
% 2.57/1.00  --inst_prop_sim_given                   true
% 2.57/1.00  --inst_prop_sim_new                     false
% 2.57/1.00  --inst_subs_new                         false
% 2.57/1.00  --inst_eq_res_simp                      false
% 2.57/1.00  --inst_subs_given                       false
% 2.57/1.00  --inst_orphan_elimination               true
% 2.57/1.00  --inst_learning_loop_flag               true
% 2.57/1.00  --inst_learning_start                   3000
% 2.57/1.00  --inst_learning_factor                  2
% 2.57/1.00  --inst_start_prop_sim_after_learn       3
% 2.57/1.00  --inst_sel_renew                        solver
% 2.57/1.00  --inst_lit_activity_flag                true
% 2.57/1.00  --inst_restr_to_given                   false
% 2.57/1.00  --inst_activity_threshold               500
% 2.57/1.00  --inst_out_proof                        true
% 2.57/1.00  
% 2.57/1.00  ------ Resolution Options
% 2.57/1.00  
% 2.57/1.00  --resolution_flag                       false
% 2.57/1.00  --res_lit_sel                           adaptive
% 2.57/1.00  --res_lit_sel_side                      none
% 2.57/1.00  --res_ordering                          kbo
% 2.57/1.00  --res_to_prop_solver                    active
% 2.57/1.00  --res_prop_simpl_new                    false
% 2.57/1.00  --res_prop_simpl_given                  true
% 2.57/1.00  --res_passive_queue_type                priority_queues
% 2.57/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/1.00  --res_passive_queues_freq               [15;5]
% 2.57/1.00  --res_forward_subs                      full
% 2.57/1.00  --res_backward_subs                     full
% 2.57/1.00  --res_forward_subs_resolution           true
% 2.57/1.00  --res_backward_subs_resolution          true
% 2.57/1.00  --res_orphan_elimination                true
% 2.57/1.00  --res_time_limit                        2.
% 2.57/1.00  --res_out_proof                         true
% 2.57/1.00  
% 2.57/1.00  ------ Superposition Options
% 2.57/1.00  
% 2.57/1.00  --superposition_flag                    true
% 2.57/1.00  --sup_passive_queue_type                priority_queues
% 2.57/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.57/1.00  --demod_completeness_check              fast
% 2.57/1.00  --demod_use_ground                      true
% 2.57/1.00  --sup_to_prop_solver                    passive
% 2.57/1.00  --sup_prop_simpl_new                    true
% 2.57/1.00  --sup_prop_simpl_given                  true
% 2.57/1.00  --sup_fun_splitting                     false
% 2.57/1.00  --sup_smt_interval                      50000
% 2.57/1.00  
% 2.57/1.00  ------ Superposition Simplification Setup
% 2.57/1.00  
% 2.57/1.00  --sup_indices_passive                   []
% 2.57/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.00  --sup_full_bw                           [BwDemod]
% 2.57/1.00  --sup_immed_triv                        [TrivRules]
% 2.57/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.00  --sup_immed_bw_main                     []
% 2.57/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.00  
% 2.57/1.00  ------ Combination Options
% 2.57/1.00  
% 2.57/1.00  --comb_res_mult                         3
% 2.57/1.00  --comb_sup_mult                         2
% 2.57/1.00  --comb_inst_mult                        10
% 2.57/1.00  
% 2.57/1.00  ------ Debug Options
% 2.57/1.00  
% 2.57/1.00  --dbg_backtrace                         false
% 2.57/1.00  --dbg_dump_prop_clauses                 false
% 2.57/1.00  --dbg_dump_prop_clauses_file            -
% 2.57/1.00  --dbg_out_stat                          false
% 2.57/1.00  
% 2.57/1.00  
% 2.57/1.00  
% 2.57/1.00  
% 2.57/1.00  ------ Proving...
% 2.57/1.00  
% 2.57/1.00  
% 2.57/1.00  % SZS status Theorem for theBenchmark.p
% 2.57/1.00  
% 2.57/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.57/1.00  
% 2.57/1.00  fof(f10,conjecture,(
% 2.57/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f11,negated_conjecture,(
% 2.57/1.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.57/1.00    inference(negated_conjecture,[],[f10])).
% 2.57/1.00  
% 2.57/1.00  fof(f21,plain,(
% 2.57/1.00    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.57/1.00    inference(ennf_transformation,[],[f11])).
% 2.57/1.00  
% 2.57/1.00  fof(f22,plain,(
% 2.57/1.00    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.57/1.00    inference(flattening,[],[f21])).
% 2.57/1.00  
% 2.57/1.00  fof(f29,plain,(
% 2.57/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3)) & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.57/1.00    introduced(choice_axiom,[])).
% 2.57/1.00  
% 2.57/1.00  fof(f28,plain,(
% 2.57/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 2.57/1.00    introduced(choice_axiom,[])).
% 2.57/1.00  
% 2.57/1.00  fof(f27,plain,(
% 2.57/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 2.57/1.00    introduced(choice_axiom,[])).
% 2.57/1.00  
% 2.57/1.00  fof(f26,plain,(
% 2.57/1.00    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 2.57/1.00    introduced(choice_axiom,[])).
% 2.57/1.00  
% 2.57/1.00  fof(f30,plain,(
% 2.57/1.00    ((((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.57/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f29,f28,f27,f26])).
% 2.57/1.00  
% 2.57/1.00  fof(f49,plain,(
% 2.57/1.00    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))),
% 2.57/1.00    inference(cnf_transformation,[],[f30])).
% 2.57/1.00  
% 2.57/1.00  fof(f7,axiom,(
% 2.57/1.00    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f40,plain,(
% 2.57/1.00    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.57/1.00    inference(cnf_transformation,[],[f7])).
% 2.57/1.00  
% 2.57/1.00  fof(f56,plain,(
% 2.57/1.00    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 2.57/1.00    inference(definition_unfolding,[],[f49,f40])).
% 2.57/1.00  
% 2.57/1.00  fof(f9,axiom,(
% 2.57/1.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f20,plain,(
% 2.57/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.57/1.00    inference(ennf_transformation,[],[f9])).
% 2.57/1.00  
% 2.57/1.00  fof(f45,plain,(
% 2.57/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.57/1.00    inference(cnf_transformation,[],[f20])).
% 2.57/1.00  
% 2.57/1.00  fof(f52,plain,(
% 2.57/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.57/1.00    inference(definition_unfolding,[],[f45,f40])).
% 2.57/1.00  
% 2.57/1.00  fof(f44,plain,(
% 2.57/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.57/1.00    inference(cnf_transformation,[],[f20])).
% 2.57/1.00  
% 2.57/1.00  fof(f53,plain,(
% 2.57/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.57/1.00    inference(definition_unfolding,[],[f44,f40])).
% 2.57/1.00  
% 2.57/1.00  fof(f43,plain,(
% 2.57/1.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.57/1.00    inference(cnf_transformation,[],[f20])).
% 2.57/1.00  
% 2.57/1.00  fof(f54,plain,(
% 2.57/1.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.57/1.00    inference(definition_unfolding,[],[f43,f40])).
% 2.57/1.00  
% 2.57/1.00  fof(f51,plain,(
% 2.57/1.00    ~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)),
% 2.57/1.00    inference(cnf_transformation,[],[f30])).
% 2.57/1.00  
% 2.57/1.00  fof(f50,plain,(
% 2.57/1.00    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 2.57/1.00    inference(cnf_transformation,[],[f30])).
% 2.57/1.00  
% 2.57/1.00  fof(f55,plain,(
% 2.57/1.00    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.57/1.00    inference(definition_unfolding,[],[f50,f40])).
% 2.57/1.00  
% 2.57/1.00  fof(f8,axiom,(
% 2.57/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f19,plain,(
% 2.57/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.57/1.00    inference(ennf_transformation,[],[f8])).
% 2.57/1.00  
% 2.57/1.00  fof(f41,plain,(
% 2.57/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.57/1.00    inference(cnf_transformation,[],[f19])).
% 2.57/1.00  
% 2.57/1.00  fof(f42,plain,(
% 2.57/1.00    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.57/1.00    inference(cnf_transformation,[],[f19])).
% 2.57/1.00  
% 2.57/1.00  fof(f48,plain,(
% 2.57/1.00    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 2.57/1.00    inference(cnf_transformation,[],[f30])).
% 2.57/1.00  
% 2.57/1.00  fof(f5,axiom,(
% 2.57/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f25,plain,(
% 2.57/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.57/1.00    inference(nnf_transformation,[],[f5])).
% 2.57/1.00  
% 2.57/1.00  fof(f37,plain,(
% 2.57/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.57/1.00    inference(cnf_transformation,[],[f25])).
% 2.57/1.00  
% 2.57/1.00  fof(f6,axiom,(
% 2.57/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f18,plain,(
% 2.57/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.57/1.00    inference(ennf_transformation,[],[f6])).
% 2.57/1.00  
% 2.57/1.00  fof(f39,plain,(
% 2.57/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.57/1.00    inference(cnf_transformation,[],[f18])).
% 2.57/1.00  
% 2.57/1.00  fof(f2,axiom,(
% 2.57/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f12,plain,(
% 2.57/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.57/1.00    inference(rectify,[],[f2])).
% 2.57/1.00  
% 2.57/1.00  fof(f15,plain,(
% 2.57/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.57/1.00    inference(ennf_transformation,[],[f12])).
% 2.57/1.00  
% 2.57/1.00  fof(f23,plain,(
% 2.57/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.57/1.00    introduced(choice_axiom,[])).
% 2.57/1.00  
% 2.57/1.00  fof(f24,plain,(
% 2.57/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.57/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f23])).
% 2.57/1.00  
% 2.57/1.00  fof(f32,plain,(
% 2.57/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.57/1.00    inference(cnf_transformation,[],[f24])).
% 2.57/1.00  
% 2.57/1.00  fof(f3,axiom,(
% 2.57/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f35,plain,(
% 2.57/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.57/1.00    inference(cnf_transformation,[],[f3])).
% 2.57/1.00  
% 2.57/1.00  fof(f4,axiom,(
% 2.57/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f16,plain,(
% 2.57/1.00    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.57/1.00    inference(ennf_transformation,[],[f4])).
% 2.57/1.00  
% 2.57/1.00  fof(f17,plain,(
% 2.57/1.00    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.57/1.00    inference(flattening,[],[f16])).
% 2.57/1.00  
% 2.57/1.00  fof(f36,plain,(
% 2.57/1.00    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.57/1.00    inference(cnf_transformation,[],[f17])).
% 2.57/1.00  
% 2.57/1.00  fof(f33,plain,(
% 2.57/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.57/1.00    inference(cnf_transformation,[],[f24])).
% 2.57/1.00  
% 2.57/1.00  fof(f1,axiom,(
% 2.57/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.57/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.00  
% 2.57/1.00  fof(f13,plain,(
% 2.57/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.57/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 2.57/1.00  
% 2.57/1.00  fof(f14,plain,(
% 2.57/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.57/1.00    inference(ennf_transformation,[],[f13])).
% 2.57/1.00  
% 2.57/1.00  fof(f31,plain,(
% 2.57/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.57/1.00    inference(cnf_transformation,[],[f14])).
% 2.57/1.00  
% 2.57/1.00  fof(f47,plain,(
% 2.57/1.00    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 2.57/1.00    inference(cnf_transformation,[],[f30])).
% 2.57/1.00  
% 2.57/1.00  fof(f46,plain,(
% 2.57/1.00    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.57/1.00    inference(cnf_transformation,[],[f30])).
% 2.57/1.00  
% 2.57/1.00  cnf(c_16,negated_conjecture,
% 2.57/1.00      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
% 2.57/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1368,plain,
% 2.57/1.00      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_11,plain,
% 2.57/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.57/1.00      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.57/1.00      | k1_xboole_0 = X3
% 2.57/1.00      | k1_xboole_0 = X2
% 2.57/1.00      | k1_xboole_0 = X1 ),
% 2.57/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1373,plain,
% 2.57/1.00      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.57/1.00      | k1_xboole_0 = X1
% 2.57/1.00      | k1_xboole_0 = X0
% 2.57/1.00      | k1_xboole_0 = X2
% 2.57/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_3632,plain,
% 2.57/1.00      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
% 2.57/1.00      | sK3 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0 ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1368,c_1373]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_12,plain,
% 2.57/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.57/1.00      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.57/1.00      | k1_xboole_0 = X3
% 2.57/1.00      | k1_xboole_0 = X2
% 2.57/1.00      | k1_xboole_0 = X1 ),
% 2.57/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1372,plain,
% 2.57/1.00      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.57/1.00      | k1_xboole_0 = X1
% 2.57/1.00      | k1_xboole_0 = X0
% 2.57/1.00      | k1_xboole_0 = X2
% 2.57/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_5759,plain,
% 2.57/1.00      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.57/1.00      | sK3 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0 ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1368,c_1372]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_13,plain,
% 2.57/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.57/1.00      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.57/1.00      | k1_xboole_0 = X3
% 2.57/1.00      | k1_xboole_0 = X2
% 2.57/1.00      | k1_xboole_0 = X1 ),
% 2.57/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1371,plain,
% 2.57/1.00      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.57/1.00      | k1_xboole_0 = X1
% 2.57/1.00      | k1_xboole_0 = X0
% 2.57/1.00      | k1_xboole_0 = X2
% 2.57/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_3639,plain,
% 2.57/1.00      ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.57/1.00      | sK3 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0 ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1368,c_1371]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_14,negated_conjecture,
% 2.57/1.00      ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
% 2.57/1.00      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
% 2.57/1.00      | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
% 2.57/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1370,plain,
% 2.57/1.00      ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
% 2.57/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.57/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_3919,plain,
% 2.57/1.00      ( sK3 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0
% 2.57/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.57/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.57/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_3639,c_1370]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_15,negated_conjecture,
% 2.57/1.00      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.57/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_24,plain,
% 2.57/1.00      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_10,plain,
% 2.57/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.57/1.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.57/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1524,plain,
% 2.57/1.00      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.57/1.00      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.57/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1525,plain,
% 2.57/1.00      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 2.57/1.00      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_1524]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1614,plain,
% 2.57/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.57/1.00      | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
% 2.57/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1618,plain,
% 2.57/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 2.57/1.00      | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_1614]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_4930,plain,
% 2.57/1.00      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.57/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.57/1.00      | sK1 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK3 = k1_xboole_0 ),
% 2.57/1.00      inference(global_propositional_subsumption,
% 2.57/1.00                [status(thm)],
% 2.57/1.00                [c_3919,c_24,c_1525,c_1618]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_4931,plain,
% 2.57/1.00      ( sK3 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0
% 2.57/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.57/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.57/1.00      inference(renaming,[status(thm)],[c_4930]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_6260,plain,
% 2.57/1.00      ( sK3 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0
% 2.57/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.57/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_5759,c_4931]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_9,plain,
% 2.57/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.57/1.00      | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.57/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1615,plain,
% 2.57/1.00      ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.57/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 2.57/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1616,plain,
% 2.57/1.00      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.57/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_1615]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_6528,plain,
% 2.57/1.00      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.57/1.00      | sK1 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK3 = k1_xboole_0 ),
% 2.57/1.00      inference(global_propositional_subsumption,
% 2.57/1.00                [status(thm)],
% 2.57/1.00                [c_6260,c_24,c_1525,c_1616]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_6529,plain,
% 2.57/1.00      ( sK3 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0
% 2.57/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.57/1.00      inference(renaming,[status(thm)],[c_6528]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_6536,plain,
% 2.57/1.00      ( sK3 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0
% 2.57/1.00      | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_3632,c_6529]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1521,plain,
% 2.57/1.00      ( r2_hidden(k2_mcart_1(sK7),sK6)
% 2.57/1.00      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.57/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_6537,plain,
% 2.57/1.00      ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
% 2.57/1.00      | sK3 = k1_xboole_0
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0 ),
% 2.57/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6536]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_6539,plain,
% 2.57/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.57/1.00      inference(global_propositional_subsumption,
% 2.57/1.00                [status(thm)],
% 2.57/1.00                [c_6536,c_24,c_1522]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_6540,plain,
% 2.57/1.00      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.57/1.00      inference(renaming,[status(thm)],[c_6539]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_17,negated_conjecture,
% 2.57/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 2.57/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1367,plain,
% 2.57/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_7,plain,
% 2.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.57/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_154,plain,
% 2.57/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.57/1.00      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_155,plain,
% 2.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.57/1.00      inference(renaming,[status(thm)],[c_154]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_8,plain,
% 2.57/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.57/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_282,plain,
% 2.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r2_hidden(X1,X0) ),
% 2.57/1.00      inference(resolution,[status(thm)],[c_155,c_8]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1364,plain,
% 2.57/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.57/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_5740,plain,
% 2.57/1.00      ( r2_hidden(sK3,sK6) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1367,c_1364]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_6545,plain,
% 2.57/1.00      ( sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0
% 2.57/1.00      | r2_hidden(k1_xboole_0,sK6) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_6540,c_5740]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_3,plain,
% 2.57/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 2.57/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_4,plain,
% 2.57/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.57/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_5,plain,
% 2.57/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 2.57/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_326,plain,
% 2.57/1.00      ( ~ r1_xboole_0(X0,X1)
% 2.57/1.00      | v1_xboole_0(X0)
% 2.57/1.00      | X1 != X2
% 2.57/1.00      | k1_xboole_0 != X0 ),
% 2.57/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_327,plain,
% 2.57/1.00      ( ~ r1_xboole_0(k1_xboole_0,X0) | v1_xboole_0(k1_xboole_0) ),
% 2.57/1.00      inference(unflattening,[status(thm)],[c_326]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_421,plain,
% 2.57/1.00      ( r2_hidden(sK0(X0,X1),X0)
% 2.57/1.00      | v1_xboole_0(k1_xboole_0)
% 2.57/1.00      | X2 != X1
% 2.57/1.00      | k1_xboole_0 != X0 ),
% 2.57/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_327]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_422,plain,
% 2.57/1.00      ( r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0)
% 2.57/1.00      | v1_xboole_0(k1_xboole_0) ),
% 2.57/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_308,plain,
% 2.57/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.57/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_309,plain,
% 2.57/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.57/1.00      inference(unflattening,[status(thm)],[c_308]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_430,plain,
% 2.57/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.57/1.00      inference(forward_subsumption_resolution,
% 2.57/1.00                [status(thm)],
% 2.57/1.00                [c_422,c_309]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_2,plain,
% 2.57/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK0(X0,X1),X1) ),
% 2.57/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1377,plain,
% 2.57/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 2.57/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_0,plain,
% 2.57/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.57/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1379,plain,
% 2.57/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.57/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1892,plain,
% 2.57/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 2.57/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1377,c_1379]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_294,plain,
% 2.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.57/1.00      | ~ r1_xboole_0(X0,X1)
% 2.57/1.00      | v1_xboole_0(X0) ),
% 2.57/1.00      inference(resolution,[status(thm)],[c_155,c_5]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1363,plain,
% 2.57/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.57/1.00      | r1_xboole_0(X0,X1) != iProver_top
% 2.57/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_2939,plain,
% 2.57/1.00      ( r1_xboole_0(sK6,sK3) != iProver_top
% 2.57/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1367,c_1363]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1522,plain,
% 2.57/1.00      ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top
% 2.57/1.00      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_1521]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1583,plain,
% 2.57/1.00      ( ~ r2_hidden(k2_mcart_1(sK7),sK6) | ~ v1_xboole_0(sK6) ),
% 2.57/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1584,plain,
% 2.57/1.00      ( r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top
% 2.57/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_3663,plain,
% 2.57/1.00      ( r1_xboole_0(sK6,sK3) != iProver_top ),
% 2.57/1.00      inference(global_propositional_subsumption,
% 2.57/1.00                [status(thm)],
% 2.57/1.00                [c_2939,c_24,c_1522,c_1584]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_8112,plain,
% 2.57/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1892,c_3663]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_11476,plain,
% 2.57/1.00      ( sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0
% 2.57/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_6540,c_8112]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_11477,plain,
% 2.57/1.00      ( ~ v1_xboole_0(k1_xboole_0)
% 2.57/1.00      | sK2 = k1_xboole_0
% 2.57/1.00      | sK1 = k1_xboole_0 ),
% 2.57/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_11476]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_12004,plain,
% 2.57/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.57/1.00      inference(global_propositional_subsumption,
% 2.57/1.00                [status(thm)],
% 2.57/1.00                [c_6545,c_432,c_11476]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_12005,plain,
% 2.57/1.00      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.57/1.00      inference(renaming,[status(thm)],[c_12004]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_12014,plain,
% 2.57/1.00      ( sK1 = k1_xboole_0
% 2.57/1.00      | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
% 2.57/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.57/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_12005,c_1370]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_432,plain,
% 2.57/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_18,negated_conjecture,
% 2.57/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 2.57/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1366,plain,
% 2.57/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_2940,plain,
% 2.57/1.00      ( r1_xboole_0(sK5,sK2) != iProver_top
% 2.57/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1366,c_1363]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1778,plain,
% 2.57/1.00      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
% 2.57/1.00      | ~ v1_xboole_0(sK5) ),
% 2.57/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1779,plain,
% 2.57/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
% 2.57/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_1778]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_3782,plain,
% 2.57/1.00      ( r1_xboole_0(sK5,sK2) != iProver_top ),
% 2.57/1.00      inference(global_propositional_subsumption,
% 2.57/1.00                [status(thm)],
% 2.57/1.00                [c_2940,c_24,c_1525,c_1616,c_1779]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_8113,plain,
% 2.57/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1892,c_3782]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_12008,plain,
% 2.57/1.00      ( sK1 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_12005,c_8113]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_12052,plain,
% 2.57/1.00      ( sK1 = k1_xboole_0 ),
% 2.57/1.00      inference(global_propositional_subsumption,
% 2.57/1.00                [status(thm)],
% 2.57/1.00                [c_12014,c_432,c_12008]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_19,negated_conjecture,
% 2.57/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 2.57/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1365,plain,
% 2.57/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_2941,plain,
% 2.57/1.00      ( r1_xboole_0(sK4,sK1) != iProver_top
% 2.57/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1365,c_1363]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1762,plain,
% 2.57/1.00      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.57/1.00      | ~ v1_xboole_0(sK4) ),
% 2.57/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_1763,plain,
% 2.57/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
% 2.57/1.00      | v1_xboole_0(sK4) != iProver_top ),
% 2.57/1.00      inference(predicate_to_equality,[status(thm)],[c_1762]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_3790,plain,
% 2.57/1.00      ( r1_xboole_0(sK4,sK1) != iProver_top ),
% 2.57/1.00      inference(global_propositional_subsumption,
% 2.57/1.00                [status(thm)],
% 2.57/1.00                [c_2941,c_24,c_1525,c_1618,c_1763]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_8114,plain,
% 2.57/1.00      ( v1_xboole_0(sK1) != iProver_top ),
% 2.57/1.00      inference(superposition,[status(thm)],[c_1892,c_3790]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(c_12055,plain,
% 2.57/1.00      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.57/1.00      inference(demodulation,[status(thm)],[c_12052,c_8114]) ).
% 2.57/1.00  
% 2.57/1.00  cnf(contradiction,plain,
% 2.57/1.00      ( $false ),
% 2.57/1.00      inference(minisat,[status(thm)],[c_12055,c_432]) ).
% 2.57/1.00  
% 2.57/1.00  
% 2.57/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.57/1.00  
% 2.57/1.00  ------                               Statistics
% 2.57/1.00  
% 2.57/1.00  ------ General
% 2.57/1.00  
% 2.57/1.00  abstr_ref_over_cycles:                  0
% 2.57/1.00  abstr_ref_under_cycles:                 0
% 2.57/1.00  gc_basic_clause_elim:                   0
% 2.57/1.00  forced_gc_time:                         0
% 2.57/1.00  parsing_time:                           0.011
% 2.57/1.00  unif_index_cands_time:                  0.
% 2.57/1.00  unif_index_add_time:                    0.
% 2.57/1.00  orderings_time:                         0.
% 2.57/1.00  out_proof_time:                         0.012
% 2.57/1.00  total_time:                             0.332
% 2.57/1.00  num_of_symbols:                         52
% 2.57/1.00  num_of_terms:                           14169
% 2.57/1.00  
% 2.57/1.00  ------ Preprocessing
% 2.57/1.00  
% 2.57/1.00  num_of_splits:                          0
% 2.57/1.00  num_of_split_atoms:                     0
% 2.57/1.00  num_of_reused_defs:                     0
% 2.57/1.00  num_eq_ax_congr_red:                    10
% 2.57/1.00  num_of_sem_filtered_clauses:            1
% 2.57/1.00  num_of_subtypes:                        0
% 2.57/1.00  monotx_restored_types:                  0
% 2.57/1.00  sat_num_of_epr_types:                   0
% 2.57/1.00  sat_num_of_non_cyclic_types:            0
% 2.57/1.00  sat_guarded_non_collapsed_types:        0
% 2.57/1.00  num_pure_diseq_elim:                    0
% 2.57/1.00  simp_replaced_by:                       0
% 2.57/1.00  res_preprocessed:                       85
% 2.57/1.00  prep_upred:                             0
% 2.57/1.00  prep_unflattend:                        40
% 2.57/1.00  smt_new_axioms:                         0
% 2.57/1.00  pred_elim_cands:                        5
% 2.57/1.00  pred_elim:                              1
% 2.57/1.00  pred_elim_cl:                           0
% 2.57/1.00  pred_elim_cycles:                       7
% 2.57/1.00  merged_defs:                            2
% 2.57/1.00  merged_defs_ncl:                        0
% 2.57/1.00  bin_hyper_res:                          2
% 2.57/1.00  prep_cycles:                            3
% 2.57/1.00  pred_elim_time:                         0.015
% 2.57/1.00  splitting_time:                         0.
% 2.57/1.00  sem_filter_time:                        0.
% 2.57/1.00  monotx_time:                            0.
% 2.57/1.00  subtype_inf_time:                       0.
% 2.57/1.00  
% 2.57/1.00  ------ Problem properties
% 2.57/1.00  
% 2.57/1.00  clauses:                                20
% 2.57/1.00  conjectures:                            6
% 2.57/1.00  epr:                                    4
% 2.57/1.00  horn:                                   15
% 2.57/1.00  ground:                                 7
% 2.57/1.00  unary:                                  8
% 2.57/1.00  binary:                                 6
% 2.57/1.00  lits:                                   44
% 2.57/1.00  lits_eq:                                12
% 2.57/1.00  fd_pure:                                0
% 2.57/1.00  fd_pseudo:                              0
% 2.57/1.00  fd_cond:                                3
% 2.57/1.00  fd_pseudo_cond:                         0
% 2.57/1.00  ac_symbols:                             0
% 2.57/1.00  
% 2.57/1.00  ------ Propositional Solver
% 2.57/1.00  
% 2.57/1.00  prop_solver_calls:                      25
% 2.57/1.00  prop_fast_solver_calls:                 709
% 2.57/1.00  smt_solver_calls:                       0
% 2.57/1.00  smt_fast_solver_calls:                  0
% 2.57/1.00  prop_num_of_clauses:                    4708
% 2.57/1.00  prop_preprocess_simplified:             12494
% 2.57/1.00  prop_fo_subsumed:                       10
% 2.57/1.00  prop_solver_time:                       0.
% 2.57/1.00  smt_solver_time:                        0.
% 2.57/1.00  smt_fast_solver_time:                   0.
% 2.57/1.00  prop_fast_solver_time:                  0.
% 2.57/1.00  prop_unsat_core_time:                   0.
% 2.57/1.00  
% 2.57/1.00  ------ QBF
% 2.57/1.00  
% 2.57/1.00  qbf_q_res:                              0
% 2.57/1.00  qbf_num_tautologies:                    0
% 2.57/1.00  qbf_prep_cycles:                        0
% 2.57/1.00  
% 2.57/1.00  ------ BMC1
% 2.57/1.00  
% 2.57/1.00  bmc1_current_bound:                     -1
% 2.57/1.00  bmc1_last_solved_bound:                 -1
% 2.57/1.00  bmc1_unsat_core_size:                   -1
% 2.57/1.00  bmc1_unsat_core_parents_size:           -1
% 2.57/1.00  bmc1_merge_next_fun:                    0
% 2.57/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.57/1.00  
% 2.57/1.00  ------ Instantiation
% 2.57/1.00  
% 2.57/1.00  inst_num_of_clauses:                    1350
% 2.57/1.00  inst_num_in_passive:                    953
% 2.57/1.00  inst_num_in_active:                     282
% 2.57/1.00  inst_num_in_unprocessed:                115
% 2.57/1.00  inst_num_of_loops:                      290
% 2.57/1.00  inst_num_of_learning_restarts:          0
% 2.57/1.00  inst_num_moves_active_passive:          7
% 2.57/1.00  inst_lit_activity:                      0
% 2.57/1.00  inst_lit_activity_moves:                0
% 2.57/1.00  inst_num_tautologies:                   0
% 2.57/1.00  inst_num_prop_implied:                  0
% 2.57/1.00  inst_num_existing_simplified:           0
% 2.57/1.00  inst_num_eq_res_simplified:             0
% 2.57/1.00  inst_num_child_elim:                    0
% 2.57/1.00  inst_num_of_dismatching_blockings:      35
% 2.57/1.00  inst_num_of_non_proper_insts:           934
% 2.57/1.00  inst_num_of_duplicates:                 0
% 2.57/1.00  inst_inst_num_from_inst_to_res:         0
% 2.57/1.00  inst_dismatching_checking_time:         0.
% 2.57/1.00  
% 2.57/1.00  ------ Resolution
% 2.57/1.00  
% 2.57/1.00  res_num_of_clauses:                     0
% 2.57/1.00  res_num_in_passive:                     0
% 2.57/1.00  res_num_in_active:                      0
% 2.57/1.00  res_num_of_loops:                       88
% 2.57/1.00  res_forward_subset_subsumed:            26
% 2.57/1.00  res_backward_subset_subsumed:           0
% 2.57/1.00  res_forward_subsumed:                   1
% 2.57/1.00  res_backward_subsumed:                  1
% 2.57/1.00  res_forward_subsumption_resolution:     1
% 2.57/1.00  res_backward_subsumption_resolution:    0
% 2.57/1.00  res_clause_to_clause_subsumption:       116
% 2.57/1.00  res_orphan_elimination:                 0
% 2.57/1.00  res_tautology_del:                      28
% 2.57/1.00  res_num_eq_res_simplified:              0
% 2.57/1.00  res_num_sel_changes:                    0
% 2.57/1.00  res_moves_from_active_to_pass:          0
% 2.57/1.00  
% 2.57/1.00  ------ Superposition
% 2.57/1.00  
% 2.57/1.00  sup_time_total:                         0.
% 2.57/1.00  sup_time_generating:                    0.
% 2.57/1.00  sup_time_sim_full:                      0.
% 2.57/1.00  sup_time_sim_immed:                     0.
% 2.57/1.00  
% 2.57/1.00  sup_num_of_clauses:                     53
% 2.57/1.00  sup_num_in_active:                      42
% 2.57/1.00  sup_num_in_passive:                     11
% 2.57/1.00  sup_num_of_loops:                       56
% 2.57/1.00  sup_fw_superposition:                   29
% 2.57/1.00  sup_bw_superposition:                   47
% 2.57/1.00  sup_immediate_simplified:               11
% 2.57/1.00  sup_given_eliminated:                   0
% 2.57/1.00  comparisons_done:                       0
% 2.57/1.00  comparisons_avoided:                    36
% 2.57/1.00  
% 2.57/1.00  ------ Simplifications
% 2.57/1.00  
% 2.57/1.00  
% 2.57/1.00  sim_fw_subset_subsumed:                 10
% 2.57/1.00  sim_bw_subset_subsumed:                 13
% 2.57/1.00  sim_fw_subsumed:                        1
% 2.57/1.00  sim_bw_subsumed:                        0
% 2.57/1.00  sim_fw_subsumption_res:                 0
% 2.57/1.00  sim_bw_subsumption_res:                 0
% 2.57/1.00  sim_tautology_del:                      0
% 2.57/1.00  sim_eq_tautology_del:                   6
% 2.57/1.00  sim_eq_res_simp:                        0
% 2.57/1.00  sim_fw_demodulated:                     0
% 2.57/1.00  sim_bw_demodulated:                     9
% 2.57/1.00  sim_light_normalised:                   0
% 2.57/1.00  sim_joinable_taut:                      0
% 2.57/1.00  sim_joinable_simp:                      0
% 2.57/1.00  sim_ac_normalised:                      0
% 2.57/1.00  sim_smt_subsumption:                    0
% 2.57/1.00  
%------------------------------------------------------------------------------
