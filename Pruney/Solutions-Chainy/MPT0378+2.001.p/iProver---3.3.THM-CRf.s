%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:10 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 361 expanded)
%              Number of clauses        :   77 (  94 expanded)
%              Number of leaves         :   23 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  601 (2166 expanded)
%              Number of equality atoms :  227 ( 442 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k1_xboole_0 != X0
                   => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  | k1_xboole_0 = X0
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  | k1_xboole_0 = X0
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f18])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ( k1_xboole_0 != X0
                           => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ( k1_xboole_0 != X0
                             => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X6,X0) )
     => ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,sK10),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK10,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X6,X0) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,sK9,X6),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X6,X0) )
        & m1_subset_1(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X6,X0) )
              & m1_subset_1(X5,X0) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,sK8,X5,X6),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X6,X0) )
            & m1_subset_1(X5,X0) )
        & m1_subset_1(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X6,X0) )
                  & m1_subset_1(X5,X0) )
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ m1_subset_1(k4_enumset1(X1,X2,sK7,X4,X5,X6),k1_zfmisc_1(X0))
                    & k1_xboole_0 != X0
                    & m1_subset_1(X6,X0) )
                & m1_subset_1(X5,X0) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ m1_subset_1(k4_enumset1(X1,sK6,X3,X4,X5,X6),k1_zfmisc_1(X0))
                        & k1_xboole_0 != X0
                        & m1_subset_1(X6,X0) )
                    & m1_subset_1(X5,X0) )
                & m1_subset_1(X4,X0) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                            & k1_xboole_0 != X0
                            & m1_subset_1(X6,X0) )
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(sK5,X2,X3,X4,X5,X6),k1_zfmisc_1(sK4))
                          & k1_xboole_0 != sK4
                          & m1_subset_1(X6,sK4) )
                      & m1_subset_1(X5,sK4) )
                  & m1_subset_1(X4,sK4) )
              & m1_subset_1(X3,sK4) )
          & m1_subset_1(X2,sK4) )
      & m1_subset_1(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4))
    & k1_xboole_0 != sK4
    & m1_subset_1(sK10,sK4)
    & m1_subset_1(sK9,sK4)
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,sK4)
    & m1_subset_1(sK6,sK4)
    & m1_subset_1(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f21,f46,f45,f44,f43,f42,f41])).

fof(f85,plain,(
    ~ m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f3])).

fof(f86,plain,(
    ~ m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
    inference(definition_unfolding,[],[f85,f51])).

fof(f78,plain,(
    m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f22,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4) != X0
            & sK3(X0,X1,X2,X3,X4) != X1
            & sK3(X0,X1,X2,X3,X4) != X2
            & sK3(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
        & ( sK3(X0,X1,X2,X3,X4) = X0
          | sK3(X0,X1,X2,X3,X4) = X1
          | sK3(X0,X1,X2,X3,X4) = X2
          | sK3(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK3(X0,X1,X2,X3,X4) != X0
              & sK3(X0,X1,X2,X3,X4) != X1
              & sK3(X0,X1,X2,X3,X4) != X2
              & sK3(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
          & ( sK3(X0,X1,X2,X3,X4) = X0
            | sK3(X0,X1,X2,X3,X4) = X1
            | sK3(X0,X1,X2,X3,X4) = X2
            | sK3(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X6,X4) ) ),
    inference(equality_resolution,[],[f60])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f15,f22])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f69])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X1)
    | m1_subset_1(k2_enumset1(X0,X4,X3,X2),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1991,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(k2_enumset1(X1,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1994,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3384,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | r2_hidden(k2_enumset1(X1,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_1994])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_48,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7734,plain,
    ( r2_hidden(k2_enumset1(X1,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3384,c_48])).

cnf(c_7735,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | r2_hidden(k2_enumset1(X1,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7734])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2012,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7742,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | r1_tarski(k2_enumset1(X1,X4,X3,X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7735,c_2012])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2016,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2013,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_24,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_1])).

cnf(c_198,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_197])).

cnf(c_1983,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_2587,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_1983])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1990,plain,
    ( m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6531,plain,
    ( r1_tarski(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2587,c_1990])).

cnf(c_7747,plain,
    ( r1_tarski(k2_enumset1(sK7,sK8,sK9,sK10),sK4) != iProver_top
    | r1_tarski(k2_tarski(sK5,sK6),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_6531])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_38,plain,
    ( m1_subset_1(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2526,plain,
    ( ~ m1_subset_1(sK6,sK4)
    | r2_hidden(sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2527,plain,
    ( m1_subset_1(sK6,sK4) != iProver_top
    | r2_hidden(sK6,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2526])).

cnf(c_2529,plain,
    ( ~ m1_subset_1(sK5,sK4)
    | r2_hidden(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2530,plain,
    ( m1_subset_1(sK5,sK4) != iProver_top
    | r2_hidden(sK5,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2529])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2727,plain,
    ( r2_hidden(sK10,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_25,c_31])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_45,plain,
    ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK4,sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_22,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_59,plain,
    ( m1_subset_1(sK4,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_108,plain,
    ( ~ r2_hidden(sK4,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | r2_hidden(X3,X4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_976,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | k2_enumset1(X4,X5,X7,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_977,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(unflattening,[status(thm)],[c_976])).

cnf(c_979,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2355,plain,
    ( ~ m1_subset_1(k2_enumset1(X0,X1,X2,X3),k1_zfmisc_1(X4))
    | r2_hidden(X3,X4)
    | ~ r2_hidden(X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2357,plain,
    ( ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2355])).

cnf(c_2514,plain,
    ( ~ m1_subset_1(sK10,sK4)
    | r2_hidden(sK10,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2920,plain,
    ( r2_hidden(sK10,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2727,c_31,c_30,c_45,c_59,c_108,c_979,c_2357,c_2514])).

cnf(c_2922,plain,
    ( r2_hidden(sK10,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2920])).

cnf(c_3090,plain,
    ( ~ r2_hidden(sK10,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3092,plain,
    ( r2_hidden(sK10,sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3090])).

cnf(c_2481,plain,
    ( ~ r2_hidden(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
    inference(resolution,[status(thm)],[c_29,c_198])).

cnf(c_2607,plain,
    ( ~ r1_tarski(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),sK4) ),
    inference(resolution,[status(thm)],[c_2481,c_5])).

cnf(c_5604,plain,
    ( ~ r1_tarski(k2_enumset1(sK7,sK8,sK9,sK10),sK4)
    | ~ r1_tarski(k2_tarski(sK5,sK6),sK4) ),
    inference(resolution,[status(thm)],[c_2607,c_2])).

cnf(c_5605,plain,
    ( r1_tarski(k2_enumset1(sK7,sK8,sK9,sK10),sK4) != iProver_top
    | r1_tarski(k2_tarski(sK5,sK6),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5604])).

cnf(c_7,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3213,plain,
    ( r1_tarski(k2_tarski(X0,sK6),sK4)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(sK6,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6290,plain,
    ( r1_tarski(k2_tarski(sK5,sK6),sK4)
    | ~ r2_hidden(sK6,sK4)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_3213])).

cnf(c_6291,plain,
    ( r1_tarski(k2_tarski(sK5,sK6),sK4) = iProver_top
    | r2_hidden(sK6,sK4) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6290])).

cnf(c_8938,plain,
    ( r1_tarski(k2_enumset1(sK7,sK8,sK9,sK10),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7747,c_37,c_38,c_2527,c_2530,c_2922,c_3092,c_5605,c_6291])).

cnf(c_16296,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK10,sK4) != iProver_top
    | m1_subset_1(sK9,sK4) != iProver_top
    | m1_subset_1(sK8,sK4) != iProver_top
    | m1_subset_1(sK7,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7742,c_8938])).

cnf(c_1144,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2248,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_1145,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2151,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_2247,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_42,plain,
    ( m1_subset_1(sK10,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_41,plain,
    ( m1_subset_1(sK9,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( m1_subset_1(sK8,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_39,plain,
    ( m1_subset_1(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16296,c_2248,c_2247,c_30,c_42,c_41,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.99/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/0.98  
% 3.99/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.99/0.98  
% 3.99/0.98  ------  iProver source info
% 3.99/0.98  
% 3.99/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.99/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.99/0.98  git: non_committed_changes: false
% 3.99/0.98  git: last_make_outside_of_git: false
% 3.99/0.98  
% 3.99/0.98  ------ 
% 3.99/0.98  ------ Parsing...
% 3.99/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.99/0.98  
% 3.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.99/0.98  
% 3.99/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.99/0.98  
% 3.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.99/0.98  ------ Proving...
% 3.99/0.98  ------ Problem Properties 
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  clauses                                 37
% 3.99/0.98  conjectures                             8
% 3.99/0.98  EPR                                     17
% 3.99/0.98  Horn                                    31
% 3.99/0.98  unary                                   10
% 3.99/0.98  binary                                  12
% 3.99/0.98  lits                                    88
% 3.99/0.98  lits eq                                 17
% 3.99/0.98  fd_pure                                 0
% 3.99/0.98  fd_pseudo                               0
% 3.99/0.98  fd_cond                                 1
% 3.99/0.98  fd_pseudo_cond                          4
% 3.99/0.98  AC symbols                              0
% 3.99/0.98  
% 3.99/0.98  ------ Input Options Time Limit: Unbounded
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  ------ 
% 3.99/0.98  Current options:
% 3.99/0.98  ------ 
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  ------ Proving...
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  % SZS status Theorem for theBenchmark.p
% 3.99/0.98  
% 3.99/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.99/0.98  
% 3.99/0.98  fof(f10,axiom,(
% 3.99/0.98    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)))))))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f18,plain,(
% 3.99/0.98    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 3.99/0.98    inference(ennf_transformation,[],[f10])).
% 3.99/0.98  
% 3.99/0.98  fof(f19,plain,(
% 3.99/0.98    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 3.99/0.98    inference(flattening,[],[f18])).
% 3.99/0.98  
% 3.99/0.98  fof(f77,plain,(
% 3.99/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f19])).
% 3.99/0.98  
% 3.99/0.98  fof(f7,axiom,(
% 3.99/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f16,plain,(
% 3.99/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.99/0.98    inference(ennf_transformation,[],[f7])).
% 3.99/0.98  
% 3.99/0.98  fof(f40,plain,(
% 3.99/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.99/0.98    inference(nnf_transformation,[],[f16])).
% 3.99/0.98  
% 3.99/0.98  fof(f71,plain,(
% 3.99/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f40])).
% 3.99/0.98  
% 3.99/0.98  fof(f8,axiom,(
% 3.99/0.98    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f75,plain,(
% 3.99/0.98    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.99/0.98    inference(cnf_transformation,[],[f8])).
% 3.99/0.98  
% 3.99/0.98  fof(f4,axiom,(
% 3.99/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f28,plain,(
% 3.99/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.99/0.98    inference(nnf_transformation,[],[f4])).
% 3.99/0.98  
% 3.99/0.98  fof(f29,plain,(
% 3.99/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.99/0.98    inference(rectify,[],[f28])).
% 3.99/0.98  
% 3.99/0.98  fof(f30,plain,(
% 3.99/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f31,plain,(
% 3.99/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 3.99/0.98  
% 3.99/0.98  fof(f52,plain,(
% 3.99/0.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.99/0.98    inference(cnf_transformation,[],[f31])).
% 3.99/0.98  
% 3.99/0.98  fof(f88,plain,(
% 3.99/0.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.99/0.98    inference(equality_resolution,[],[f52])).
% 3.99/0.98  
% 3.99/0.98  fof(f2,axiom,(
% 3.99/0.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f13,plain,(
% 3.99/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.99/0.98    inference(ennf_transformation,[],[f2])).
% 3.99/0.98  
% 3.99/0.98  fof(f14,plain,(
% 3.99/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.99/0.98    inference(flattening,[],[f13])).
% 3.99/0.98  
% 3.99/0.98  fof(f50,plain,(
% 3.99/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f14])).
% 3.99/0.98  
% 3.99/0.98  fof(f53,plain,(
% 3.99/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.99/0.98    inference(cnf_transformation,[],[f31])).
% 3.99/0.98  
% 3.99/0.98  fof(f87,plain,(
% 3.99/0.98    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.99/0.98    inference(equality_resolution,[],[f53])).
% 3.99/0.98  
% 3.99/0.98  fof(f72,plain,(
% 3.99/0.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f40])).
% 3.99/0.98  
% 3.99/0.98  fof(f1,axiom,(
% 3.99/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f24,plain,(
% 3.99/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.99/0.98    inference(nnf_transformation,[],[f1])).
% 3.99/0.98  
% 3.99/0.98  fof(f25,plain,(
% 3.99/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.99/0.98    inference(rectify,[],[f24])).
% 3.99/0.98  
% 3.99/0.98  fof(f26,plain,(
% 3.99/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f27,plain,(
% 3.99/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 3.99/0.98  
% 3.99/0.98  fof(f48,plain,(
% 3.99/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f27])).
% 3.99/0.98  
% 3.99/0.98  fof(f11,conjecture,(
% 3.99/0.98    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f12,negated_conjecture,(
% 3.99/0.98    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 3.99/0.98    inference(negated_conjecture,[],[f11])).
% 3.99/0.98  
% 3.99/0.98  fof(f20,plain,(
% 3.99/0.98    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 3.99/0.98    inference(ennf_transformation,[],[f12])).
% 3.99/0.98  
% 3.99/0.98  fof(f21,plain,(
% 3.99/0.98    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 3.99/0.98    inference(flattening,[],[f20])).
% 3.99/0.98  
% 3.99/0.98  fof(f46,plain,(
% 3.99/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) => (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,sK10),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(sK10,X0))) )),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f45,plain,(
% 3.99/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) => (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,sK9,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(sK9,X0))) )),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f44,plain,(
% 3.99/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,sK8,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(sK8,X0))) )),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f43,plain,(
% 3.99/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) => (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,sK7,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(sK7,X0))) )),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f42,plain,(
% 3.99/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,sK6,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(sK6,X0))) )),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f41,plain,(
% 3.99/0.98    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK5,X2,X3,X4,X5,X6),k1_zfmisc_1(sK4)) & k1_xboole_0 != sK4 & m1_subset_1(X6,sK4)) & m1_subset_1(X5,sK4)) & m1_subset_1(X4,sK4)) & m1_subset_1(X3,sK4)) & m1_subset_1(X2,sK4)) & m1_subset_1(sK5,sK4))),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f47,plain,(
% 3.99/0.98    (((((~m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4)) & k1_xboole_0 != sK4 & m1_subset_1(sK10,sK4)) & m1_subset_1(sK9,sK4)) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,sK4)) & m1_subset_1(sK6,sK4)) & m1_subset_1(sK5,sK4)),
% 3.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f21,f46,f45,f44,f43,f42,f41])).
% 3.99/0.98  
% 3.99/0.98  fof(f85,plain,(
% 3.99/0.98    ~m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4))),
% 3.99/0.98    inference(cnf_transformation,[],[f47])).
% 3.99/0.98  
% 3.99/0.98  fof(f3,axiom,(
% 3.99/0.98    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f51,plain,(
% 3.99/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f3])).
% 3.99/0.98  
% 3.99/0.98  fof(f86,plain,(
% 3.99/0.98    ~m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4))),
% 3.99/0.98    inference(definition_unfolding,[],[f85,f51])).
% 3.99/0.98  
% 3.99/0.98  fof(f78,plain,(
% 3.99/0.98    m1_subset_1(sK5,sK4)),
% 3.99/0.98    inference(cnf_transformation,[],[f47])).
% 3.99/0.98  
% 3.99/0.98  fof(f79,plain,(
% 3.99/0.98    m1_subset_1(sK6,sK4)),
% 3.99/0.98    inference(cnf_transformation,[],[f47])).
% 3.99/0.98  
% 3.99/0.98  fof(f83,plain,(
% 3.99/0.98    m1_subset_1(sK10,sK4)),
% 3.99/0.98    inference(cnf_transformation,[],[f47])).
% 3.99/0.98  
% 3.99/0.98  fof(f84,plain,(
% 3.99/0.98    k1_xboole_0 != sK4),
% 3.99/0.98    inference(cnf_transformation,[],[f47])).
% 3.99/0.98  
% 3.99/0.98  fof(f74,plain,(
% 3.99/0.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f40])).
% 3.99/0.98  
% 3.99/0.98  fof(f22,plain,(
% 3.99/0.98    ! [X3,X2,X1,X0,X4] : (sP0(X3,X2,X1,X0,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 3.99/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.99/0.98  
% 3.99/0.98  fof(f34,plain,(
% 3.99/0.98    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 3.99/0.98    inference(nnf_transformation,[],[f22])).
% 3.99/0.98  
% 3.99/0.98  fof(f35,plain,(
% 3.99/0.98    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 3.99/0.98    inference(flattening,[],[f34])).
% 3.99/0.98  
% 3.99/0.98  fof(f36,plain,(
% 3.99/0.98    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.99/0.98    inference(rectify,[],[f35])).
% 3.99/0.98  
% 3.99/0.98  fof(f37,plain,(
% 3.99/0.98    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4))) => (((sK3(X0,X1,X2,X3,X4) != X0 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X0 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4))))),
% 3.99/0.98    introduced(choice_axiom,[])).
% 3.99/0.98  
% 3.99/0.98  fof(f38,plain,(
% 3.99/0.98    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (((sK3(X0,X1,X2,X3,X4) != X0 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X0 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 3.99/0.98  
% 3.99/0.98  fof(f60,plain,(
% 3.99/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f38])).
% 3.99/0.98  
% 3.99/0.98  fof(f92,plain,(
% 3.99/0.98    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | ~sP0(X0,X1,X2,X6,X4)) )),
% 3.99/0.98    inference(equality_resolution,[],[f60])).
% 3.99/0.98  
% 3.99/0.98  fof(f6,axiom,(
% 3.99/0.98    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f15,plain,(
% 3.99/0.98    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 3.99/0.98    inference(ennf_transformation,[],[f6])).
% 3.99/0.98  
% 3.99/0.98  fof(f23,plain,(
% 3.99/0.98    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP0(X3,X2,X1,X0,X4))),
% 3.99/0.98    inference(definition_folding,[],[f15,f22])).
% 3.99/0.98  
% 3.99/0.98  fof(f39,plain,(
% 3.99/0.98    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP0(X3,X2,X1,X0,X4)) & (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 3.99/0.98    inference(nnf_transformation,[],[f23])).
% 3.99/0.98  
% 3.99/0.98  fof(f69,plain,(
% 3.99/0.98    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 3.99/0.98    inference(cnf_transformation,[],[f39])).
% 3.99/0.98  
% 3.99/0.98  fof(f93,plain,(
% 3.99/0.98    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3))) )),
% 3.99/0.98    inference(equality_resolution,[],[f69])).
% 3.99/0.98  
% 3.99/0.98  fof(f9,axiom,(
% 3.99/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f17,plain,(
% 3.99/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.99/0.98    inference(ennf_transformation,[],[f9])).
% 3.99/0.98  
% 3.99/0.98  fof(f76,plain,(
% 3.99/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.99/0.98    inference(cnf_transformation,[],[f17])).
% 3.99/0.98  
% 3.99/0.98  fof(f5,axiom,(
% 3.99/0.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/0.98  
% 3.99/0.98  fof(f32,plain,(
% 3.99/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.99/0.98    inference(nnf_transformation,[],[f5])).
% 3.99/0.98  
% 3.99/0.98  fof(f33,plain,(
% 3.99/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.99/0.98    inference(flattening,[],[f32])).
% 3.99/0.98  
% 3.99/0.98  fof(f58,plain,(
% 3.99/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.99/0.98    inference(cnf_transformation,[],[f33])).
% 3.99/0.98  
% 3.99/0.98  fof(f82,plain,(
% 3.99/0.98    m1_subset_1(sK9,sK4)),
% 3.99/0.98    inference(cnf_transformation,[],[f47])).
% 3.99/0.98  
% 3.99/0.98  fof(f81,plain,(
% 3.99/0.98    m1_subset_1(sK8,sK4)),
% 3.99/0.98    inference(cnf_transformation,[],[f47])).
% 3.99/0.98  
% 3.99/0.98  fof(f80,plain,(
% 3.99/0.98    m1_subset_1(sK7,sK4)),
% 3.99/0.98    inference(cnf_transformation,[],[f47])).
% 3.99/0.98  
% 3.99/0.98  cnf(c_28,plain,
% 3.99/0.98      ( ~ m1_subset_1(X0,X1)
% 3.99/0.98      | ~ m1_subset_1(X2,X1)
% 3.99/0.98      | ~ m1_subset_1(X3,X1)
% 3.99/0.98      | ~ m1_subset_1(X4,X1)
% 3.99/0.98      | m1_subset_1(k2_enumset1(X0,X4,X3,X2),k1_zfmisc_1(X1))
% 3.99/0.98      | k1_xboole_0 = X1 ),
% 3.99/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_1991,plain,
% 3.99/0.98      ( k1_xboole_0 = X0
% 3.99/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X3,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X4,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(k2_enumset1(X1,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_25,plain,
% 3.99/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.99/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_1994,plain,
% 3.99/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.99/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.99/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_3384,plain,
% 3.99/0.98      ( k1_xboole_0 = X0
% 3.99/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X3,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X4,X0) != iProver_top
% 3.99/0.98      | r2_hidden(k2_enumset1(X1,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
% 3.99/0.98      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_1991,c_1994]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_26,plain,
% 3.99/0.98      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.99/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_48,plain,
% 3.99/0.98      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_7734,plain,
% 3.99/0.98      ( r2_hidden(k2_enumset1(X1,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
% 3.99/0.98      | m1_subset_1(X4,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X3,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.99/0.98      | k1_xboole_0 = X0 ),
% 3.99/0.98      inference(global_propositional_subsumption,
% 3.99/0.98                [status(thm)],
% 3.99/0.98                [c_3384,c_48]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_7735,plain,
% 3.99/0.98      ( k1_xboole_0 = X0
% 3.99/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X3,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X4,X0) != iProver_top
% 3.99/0.98      | r2_hidden(k2_enumset1(X1,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 3.99/0.98      inference(renaming,[status(thm)],[c_7734]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_6,plain,
% 3.99/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.99/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2012,plain,
% 3.99/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.99/0.98      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_7742,plain,
% 3.99/0.98      ( k1_xboole_0 = X0
% 3.99/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X3,X0) != iProver_top
% 3.99/0.98      | m1_subset_1(X4,X0) != iProver_top
% 3.99/0.98      | r1_tarski(k2_enumset1(X1,X4,X3,X2),X0) = iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_7735,c_2012]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2,plain,
% 3.99/0.98      ( ~ r1_tarski(X0,X1)
% 3.99/0.98      | ~ r1_tarski(X2,X1)
% 3.99/0.98      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 3.99/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2016,plain,
% 3.99/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.99/0.98      | r1_tarski(X2,X1) != iProver_top
% 3.99/0.98      | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_5,plain,
% 3.99/0.98      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.99/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2013,plain,
% 3.99/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.99/0.98      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_24,plain,
% 3.99/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.99/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_1,plain,
% 3.99/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.99/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_197,plain,
% 3.99/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.99/0.98      inference(global_propositional_subsumption,
% 3.99/0.98                [status(thm)],
% 3.99/0.98                [c_24,c_1]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_198,plain,
% 3.99/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.99/0.98      inference(renaming,[status(thm)],[c_197]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_1983,plain,
% 3.99/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.99/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_198]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2587,plain,
% 3.99/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.99/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_2013,c_1983]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_29,negated_conjecture,
% 3.99/0.98      ( ~ m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
% 3.99/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_1990,plain,
% 3.99/0.98      ( m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_6531,plain,
% 3.99/0.98      ( r1_tarski(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),sK4) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_2587,c_1990]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_7747,plain,
% 3.99/0.98      ( r1_tarski(k2_enumset1(sK7,sK8,sK9,sK10),sK4) != iProver_top
% 3.99/0.98      | r1_tarski(k2_tarski(sK5,sK6),sK4) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_2016,c_6531]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_36,negated_conjecture,
% 3.99/0.98      ( m1_subset_1(sK5,sK4) ),
% 3.99/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_37,plain,
% 3.99/0.98      ( m1_subset_1(sK5,sK4) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_35,negated_conjecture,
% 3.99/0.98      ( m1_subset_1(sK6,sK4) ),
% 3.99/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_38,plain,
% 3.99/0.98      ( m1_subset_1(sK6,sK4) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2526,plain,
% 3.99/0.98      ( ~ m1_subset_1(sK6,sK4) | r2_hidden(sK6,sK4) | v1_xboole_0(sK4) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2527,plain,
% 3.99/0.98      ( m1_subset_1(sK6,sK4) != iProver_top
% 3.99/0.98      | r2_hidden(sK6,sK4) = iProver_top
% 3.99/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2526]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2529,plain,
% 3.99/0.98      ( ~ m1_subset_1(sK5,sK4) | r2_hidden(sK5,sK4) | v1_xboole_0(sK4) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2530,plain,
% 3.99/0.98      ( m1_subset_1(sK5,sK4) != iProver_top
% 3.99/0.98      | r2_hidden(sK5,sK4) = iProver_top
% 3.99/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2529]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_31,negated_conjecture,
% 3.99/0.98      ( m1_subset_1(sK10,sK4) ),
% 3.99/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2727,plain,
% 3.99/0.98      ( r2_hidden(sK10,sK4) | v1_xboole_0(sK4) ),
% 3.99/0.98      inference(resolution,[status(thm)],[c_25,c_31]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_30,negated_conjecture,
% 3.99/0.98      ( k1_xboole_0 != sK4 ),
% 3.99/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_45,plain,
% 3.99/0.98      ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
% 3.99/0.98      | ~ m1_subset_1(sK4,sK4)
% 3.99/0.98      | k1_xboole_0 = sK4 ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_28]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_22,plain,
% 3.99/0.98      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 3.99/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_59,plain,
% 3.99/0.98      ( m1_subset_1(sK4,sK4) | ~ v1_xboole_0(sK4) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_108,plain,
% 3.99/0.98      ( ~ r2_hidden(sK4,sK4) | ~ v1_xboole_0(sK4) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_18,plain,
% 3.99/0.98      ( ~ sP0(X0,X1,X2,X3,X4) | r2_hidden(X3,X4) ),
% 3.99/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_21,plain,
% 3.99/0.98      ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
% 3.99/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_976,plain,
% 3.99/0.98      ( r2_hidden(X0,X1)
% 3.99/0.98      | X2 != X3
% 3.99/0.98      | X4 != X0
% 3.99/0.98      | X5 != X6
% 3.99/0.98      | X7 != X8
% 3.99/0.98      | k2_enumset1(X4,X5,X7,X2) != X1 ),
% 3.99/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_977,plain,
% 3.99/0.98      ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
% 3.99/0.98      inference(unflattening,[status(thm)],[c_976]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_979,plain,
% 3.99/0.98      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_977]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_27,plain,
% 3.99/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.99/0.98      | ~ r2_hidden(X2,X0)
% 3.99/0.98      | r2_hidden(X2,X1) ),
% 3.99/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2355,plain,
% 3.99/0.98      ( ~ m1_subset_1(k2_enumset1(X0,X1,X2,X3),k1_zfmisc_1(X4))
% 3.99/0.98      | r2_hidden(X3,X4)
% 3.99/0.98      | ~ r2_hidden(X3,k2_enumset1(X0,X1,X2,X3)) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_27]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2357,plain,
% 3.99/0.98      ( ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
% 3.99/0.98      | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.99/0.98      | r2_hidden(sK4,sK4) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_2355]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2514,plain,
% 3.99/0.98      ( ~ m1_subset_1(sK10,sK4)
% 3.99/0.98      | r2_hidden(sK10,sK4)
% 3.99/0.98      | v1_xboole_0(sK4) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2920,plain,
% 3.99/0.98      ( r2_hidden(sK10,sK4) ),
% 3.99/0.98      inference(global_propositional_subsumption,
% 3.99/0.98                [status(thm)],
% 3.99/0.98                [c_2727,c_31,c_30,c_45,c_59,c_108,c_979,c_2357,c_2514]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2922,plain,
% 3.99/0.98      ( r2_hidden(sK10,sK4) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_2920]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_3090,plain,
% 3.99/0.98      ( ~ r2_hidden(sK10,sK4) | ~ v1_xboole_0(sK4) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_3092,plain,
% 3.99/0.98      ( r2_hidden(sK10,sK4) != iProver_top
% 3.99/0.98      | v1_xboole_0(sK4) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_3090]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2481,plain,
% 3.99/0.98      ( ~ r2_hidden(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
% 3.99/0.98      inference(resolution,[status(thm)],[c_29,c_198]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2607,plain,
% 3.99/0.98      ( ~ r1_tarski(k2_xboole_0(k2_tarski(sK5,sK6),k2_enumset1(sK7,sK8,sK9,sK10)),sK4) ),
% 3.99/0.98      inference(resolution,[status(thm)],[c_2481,c_5]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_5604,plain,
% 3.99/0.98      ( ~ r1_tarski(k2_enumset1(sK7,sK8,sK9,sK10),sK4)
% 3.99/0.98      | ~ r1_tarski(k2_tarski(sK5,sK6),sK4) ),
% 3.99/0.98      inference(resolution,[status(thm)],[c_2607,c_2]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_5605,plain,
% 3.99/0.98      ( r1_tarski(k2_enumset1(sK7,sK8,sK9,sK10),sK4) != iProver_top
% 3.99/0.98      | r1_tarski(k2_tarski(sK5,sK6),sK4) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_5604]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_7,plain,
% 3.99/0.98      ( r1_tarski(k2_tarski(X0,X1),X2)
% 3.99/0.98      | ~ r2_hidden(X0,X2)
% 3.99/0.98      | ~ r2_hidden(X1,X2) ),
% 3.99/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_3213,plain,
% 3.99/0.98      ( r1_tarski(k2_tarski(X0,sK6),sK4)
% 3.99/0.98      | ~ r2_hidden(X0,sK4)
% 3.99/0.98      | ~ r2_hidden(sK6,sK4) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_6290,plain,
% 3.99/0.98      ( r1_tarski(k2_tarski(sK5,sK6),sK4)
% 3.99/0.98      | ~ r2_hidden(sK6,sK4)
% 3.99/0.98      | ~ r2_hidden(sK5,sK4) ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_3213]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_6291,plain,
% 3.99/0.98      ( r1_tarski(k2_tarski(sK5,sK6),sK4) = iProver_top
% 3.99/0.98      | r2_hidden(sK6,sK4) != iProver_top
% 3.99/0.98      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_6290]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_8938,plain,
% 3.99/0.98      ( r1_tarski(k2_enumset1(sK7,sK8,sK9,sK10),sK4) != iProver_top ),
% 3.99/0.98      inference(global_propositional_subsumption,
% 3.99/0.98                [status(thm)],
% 3.99/0.98                [c_7747,c_37,c_38,c_2527,c_2530,c_2922,c_3092,c_5605,
% 3.99/0.98                 c_6291]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_16296,plain,
% 3.99/0.98      ( sK4 = k1_xboole_0
% 3.99/0.98      | m1_subset_1(sK10,sK4) != iProver_top
% 3.99/0.98      | m1_subset_1(sK9,sK4) != iProver_top
% 3.99/0.98      | m1_subset_1(sK8,sK4) != iProver_top
% 3.99/0.98      | m1_subset_1(sK7,sK4) != iProver_top ),
% 3.99/0.98      inference(superposition,[status(thm)],[c_7742,c_8938]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_1144,plain,( X0 = X0 ),theory(equality) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2248,plain,
% 3.99/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_1144]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_1145,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2151,plain,
% 3.99/0.98      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_1145]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_2247,plain,
% 3.99/0.98      ( sK4 != k1_xboole_0
% 3.99/0.98      | k1_xboole_0 = sK4
% 3.99/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.99/0.98      inference(instantiation,[status(thm)],[c_2151]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_42,plain,
% 3.99/0.98      ( m1_subset_1(sK10,sK4) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_32,negated_conjecture,
% 3.99/0.98      ( m1_subset_1(sK9,sK4) ),
% 3.99/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_41,plain,
% 3.99/0.98      ( m1_subset_1(sK9,sK4) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_33,negated_conjecture,
% 3.99/0.98      ( m1_subset_1(sK8,sK4) ),
% 3.99/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_40,plain,
% 3.99/0.98      ( m1_subset_1(sK8,sK4) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_34,negated_conjecture,
% 3.99/0.98      ( m1_subset_1(sK7,sK4) ),
% 3.99/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(c_39,plain,
% 3.99/0.98      ( m1_subset_1(sK7,sK4) = iProver_top ),
% 3.99/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.99/0.98  
% 3.99/0.98  cnf(contradiction,plain,
% 3.99/0.98      ( $false ),
% 3.99/0.98      inference(minisat,
% 3.99/0.98                [status(thm)],
% 3.99/0.98                [c_16296,c_2248,c_2247,c_30,c_42,c_41,c_40,c_39]) ).
% 3.99/0.98  
% 3.99/0.98  
% 3.99/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.99/0.98  
% 3.99/0.98  ------                               Statistics
% 3.99/0.98  
% 3.99/0.98  ------ Selected
% 3.99/0.98  
% 3.99/0.98  total_time:                             0.46
% 3.99/0.98  
%------------------------------------------------------------------------------
