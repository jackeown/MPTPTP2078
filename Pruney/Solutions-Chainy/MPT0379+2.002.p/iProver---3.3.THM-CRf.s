%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:11 EST 2020

% Result     : Theorem 11.47s
% Output     : CNFRefutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 379 expanded)
%              Number of clauses        :   76 (  92 expanded)
%              Number of leaves         :   24 ( 140 expanded)
%              Depth                    :   15
%              Number of atoms          :  675 (2606 expanded)
%              Number of equality atoms :  286 ( 544 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ! [X6] :
                          ( m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          | k1_xboole_0 = X0
                          | ~ m1_subset_1(X6,X0) )
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ! [X6] :
                          ( m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          | k1_xboole_0 = X0
                          | ~ m1_subset_1(X6,X0) )
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f19])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
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

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,conjecture,(
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
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ( k1_xboole_0 != X0
                               => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
                           => ! [X7] :
                                ( m1_subset_1(X7,X0)
                               => ( k1_xboole_0 != X0
                                 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X7,X0) )
     => ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,sK11),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK11,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X7,X0) )
          & m1_subset_1(X6,X0) )
     => ( ? [X7] :
            ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,sK10,X7),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X7,X0) )
        & m1_subset_1(sK10,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X7,X0) )
              & m1_subset_1(X6,X0) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,sK9,X6,X7),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X7,X0) )
            & m1_subset_1(X6,X0) )
        & m1_subset_1(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X7,X0) )
                  & m1_subset_1(X6,X0) )
              & m1_subset_1(X5,X0) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,sK8,X5,X6,X7),k1_zfmisc_1(X0))
                    & k1_xboole_0 != X0
                    & m1_subset_1(X7,X0) )
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
                      ( ? [X7] :
                          ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X7,X0) )
                      & m1_subset_1(X6,X0) )
                  & m1_subset_1(X5,X0) )
              & m1_subset_1(X4,X0) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ~ m1_subset_1(k5_enumset1(X1,X2,sK7,X4,X5,X6,X7),k1_zfmisc_1(X0))
                        & k1_xboole_0 != X0
                        & m1_subset_1(X7,X0) )
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
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ~ m1_subset_1(k5_enumset1(X1,sK6,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                            & k1_xboole_0 != X0
                            & m1_subset_1(X7,X0) )
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
                            ( ? [X7] :
                                ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                                & k1_xboole_0 != X0
                                & m1_subset_1(X7,X0) )
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
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(sK5,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK4))
                              & k1_xboole_0 != sK4
                              & m1_subset_1(X7,sK4) )
                          & m1_subset_1(X6,sK4) )
                      & m1_subset_1(X5,sK4) )
                  & m1_subset_1(X4,sK4) )
              & m1_subset_1(X3,sK4) )
          & m1_subset_1(X2,sK4) )
      & m1_subset_1(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ~ m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4))
    & k1_xboole_0 != sK4
    & m1_subset_1(sK11,sK4)
    & m1_subset_1(sK10,sK4)
    & m1_subset_1(sK9,sK4)
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,sK4)
    & m1_subset_1(sK6,sK4)
    & m1_subset_1(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f22,f47,f46,f45,f44,f43,f42,f41])).

fof(f91,plain,(
    ~ m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f3])).

fof(f93,plain,(
    ~ m1_subset_1(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) ),
    inference(definition_unfolding,[],[f91,f52])).

fof(f83,plain,(
    m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    m1_subset_1(sK11,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f48])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f23,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7
                & X5 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | X5 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X0 != X7
              & X1 != X7
              & X2 != X7
              & X3 != X7
              & X4 != X7
              & X5 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X0 = X7
            | X1 = X7
            | X2 = X7
            | X3 = X7
            | X4 = X7
            | X5 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X0
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X5 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X0
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X5
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X0
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X5 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X0
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X5
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X0,X1,X2,X3,X4,X8,X6) ) ),
    inference(equality_resolution,[],[f65])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP0(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f17,f23])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f78])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X6,X1)
    | m1_subset_1(k4_enumset1(X0,X6,X5,X4,X3,X2),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2718,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X6,X0) != iProver_top
    | m1_subset_1(k4_enumset1(X1,X6,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2737,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4664,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X6,X0) != iProver_top
    | r2_hidden(k4_enumset1(X1,X6,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2718,c_2737])).

cnf(c_30,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_54,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12206,plain,
    ( r2_hidden(k4_enumset1(X1,X6,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(X6,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4664,c_54])).

cnf(c_12207,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X6,X0) != iProver_top
    | r2_hidden(k4_enumset1(X1,X6,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12206])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2742,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12215,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X6,X0) != iProver_top
    | r1_tarski(k4_enumset1(X1,X6,X5,X4,X3,X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12207,c_2742])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2746,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2743,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_1])).

cnf(c_233,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_2709,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_3605,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_2709])).

cnf(c_33,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2717,plain,
    ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8571,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3605,c_2717])).

cnf(c_12697,plain,
    ( r1_tarski(k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11),sK4) != iProver_top
    | r1_tarski(k1_tarski(sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2746,c_8571])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_42,plain,
    ( m1_subset_1(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3337,plain,
    ( ~ m1_subset_1(sK5,sK4)
    | r2_hidden(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3338,plain,
    ( m1_subset_1(sK5,sK4) != iProver_top
    | r2_hidden(sK5,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3337])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK11,sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3479,plain,
    ( r2_hidden(sK11,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_13,c_35])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_51,plain,
    ( m1_subset_1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK4,sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_93,plain,
    ( m1_subset_1(sK4,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_118,plain,
    ( ~ r2_hidden(sK4,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X5,X6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_29,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k4_enumset1(X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1480,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | X11 != X12
    | k4_enumset1(X4,X5,X7,X9,X11,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_1481,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(unflattening,[status(thm)],[c_1480])).

cnf(c_1483,plain,
    ( r2_hidden(sK4,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3108,plain,
    ( ~ m1_subset_1(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(X6))
    | r2_hidden(X5,X6)
    | ~ r2_hidden(X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3110,plain,
    ( ~ m1_subset_1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK4,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_3108])).

cnf(c_3319,plain,
    ( ~ m1_subset_1(sK11,sK4)
    | r2_hidden(sK11,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3613,plain,
    ( r2_hidden(sK11,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3479,c_35,c_34,c_51,c_93,c_118,c_1483,c_3110,c_3319])).

cnf(c_3615,plain,
    ( r2_hidden(sK11,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3613])).

cnf(c_3870,plain,
    ( ~ r2_hidden(sK11,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3875,plain,
    ( r2_hidden(sK11,sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3870])).

cnf(c_8,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4021,plain,
    ( r1_tarski(k1_tarski(sK5),sK4)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4022,plain,
    ( r1_tarski(k1_tarski(sK5),sK4) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4021])).

cnf(c_3203,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) ),
    inference(resolution,[status(thm)],[c_33,c_233])).

cnf(c_3209,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),sK4) ),
    inference(resolution,[status(thm)],[c_3203,c_6])).

cnf(c_6554,plain,
    ( ~ r1_tarski(k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11),sK4)
    | ~ r1_tarski(k1_tarski(sK5),sK4) ),
    inference(resolution,[status(thm)],[c_3209,c_2])).

cnf(c_6555,plain,
    ( r1_tarski(k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11),sK4) != iProver_top
    | r1_tarski(k1_tarski(sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6554])).

cnf(c_16665,plain,
    ( r1_tarski(k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12697,c_42,c_3338,c_3615,c_3875,c_4022,c_6555])).

cnf(c_35610,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK11,sK4) != iProver_top
    | m1_subset_1(sK10,sK4) != iProver_top
    | m1_subset_1(sK9,sK4) != iProver_top
    | m1_subset_1(sK8,sK4) != iProver_top
    | m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12215,c_16665])).

cnf(c_1774,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3016,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_1775,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2888,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_3015,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2888])).

cnf(c_48,plain,
    ( m1_subset_1(sK11,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_47,plain,
    ( m1_subset_1(sK10,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_46,plain,
    ( m1_subset_1(sK9,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_45,plain,
    ( m1_subset_1(sK8,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( m1_subset_1(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_43,plain,
    ( m1_subset_1(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35610,c_3016,c_3015,c_34,c_48,c_47,c_46,c_45,c_44,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:01:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.47/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.47/1.99  
% 11.47/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.47/1.99  
% 11.47/1.99  ------  iProver source info
% 11.47/1.99  
% 11.47/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.47/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.47/1.99  git: non_committed_changes: false
% 11.47/1.99  git: last_make_outside_of_git: false
% 11.47/1.99  
% 11.47/1.99  ------ 
% 11.47/1.99  ------ Parsing...
% 11.47/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.47/1.99  
% 11.47/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.47/1.99  
% 11.47/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.47/1.99  
% 11.47/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.47/1.99  ------ Proving...
% 11.47/1.99  ------ Problem Properties 
% 11.47/1.99  
% 11.47/1.99  
% 11.47/1.99  clauses                                 42
% 11.47/1.99  conjectures                             9
% 11.47/1.99  EPR                                     20
% 11.47/1.99  Horn                                    36
% 11.47/1.99  unary                                   12
% 11.47/1.99  binary                                  14
% 11.47/1.99  lits                                    103
% 11.47/1.99  lits eq                                 24
% 11.47/1.99  fd_pure                                 0
% 11.47/1.99  fd_pseudo                               0
% 11.47/1.99  fd_cond                                 1
% 11.47/1.99  fd_pseudo_cond                          4
% 11.47/1.99  AC symbols                              0
% 11.47/1.99  
% 11.47/1.99  ------ Input Options Time Limit: Unbounded
% 11.47/1.99  
% 11.47/1.99  
% 11.47/1.99  ------ 
% 11.47/1.99  Current options:
% 11.47/1.99  ------ 
% 11.47/1.99  
% 11.47/1.99  
% 11.47/1.99  
% 11.47/1.99  
% 11.47/1.99  ------ Proving...
% 11.47/1.99  
% 11.47/1.99  
% 11.47/1.99  % SZS status Theorem for theBenchmark.p
% 11.47/1.99  
% 11.47/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.47/1.99  
% 11.47/1.99  fof(f11,axiom,(
% 11.47/1.99    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f19,plain,(
% 11.47/1.99    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 11.47/1.99    inference(ennf_transformation,[],[f11])).
% 11.47/1.99  
% 11.47/1.99  fof(f20,plain,(
% 11.47/1.99    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 11.47/1.99    inference(flattening,[],[f19])).
% 11.47/1.99  
% 11.47/1.99  fof(f82,plain,(
% 11.47/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X6,X0) | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f20])).
% 11.47/1.99  
% 11.47/1.99  fof(f7,axiom,(
% 11.47/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f16,plain,(
% 11.47/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.47/1.99    inference(ennf_transformation,[],[f7])).
% 11.47/1.99  
% 11.47/1.99  fof(f34,plain,(
% 11.47/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.47/1.99    inference(nnf_transformation,[],[f16])).
% 11.47/1.99  
% 11.47/1.99  fof(f60,plain,(
% 11.47/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f34])).
% 11.47/1.99  
% 11.47/1.99  fof(f9,axiom,(
% 11.47/1.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f80,plain,(
% 11.47/1.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.47/1.99    inference(cnf_transformation,[],[f9])).
% 11.47/1.99  
% 11.47/1.99  fof(f5,axiom,(
% 11.47/1.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f29,plain,(
% 11.47/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.47/1.99    inference(nnf_transformation,[],[f5])).
% 11.47/1.99  
% 11.47/1.99  fof(f30,plain,(
% 11.47/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.47/1.99    inference(rectify,[],[f29])).
% 11.47/1.99  
% 11.47/1.99  fof(f31,plain,(
% 11.47/1.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f32,plain,(
% 11.47/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.47/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 11.47/1.99  
% 11.47/1.99  fof(f54,plain,(
% 11.47/1.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.47/1.99    inference(cnf_transformation,[],[f32])).
% 11.47/1.99  
% 11.47/1.99  fof(f95,plain,(
% 11.47/1.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.47/1.99    inference(equality_resolution,[],[f54])).
% 11.47/1.99  
% 11.47/1.99  fof(f2,axiom,(
% 11.47/1.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f14,plain,(
% 11.47/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 11.47/1.99    inference(ennf_transformation,[],[f2])).
% 11.47/1.99  
% 11.47/1.99  fof(f15,plain,(
% 11.47/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 11.47/1.99    inference(flattening,[],[f14])).
% 11.47/1.99  
% 11.47/1.99  fof(f51,plain,(
% 11.47/1.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f15])).
% 11.47/1.99  
% 11.47/1.99  fof(f55,plain,(
% 11.47/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 11.47/1.99    inference(cnf_transformation,[],[f32])).
% 11.47/1.99  
% 11.47/1.99  fof(f94,plain,(
% 11.47/1.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 11.47/1.99    inference(equality_resolution,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f61,plain,(
% 11.47/1.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f34])).
% 11.47/1.99  
% 11.47/1.99  fof(f1,axiom,(
% 11.47/1.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f25,plain,(
% 11.47/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.47/1.99    inference(nnf_transformation,[],[f1])).
% 11.47/1.99  
% 11.47/1.99  fof(f26,plain,(
% 11.47/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.47/1.99    inference(rectify,[],[f25])).
% 11.47/1.99  
% 11.47/1.99  fof(f27,plain,(
% 11.47/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f28,plain,(
% 11.47/1.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.47/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 11.47/1.99  
% 11.47/1.99  fof(f49,plain,(
% 11.47/1.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f28])).
% 11.47/1.99  
% 11.47/1.99  fof(f12,conjecture,(
% 11.47/1.99    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => (k1_xboole_0 != X0 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))))))))))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f13,negated_conjecture,(
% 11.47/1.99    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => (k1_xboole_0 != X0 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))))))))))),
% 11.47/1.99    inference(negated_conjecture,[],[f12])).
% 11.47/1.99  
% 11.47/1.99  fof(f21,plain,(
% 11.47/1.99    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 11.47/1.99    inference(ennf_transformation,[],[f13])).
% 11.47/1.99  
% 11.47/1.99  fof(f22,plain,(
% 11.47/1.99    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 11.47/1.99    inference(flattening,[],[f21])).
% 11.47/1.99  
% 11.47/1.99  fof(f47,plain,(
% 11.47/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) => (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,sK11),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(sK11,X0))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f46,plain,(
% 11.47/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) => (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,sK10,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(sK10,X0))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f45,plain,(
% 11.47/1.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,sK9,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(sK9,X0))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f44,plain,(
% 11.47/1.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,sK8,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(sK8,X0))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f43,plain,(
% 11.47/1.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,sK7,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(sK7,X0))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f42,plain,(
% 11.47/1.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,sK6,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(sK6,X0))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f41,plain,(
% 11.47/1.99    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK5,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK4)) & k1_xboole_0 != sK4 & m1_subset_1(X7,sK4)) & m1_subset_1(X6,sK4)) & m1_subset_1(X5,sK4)) & m1_subset_1(X4,sK4)) & m1_subset_1(X3,sK4)) & m1_subset_1(X2,sK4)) & m1_subset_1(sK5,sK4))),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f48,plain,(
% 11.47/1.99    ((((((~m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4)) & k1_xboole_0 != sK4 & m1_subset_1(sK11,sK4)) & m1_subset_1(sK10,sK4)) & m1_subset_1(sK9,sK4)) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,sK4)) & m1_subset_1(sK6,sK4)) & m1_subset_1(sK5,sK4)),
% 11.47/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f22,f47,f46,f45,f44,f43,f42,f41])).
% 11.47/1.99  
% 11.47/1.99  fof(f91,plain,(
% 11.47/1.99    ~m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4))),
% 11.47/1.99    inference(cnf_transformation,[],[f48])).
% 11.47/1.99  
% 11.47/1.99  fof(f3,axiom,(
% 11.47/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f52,plain,(
% 11.47/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f3])).
% 11.47/1.99  
% 11.47/1.99  fof(f93,plain,(
% 11.47/1.99    ~m1_subset_1(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4))),
% 11.47/1.99    inference(definition_unfolding,[],[f91,f52])).
% 11.47/1.99  
% 11.47/1.99  fof(f83,plain,(
% 11.47/1.99    m1_subset_1(sK5,sK4)),
% 11.47/1.99    inference(cnf_transformation,[],[f48])).
% 11.47/1.99  
% 11.47/1.99  fof(f89,plain,(
% 11.47/1.99    m1_subset_1(sK11,sK4)),
% 11.47/1.99    inference(cnf_transformation,[],[f48])).
% 11.47/1.99  
% 11.47/1.99  fof(f90,plain,(
% 11.47/1.99    k1_xboole_0 != sK4),
% 11.47/1.99    inference(cnf_transformation,[],[f48])).
% 11.47/1.99  
% 11.47/1.99  fof(f63,plain,(
% 11.47/1.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f34])).
% 11.47/1.99  
% 11.47/1.99  fof(f23,plain,(
% 11.47/1.99    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 11.47/1.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.47/1.99  
% 11.47/1.99  fof(f35,plain,(
% 11.47/1.99    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 11.47/1.99    inference(nnf_transformation,[],[f23])).
% 11.47/1.99  
% 11.47/1.99  fof(f36,plain,(
% 11.47/1.99    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 11.47/1.99    inference(flattening,[],[f35])).
% 11.47/1.99  
% 11.47/1.99  fof(f37,plain,(
% 11.47/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 11.47/1.99    inference(rectify,[],[f36])).
% 11.47/1.99  
% 11.47/1.99  fof(f38,plain,(
% 11.47/1.99    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK3(X0,X1,X2,X3,X4,X5,X6) != X0 & sK3(X0,X1,X2,X3,X4,X5,X6) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK3(X0,X1,X2,X3,X4,X5,X6) = X0 | sK3(X0,X1,X2,X3,X4,X5,X6) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f39,plain,(
% 11.47/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK3(X0,X1,X2,X3,X4,X5,X6) != X0 & sK3(X0,X1,X2,X3,X4,X5,X6) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK3(X0,X1,X2,X3,X4,X5,X6) = X0 | sK3(X0,X1,X2,X3,X4,X5,X6) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 11.47/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 11.47/1.99  
% 11.47/1.99  fof(f65,plain,(
% 11.47/1.99    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f39])).
% 11.47/1.99  
% 11.47/1.99  fof(f101,plain,(
% 11.47/1.99    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X0,X1,X2,X3,X4,X8,X6)) )),
% 11.47/1.99    inference(equality_resolution,[],[f65])).
% 11.47/1.99  
% 11.47/1.99  fof(f8,axiom,(
% 11.47/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f17,plain,(
% 11.47/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 11.47/1.99    inference(ennf_transformation,[],[f8])).
% 11.47/1.99  
% 11.47/1.99  fof(f24,plain,(
% 11.47/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 11.47/1.99    inference(definition_folding,[],[f17,f23])).
% 11.47/1.99  
% 11.47/1.99  fof(f40,plain,(
% 11.47/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 11.47/1.99    inference(nnf_transformation,[],[f24])).
% 11.47/1.99  
% 11.47/1.99  fof(f78,plain,(
% 11.47/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 11.47/1.99    inference(cnf_transformation,[],[f40])).
% 11.47/1.99  
% 11.47/1.99  fof(f102,plain,(
% 11.47/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 11.47/1.99    inference(equality_resolution,[],[f78])).
% 11.47/1.99  
% 11.47/1.99  fof(f10,axiom,(
% 11.47/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f18,plain,(
% 11.47/1.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.47/1.99    inference(ennf_transformation,[],[f10])).
% 11.47/1.99  
% 11.47/1.99  fof(f81,plain,(
% 11.47/1.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.47/1.99    inference(cnf_transformation,[],[f18])).
% 11.47/1.99  
% 11.47/1.99  fof(f6,axiom,(
% 11.47/1.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f33,plain,(
% 11.47/1.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.47/1.99    inference(nnf_transformation,[],[f6])).
% 11.47/1.99  
% 11.47/1.99  fof(f59,plain,(
% 11.47/1.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f33])).
% 11.47/1.99  
% 11.47/1.99  fof(f88,plain,(
% 11.47/1.99    m1_subset_1(sK10,sK4)),
% 11.47/1.99    inference(cnf_transformation,[],[f48])).
% 11.47/1.99  
% 11.47/1.99  fof(f87,plain,(
% 11.47/1.99    m1_subset_1(sK9,sK4)),
% 11.47/1.99    inference(cnf_transformation,[],[f48])).
% 11.47/1.99  
% 11.47/1.99  fof(f86,plain,(
% 11.47/1.99    m1_subset_1(sK8,sK4)),
% 11.47/1.99    inference(cnf_transformation,[],[f48])).
% 11.47/1.99  
% 11.47/1.99  fof(f85,plain,(
% 11.47/1.99    m1_subset_1(sK7,sK4)),
% 11.47/1.99    inference(cnf_transformation,[],[f48])).
% 11.47/1.99  
% 11.47/1.99  fof(f84,plain,(
% 11.47/1.99    m1_subset_1(sK6,sK4)),
% 11.47/1.99    inference(cnf_transformation,[],[f48])).
% 11.47/1.99  
% 11.47/1.99  cnf(c_32,plain,
% 11.47/1.99      ( ~ m1_subset_1(X0,X1)
% 11.47/1.99      | ~ m1_subset_1(X2,X1)
% 11.47/1.99      | ~ m1_subset_1(X3,X1)
% 11.47/1.99      | ~ m1_subset_1(X4,X1)
% 11.47/1.99      | ~ m1_subset_1(X5,X1)
% 11.47/1.99      | ~ m1_subset_1(X6,X1)
% 11.47/1.99      | m1_subset_1(k4_enumset1(X0,X6,X5,X4,X3,X2),k1_zfmisc_1(X1))
% 11.47/1.99      | k1_xboole_0 = X1 ),
% 11.47/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2718,plain,
% 11.47/1.99      ( k1_xboole_0 = X0
% 11.47/1.99      | m1_subset_1(X1,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X2,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X3,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X4,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X5,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X6,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(k4_enumset1(X1,X6,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_13,plain,
% 11.47/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2737,plain,
% 11.47/1.99      ( m1_subset_1(X0,X1) != iProver_top
% 11.47/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.47/1.99      | v1_xboole_0(X1) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4664,plain,
% 11.47/1.99      ( k1_xboole_0 = X0
% 11.47/1.99      | m1_subset_1(X1,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X2,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X3,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X4,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X5,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X6,X0) != iProver_top
% 11.47/1.99      | r2_hidden(k4_enumset1(X1,X6,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
% 11.47/1.99      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_2718,c_2737]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_30,plain,
% 11.47/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.47/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_54,plain,
% 11.47/1.99      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_12206,plain,
% 11.47/1.99      ( r2_hidden(k4_enumset1(X1,X6,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
% 11.47/1.99      | m1_subset_1(X6,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X5,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X4,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X3,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X2,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X1,X0) != iProver_top
% 11.47/1.99      | k1_xboole_0 = X0 ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_4664,c_54]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_12207,plain,
% 11.47/1.99      ( k1_xboole_0 = X0
% 11.47/1.99      | m1_subset_1(X1,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X2,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X3,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X4,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X5,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X6,X0) != iProver_top
% 11.47/1.99      | r2_hidden(k4_enumset1(X1,X6,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 11.47/1.99      inference(renaming,[status(thm)],[c_12206]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_7,plain,
% 11.47/1.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.47/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2742,plain,
% 11.47/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.47/1.99      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_12215,plain,
% 11.47/1.99      ( k1_xboole_0 = X0
% 11.47/1.99      | m1_subset_1(X1,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X2,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X3,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X4,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X5,X0) != iProver_top
% 11.47/1.99      | m1_subset_1(X6,X0) != iProver_top
% 11.47/1.99      | r1_tarski(k4_enumset1(X1,X6,X5,X4,X3,X2),X0) = iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_12207,c_2742]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2,plain,
% 11.47/1.99      ( ~ r1_tarski(X0,X1)
% 11.47/1.99      | ~ r1_tarski(X2,X1)
% 11.47/1.99      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2746,plain,
% 11.47/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.47/1.99      | r1_tarski(X2,X1) != iProver_top
% 11.47/1.99      | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6,plain,
% 11.47/1.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.47/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2743,plain,
% 11.47/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.47/1.99      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_12,plain,
% 11.47/1.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1,plain,
% 11.47/1.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_232,plain,
% 11.47/1.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_12,c_1]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_233,plain,
% 11.47/1.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 11.47/1.99      inference(renaming,[status(thm)],[c_232]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2709,plain,
% 11.47/1.99      ( m1_subset_1(X0,X1) = iProver_top
% 11.47/1.99      | r2_hidden(X0,X1) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3605,plain,
% 11.47/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.47/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_2743,c_2709]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_33,negated_conjecture,
% 11.47/1.99      ( ~ m1_subset_1(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) ),
% 11.47/1.99      inference(cnf_transformation,[],[f93]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2717,plain,
% 11.47/1.99      ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_8571,plain,
% 11.47/1.99      ( r1_tarski(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),sK4) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_3605,c_2717]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_12697,plain,
% 11.47/1.99      ( r1_tarski(k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11),sK4) != iProver_top
% 11.47/1.99      | r1_tarski(k1_tarski(sK5),sK4) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_2746,c_8571]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_41,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK5,sK4) ),
% 11.47/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_42,plain,
% 11.47/1.99      ( m1_subset_1(sK5,sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3337,plain,
% 11.47/1.99      ( ~ m1_subset_1(sK5,sK4) | r2_hidden(sK5,sK4) | v1_xboole_0(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3338,plain,
% 11.47/1.99      ( m1_subset_1(sK5,sK4) != iProver_top
% 11.47/1.99      | r2_hidden(sK5,sK4) = iProver_top
% 11.47/1.99      | v1_xboole_0(sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_3337]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_35,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK11,sK4) ),
% 11.47/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3479,plain,
% 11.47/1.99      ( r2_hidden(sK11,sK4) | v1_xboole_0(sK4) ),
% 11.47/1.99      inference(resolution,[status(thm)],[c_13,c_35]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_34,negated_conjecture,
% 11.47/1.99      ( k1_xboole_0 != sK4 ),
% 11.47/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_51,plain,
% 11.47/1.99      ( m1_subset_1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
% 11.47/1.99      | ~ m1_subset_1(sK4,sK4)
% 11.47/1.99      | k1_xboole_0 = sK4 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_32]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_10,plain,
% 11.47/1.99      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 11.47/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_93,plain,
% 11.47/1.99      ( m1_subset_1(sK4,sK4) | ~ v1_xboole_0(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_118,plain,
% 11.47/1.99      ( ~ r2_hidden(sK4,sK4) | ~ v1_xboole_0(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_26,plain,
% 11.47/1.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X5,X6) ),
% 11.47/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_29,plain,
% 11.47/1.99      ( sP0(X0,X1,X2,X3,X4,X5,k4_enumset1(X5,X4,X3,X2,X1,X0)) ),
% 11.47/1.99      inference(cnf_transformation,[],[f102]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1480,plain,
% 11.47/1.99      ( r2_hidden(X0,X1)
% 11.47/1.99      | X2 != X3
% 11.47/1.99      | X4 != X0
% 11.47/1.99      | X5 != X6
% 11.47/1.99      | X7 != X8
% 11.47/1.99      | X9 != X10
% 11.47/1.99      | X11 != X12
% 11.47/1.99      | k4_enumset1(X4,X5,X7,X9,X11,X2) != X1 ),
% 11.47/1.99      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1481,plain,
% 11.47/1.99      ( r2_hidden(X0,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
% 11.47/1.99      inference(unflattening,[status(thm)],[c_1480]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1483,plain,
% 11.47/1.99      ( r2_hidden(sK4,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_1481]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_31,plain,
% 11.47/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.47/1.99      | ~ r2_hidden(X2,X0)
% 11.47/1.99      | r2_hidden(X2,X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3108,plain,
% 11.47/1.99      ( ~ m1_subset_1(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(X6))
% 11.47/1.99      | r2_hidden(X5,X6)
% 11.47/1.99      | ~ r2_hidden(X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_31]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3110,plain,
% 11.47/1.99      ( ~ m1_subset_1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
% 11.47/1.99      | ~ r2_hidden(sK4,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4))
% 11.47/1.99      | r2_hidden(sK4,sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_3108]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3319,plain,
% 11.47/1.99      ( ~ m1_subset_1(sK11,sK4)
% 11.47/1.99      | r2_hidden(sK11,sK4)
% 11.47/1.99      | v1_xboole_0(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3613,plain,
% 11.47/1.99      ( r2_hidden(sK11,sK4) ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_3479,c_35,c_34,c_51,c_93,c_118,c_1483,c_3110,c_3319]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3615,plain,
% 11.47/1.99      ( r2_hidden(sK11,sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_3613]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3870,plain,
% 11.47/1.99      ( ~ r2_hidden(sK11,sK4) | ~ v1_xboole_0(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3875,plain,
% 11.47/1.99      ( r2_hidden(sK11,sK4) != iProver_top
% 11.47/1.99      | v1_xboole_0(sK4) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_3870]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_8,plain,
% 11.47/1.99      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4021,plain,
% 11.47/1.99      ( r1_tarski(k1_tarski(sK5),sK4) | ~ r2_hidden(sK5,sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4022,plain,
% 11.47/1.99      ( r1_tarski(k1_tarski(sK5),sK4) = iProver_top
% 11.47/1.99      | r2_hidden(sK5,sK4) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_4021]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3203,plain,
% 11.47/1.99      ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) ),
% 11.47/1.99      inference(resolution,[status(thm)],[c_33,c_233]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3209,plain,
% 11.47/1.99      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK5),k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11)),sK4) ),
% 11.47/1.99      inference(resolution,[status(thm)],[c_3203,c_6]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6554,plain,
% 11.47/1.99      ( ~ r1_tarski(k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11),sK4)
% 11.47/1.99      | ~ r1_tarski(k1_tarski(sK5),sK4) ),
% 11.47/1.99      inference(resolution,[status(thm)],[c_3209,c_2]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6555,plain,
% 11.47/1.99      ( r1_tarski(k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11),sK4) != iProver_top
% 11.47/1.99      | r1_tarski(k1_tarski(sK5),sK4) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_6554]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_16665,plain,
% 11.47/1.99      ( r1_tarski(k4_enumset1(sK6,sK7,sK8,sK9,sK10,sK11),sK4) != iProver_top ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_12697,c_42,c_3338,c_3615,c_3875,c_4022,c_6555]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_35610,plain,
% 11.47/1.99      ( sK4 = k1_xboole_0
% 11.47/1.99      | m1_subset_1(sK11,sK4) != iProver_top
% 11.47/1.99      | m1_subset_1(sK10,sK4) != iProver_top
% 11.47/1.99      | m1_subset_1(sK9,sK4) != iProver_top
% 11.47/1.99      | m1_subset_1(sK8,sK4) != iProver_top
% 11.47/1.99      | m1_subset_1(sK7,sK4) != iProver_top
% 11.47/1.99      | m1_subset_1(sK6,sK4) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_12215,c_16665]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1774,plain,( X0 = X0 ),theory(equality) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3016,plain,
% 11.47/1.99      ( k1_xboole_0 = k1_xboole_0 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_1774]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1775,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2888,plain,
% 11.47/1.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_1775]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3015,plain,
% 11.47/1.99      ( sK4 != k1_xboole_0
% 11.47/1.99      | k1_xboole_0 = sK4
% 11.47/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_2888]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_48,plain,
% 11.47/1.99      ( m1_subset_1(sK11,sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_36,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK10,sK4) ),
% 11.47/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_47,plain,
% 11.47/1.99      ( m1_subset_1(sK10,sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_37,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK9,sK4) ),
% 11.47/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_46,plain,
% 11.47/1.99      ( m1_subset_1(sK9,sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_38,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK8,sK4) ),
% 11.47/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_45,plain,
% 11.47/1.99      ( m1_subset_1(sK8,sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_39,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK7,sK4) ),
% 11.47/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_44,plain,
% 11.47/1.99      ( m1_subset_1(sK7,sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_40,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK6,sK4) ),
% 11.47/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_43,plain,
% 11.47/1.99      ( m1_subset_1(sK6,sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(contradiction,plain,
% 11.47/1.99      ( $false ),
% 11.47/1.99      inference(minisat,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_35610,c_3016,c_3015,c_34,c_48,c_47,c_46,c_45,c_44,
% 11.47/1.99                 c_43]) ).
% 11.47/1.99  
% 11.47/1.99  
% 11.47/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.47/1.99  
% 11.47/1.99  ------                               Statistics
% 11.47/1.99  
% 11.47/1.99  ------ Selected
% 11.47/1.99  
% 11.47/1.99  total_time:                             1.107
% 11.47/1.99  
%------------------------------------------------------------------------------
