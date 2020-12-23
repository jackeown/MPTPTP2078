%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:11 EST 2020

% Result     : Theorem 23.44s
% Output     : CNFRefutation 23.44s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 395 expanded)
%              Number of clauses        :   78 ( 111 expanded)
%              Number of leaves         :   23 ( 126 expanded)
%              Depth                    :   14
%              Number of atoms          :  633 (2441 expanded)
%              Number of equality atoms :  287 ( 686 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   2 average)
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
                     => ( k1_xboole_0 != X0
                       => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      | k1_xboole_0 = X0
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
                      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      | k1_xboole_0 = X0
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f19])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
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

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
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

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f60,plain,(
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

fof(f48,plain,(
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
                         => ( k1_xboole_0 != X0
                           => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
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
                           => ( k1_xboole_0 != X0
                             => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f22,f46,f45,f44,f43,f42,f41])).

fof(f87,plain,(
    ~ m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f3])).

fof(f89,plain,(
    ~ m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
    inference(definition_unfolding,[],[f87,f51])).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f23,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X0
            & sK3(X0,X1,X2,X3,X4,X5) != X1
            & sK3(X0,X1,X2,X3,X4,X5) != X2
            & sK3(X0,X1,X2,X3,X4,X5) != X3
            & sK3(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK3(X0,X1,X2,X3,X4,X5) = X0
          | sK3(X0,X1,X2,X3,X4,X5) = X1
          | sK3(X0,X1,X2,X3,X4,X5) = X2
          | sK3(X0,X1,X2,X3,X4,X5) = X3
          | sK3(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X0
              & sK3(X0,X1,X2,X3,X4,X5) != X1
              & sK3(X0,X1,X2,X3,X4,X5) != X2
              & sK3(X0,X1,X2,X3,X4,X5) != X3
              & sK3(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK3(X0,X1,X2,X3,X4,X5) = X0
            | sK3(X0,X1,X2,X3,X4,X5) = X1
            | sK3(X0,X1,X2,X3,X4,X5) = X2
            | sK3(X0,X1,X2,X3,X4,X5) = X3
            | sK3(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f64,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X7,X5) ) ),
    inference(equality_resolution,[],[f64])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f17,f23])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f75])).

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

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X5,X1)
    | m1_subset_1(k3_enumset1(X0,X5,X4,X3,X2),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2229,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2246,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4468,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_2246])).

cnf(c_28,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_50,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8648,plain,
    ( r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4468,c_50])).

cnf(c_8649,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8648])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2251,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8656,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | r1_tarski(k3_enumset1(X1,X5,X4,X3,X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8649,c_2251])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2255,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2252,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_1])).

cnf(c_218,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_2221,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_3820,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_2221])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2228,plain,
    ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3826,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_2228])).

cnf(c_5170,plain,
    ( r1_tarski(k3_enumset1(sK6,sK7,sK8,sK9,sK10),sK4) != iProver_top
    | r1_tarski(k1_tarski(sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2255,c_3826])).

cnf(c_45,plain,
    ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2303,plain,
    ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4))
    | ~ r2_hidden(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_2304,plain,
    ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) = iProver_top
    | r2_hidden(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2303])).

cnf(c_2341,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4)
    | r2_hidden(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2342,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4) != iProver_top
    | r2_hidden(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2341])).

cnf(c_2480,plain,
    ( ~ r1_tarski(k3_enumset1(sK6,sK7,sK8,sK9,sK10),sK4)
    | r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4)
    | ~ r1_tarski(k1_tarski(sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2481,plain,
    ( r1_tarski(k3_enumset1(sK6,sK7,sK8,sK9,sK10),sK4) != iProver_top
    | r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4) = iProver_top
    | r1_tarski(k1_tarski(sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2480])).

cnf(c_8,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3149,plain,
    ( r1_tarski(k1_tarski(sK5),sK4)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3150,plain,
    ( r1_tarski(k1_tarski(sK5),sK4) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3149])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2222,plain,
    ( m1_subset_1(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4467,plain,
    ( r2_hidden(sK5,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2222,c_2246])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2227,plain,
    ( m1_subset_1(sK10,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2247,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4483,plain,
    ( v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_2247])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_86,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_88,plain,
    ( m1_subset_1(sK4,sK4) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_111,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_113,plain,
    ( r2_hidden(sK4,sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X4,X5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_27,plain,
    ( sP0(X0,X1,X2,X3,X4,k3_enumset1(X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1203,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | k3_enumset1(X4,X5,X7,X9,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_1204,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(unflattening,[status(thm)],[c_1203])).

cnf(c_1205,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_1207,plain,
    ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4417,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | r2_hidden(X6,X0) = iProver_top
    | r2_hidden(X6,k3_enumset1(X1,X5,X4,X3,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_2230])).

cnf(c_4420,plain,
    ( k1_xboole_0 = sK4
    | m1_subset_1(sK4,sK4) != iProver_top
    | r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK4,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4417])).

cnf(c_4577,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4483,c_32,c_88,c_113,c_1207,c_4420])).

cnf(c_5503,plain,
    ( r1_tarski(k3_enumset1(sK6,sK7,sK8,sK9,sK10),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5170,c_32,c_45,c_88,c_113,c_1207,c_2304,c_2342,c_2481,c_3150,c_4420,c_4467])).

cnf(c_71831,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK10,sK4) != iProver_top
    | m1_subset_1(sK9,sK4) != iProver_top
    | m1_subset_1(sK8,sK4) != iProver_top
    | m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8656,c_5503])).

cnf(c_1424,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3209,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_1425,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2318,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1425])).

cnf(c_2395,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2318])).

cnf(c_44,plain,
    ( m1_subset_1(sK10,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_43,plain,
    ( m1_subset_1(sK9,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_42,plain,
    ( m1_subset_1(sK8,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_41,plain,
    ( m1_subset_1(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71831,c_3209,c_2395,c_32,c_44,c_43,c_42,c_41,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 23.44/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.44/3.49  
% 23.44/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.44/3.49  
% 23.44/3.49  ------  iProver source info
% 23.44/3.49  
% 23.44/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.44/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.44/3.49  git: non_committed_changes: false
% 23.44/3.49  git: last_make_outside_of_git: false
% 23.44/3.49  
% 23.44/3.49  ------ 
% 23.44/3.49  
% 23.44/3.49  ------ Input Options
% 23.44/3.49  
% 23.44/3.49  --out_options                           all
% 23.44/3.49  --tptp_safe_out                         true
% 23.44/3.49  --problem_path                          ""
% 23.44/3.49  --include_path                          ""
% 23.44/3.49  --clausifier                            res/vclausify_rel
% 23.44/3.49  --clausifier_options                    ""
% 23.44/3.49  --stdin                                 false
% 23.44/3.49  --stats_out                             all
% 23.44/3.49  
% 23.44/3.49  ------ General Options
% 23.44/3.49  
% 23.44/3.49  --fof                                   false
% 23.44/3.49  --time_out_real                         305.
% 23.44/3.49  --time_out_virtual                      -1.
% 23.44/3.49  --symbol_type_check                     false
% 23.44/3.49  --clausify_out                          false
% 23.44/3.49  --sig_cnt_out                           false
% 23.44/3.49  --trig_cnt_out                          false
% 23.44/3.49  --trig_cnt_out_tolerance                1.
% 23.44/3.49  --trig_cnt_out_sk_spl                   false
% 23.44/3.49  --abstr_cl_out                          false
% 23.44/3.49  
% 23.44/3.49  ------ Global Options
% 23.44/3.49  
% 23.44/3.49  --schedule                              default
% 23.44/3.49  --add_important_lit                     false
% 23.44/3.49  --prop_solver_per_cl                    1000
% 23.44/3.49  --min_unsat_core                        false
% 23.44/3.49  --soft_assumptions                      false
% 23.44/3.49  --soft_lemma_size                       3
% 23.44/3.49  --prop_impl_unit_size                   0
% 23.44/3.49  --prop_impl_unit                        []
% 23.44/3.49  --share_sel_clauses                     true
% 23.44/3.49  --reset_solvers                         false
% 23.44/3.49  --bc_imp_inh                            [conj_cone]
% 23.44/3.49  --conj_cone_tolerance                   3.
% 23.44/3.49  --extra_neg_conj                        none
% 23.44/3.49  --large_theory_mode                     true
% 23.44/3.49  --prolific_symb_bound                   200
% 23.44/3.49  --lt_threshold                          2000
% 23.44/3.49  --clause_weak_htbl                      true
% 23.44/3.49  --gc_record_bc_elim                     false
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing Options
% 23.44/3.49  
% 23.44/3.49  --preprocessing_flag                    true
% 23.44/3.49  --time_out_prep_mult                    0.1
% 23.44/3.49  --splitting_mode                        input
% 23.44/3.49  --splitting_grd                         true
% 23.44/3.49  --splitting_cvd                         false
% 23.44/3.49  --splitting_cvd_svl                     false
% 23.44/3.49  --splitting_nvd                         32
% 23.44/3.49  --sub_typing                            true
% 23.44/3.49  --prep_gs_sim                           true
% 23.44/3.49  --prep_unflatten                        true
% 23.44/3.49  --prep_res_sim                          true
% 23.44/3.49  --prep_upred                            true
% 23.44/3.49  --prep_sem_filter                       exhaustive
% 23.44/3.49  --prep_sem_filter_out                   false
% 23.44/3.49  --pred_elim                             true
% 23.44/3.49  --res_sim_input                         true
% 23.44/3.49  --eq_ax_congr_red                       true
% 23.44/3.49  --pure_diseq_elim                       true
% 23.44/3.49  --brand_transform                       false
% 23.44/3.49  --non_eq_to_eq                          false
% 23.44/3.49  --prep_def_merge                        true
% 23.44/3.49  --prep_def_merge_prop_impl              false
% 23.44/3.49  --prep_def_merge_mbd                    true
% 23.44/3.49  --prep_def_merge_tr_red                 false
% 23.44/3.49  --prep_def_merge_tr_cl                  false
% 23.44/3.49  --smt_preprocessing                     true
% 23.44/3.49  --smt_ac_axioms                         fast
% 23.44/3.49  --preprocessed_out                      false
% 23.44/3.49  --preprocessed_stats                    false
% 23.44/3.49  
% 23.44/3.49  ------ Abstraction refinement Options
% 23.44/3.49  
% 23.44/3.49  --abstr_ref                             []
% 23.44/3.49  --abstr_ref_prep                        false
% 23.44/3.49  --abstr_ref_until_sat                   false
% 23.44/3.49  --abstr_ref_sig_restrict                funpre
% 23.44/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.44/3.49  --abstr_ref_under                       []
% 23.44/3.49  
% 23.44/3.49  ------ SAT Options
% 23.44/3.49  
% 23.44/3.49  --sat_mode                              false
% 23.44/3.49  --sat_fm_restart_options                ""
% 23.44/3.49  --sat_gr_def                            false
% 23.44/3.49  --sat_epr_types                         true
% 23.44/3.49  --sat_non_cyclic_types                  false
% 23.44/3.49  --sat_finite_models                     false
% 23.44/3.49  --sat_fm_lemmas                         false
% 23.44/3.49  --sat_fm_prep                           false
% 23.44/3.49  --sat_fm_uc_incr                        true
% 23.44/3.49  --sat_out_model                         small
% 23.44/3.49  --sat_out_clauses                       false
% 23.44/3.49  
% 23.44/3.49  ------ QBF Options
% 23.44/3.49  
% 23.44/3.49  --qbf_mode                              false
% 23.44/3.49  --qbf_elim_univ                         false
% 23.44/3.49  --qbf_dom_inst                          none
% 23.44/3.49  --qbf_dom_pre_inst                      false
% 23.44/3.49  --qbf_sk_in                             false
% 23.44/3.49  --qbf_pred_elim                         true
% 23.44/3.49  --qbf_split                             512
% 23.44/3.49  
% 23.44/3.49  ------ BMC1 Options
% 23.44/3.49  
% 23.44/3.49  --bmc1_incremental                      false
% 23.44/3.49  --bmc1_axioms                           reachable_all
% 23.44/3.49  --bmc1_min_bound                        0
% 23.44/3.49  --bmc1_max_bound                        -1
% 23.44/3.49  --bmc1_max_bound_default                -1
% 23.44/3.49  --bmc1_symbol_reachability              true
% 23.44/3.49  --bmc1_property_lemmas                  false
% 23.44/3.49  --bmc1_k_induction                      false
% 23.44/3.49  --bmc1_non_equiv_states                 false
% 23.44/3.49  --bmc1_deadlock                         false
% 23.44/3.49  --bmc1_ucm                              false
% 23.44/3.49  --bmc1_add_unsat_core                   none
% 23.44/3.49  --bmc1_unsat_core_children              false
% 23.44/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.44/3.49  --bmc1_out_stat                         full
% 23.44/3.49  --bmc1_ground_init                      false
% 23.44/3.49  --bmc1_pre_inst_next_state              false
% 23.44/3.49  --bmc1_pre_inst_state                   false
% 23.44/3.49  --bmc1_pre_inst_reach_state             false
% 23.44/3.49  --bmc1_out_unsat_core                   false
% 23.44/3.49  --bmc1_aig_witness_out                  false
% 23.44/3.49  --bmc1_verbose                          false
% 23.44/3.49  --bmc1_dump_clauses_tptp                false
% 23.44/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.44/3.49  --bmc1_dump_file                        -
% 23.44/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.44/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.44/3.49  --bmc1_ucm_extend_mode                  1
% 23.44/3.49  --bmc1_ucm_init_mode                    2
% 23.44/3.49  --bmc1_ucm_cone_mode                    none
% 23.44/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.44/3.49  --bmc1_ucm_relax_model                  4
% 23.44/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.44/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.44/3.49  --bmc1_ucm_layered_model                none
% 23.44/3.49  --bmc1_ucm_max_lemma_size               10
% 23.44/3.49  
% 23.44/3.49  ------ AIG Options
% 23.44/3.49  
% 23.44/3.49  --aig_mode                              false
% 23.44/3.49  
% 23.44/3.49  ------ Instantiation Options
% 23.44/3.49  
% 23.44/3.49  --instantiation_flag                    true
% 23.44/3.49  --inst_sos_flag                         true
% 23.44/3.49  --inst_sos_phase                        true
% 23.44/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.44/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.44/3.49  --inst_lit_sel_side                     num_symb
% 23.44/3.49  --inst_solver_per_active                1400
% 23.44/3.49  --inst_solver_calls_frac                1.
% 23.44/3.49  --inst_passive_queue_type               priority_queues
% 23.44/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.44/3.49  --inst_passive_queues_freq              [25;2]
% 23.44/3.49  --inst_dismatching                      true
% 23.44/3.49  --inst_eager_unprocessed_to_passive     true
% 23.44/3.49  --inst_prop_sim_given                   true
% 23.44/3.49  --inst_prop_sim_new                     false
% 23.44/3.49  --inst_subs_new                         false
% 23.44/3.49  --inst_eq_res_simp                      false
% 23.44/3.49  --inst_subs_given                       false
% 23.44/3.49  --inst_orphan_elimination               true
% 23.44/3.49  --inst_learning_loop_flag               true
% 23.44/3.49  --inst_learning_start                   3000
% 23.44/3.49  --inst_learning_factor                  2
% 23.44/3.49  --inst_start_prop_sim_after_learn       3
% 23.44/3.49  --inst_sel_renew                        solver
% 23.44/3.49  --inst_lit_activity_flag                true
% 23.44/3.49  --inst_restr_to_given                   false
% 23.44/3.49  --inst_activity_threshold               500
% 23.44/3.49  --inst_out_proof                        true
% 23.44/3.49  
% 23.44/3.49  ------ Resolution Options
% 23.44/3.49  
% 23.44/3.49  --resolution_flag                       true
% 23.44/3.49  --res_lit_sel                           adaptive
% 23.44/3.49  --res_lit_sel_side                      none
% 23.44/3.49  --res_ordering                          kbo
% 23.44/3.49  --res_to_prop_solver                    active
% 23.44/3.49  --res_prop_simpl_new                    false
% 23.44/3.49  --res_prop_simpl_given                  true
% 23.44/3.49  --res_passive_queue_type                priority_queues
% 23.44/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.44/3.49  --res_passive_queues_freq               [15;5]
% 23.44/3.49  --res_forward_subs                      full
% 23.44/3.49  --res_backward_subs                     full
% 23.44/3.49  --res_forward_subs_resolution           true
% 23.44/3.49  --res_backward_subs_resolution          true
% 23.44/3.49  --res_orphan_elimination                true
% 23.44/3.49  --res_time_limit                        2.
% 23.44/3.49  --res_out_proof                         true
% 23.44/3.49  
% 23.44/3.49  ------ Superposition Options
% 23.44/3.49  
% 23.44/3.49  --superposition_flag                    true
% 23.44/3.49  --sup_passive_queue_type                priority_queues
% 23.44/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.44/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.44/3.49  --demod_completeness_check              fast
% 23.44/3.49  --demod_use_ground                      true
% 23.44/3.49  --sup_to_prop_solver                    passive
% 23.44/3.49  --sup_prop_simpl_new                    true
% 23.44/3.49  --sup_prop_simpl_given                  true
% 23.44/3.49  --sup_fun_splitting                     true
% 23.44/3.49  --sup_smt_interval                      50000
% 23.44/3.49  
% 23.44/3.49  ------ Superposition Simplification Setup
% 23.44/3.49  
% 23.44/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.44/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.44/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.44/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.44/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.44/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.44/3.49  --sup_immed_triv                        [TrivRules]
% 23.44/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.49  --sup_immed_bw_main                     []
% 23.44/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.44/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.44/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.49  --sup_input_bw                          []
% 23.44/3.49  
% 23.44/3.49  ------ Combination Options
% 23.44/3.49  
% 23.44/3.49  --comb_res_mult                         3
% 23.44/3.49  --comb_sup_mult                         2
% 23.44/3.49  --comb_inst_mult                        10
% 23.44/3.49  
% 23.44/3.49  ------ Debug Options
% 23.44/3.49  
% 23.44/3.49  --dbg_backtrace                         false
% 23.44/3.49  --dbg_dump_prop_clauses                 false
% 23.44/3.49  --dbg_dump_prop_clauses_file            -
% 23.44/3.49  --dbg_out_stat                          false
% 23.44/3.49  ------ Parsing...
% 23.44/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.44/3.49  ------ Proving...
% 23.44/3.49  ------ Problem Properties 
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  clauses                                 39
% 23.44/3.49  conjectures                             8
% 23.44/3.49  EPR                                     18
% 23.44/3.49  Horn                                    33
% 23.44/3.49  unary                                   11
% 23.44/3.49  binary                                  13
% 23.44/3.49  lits                                    94
% 23.44/3.49  lits eq                                 21
% 23.44/3.49  fd_pure                                 0
% 23.44/3.49  fd_pseudo                               0
% 23.44/3.49  fd_cond                                 1
% 23.44/3.49  fd_pseudo_cond                          4
% 23.44/3.49  AC symbols                              0
% 23.44/3.49  
% 23.44/3.49  ------ Schedule dynamic 5 is on 
% 23.44/3.49  
% 23.44/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.44/3.49  
% 23.44/3.49  
% 23.44/3.49  ------ 
% 23.44/3.49  Current options:
% 23.44/3.49  ------ 
% 23.44/3.49  
% 23.44/3.49  ------ Input Options
% 23.44/3.49  
% 23.44/3.49  --out_options                           all
% 23.44/3.49  --tptp_safe_out                         true
% 23.44/3.49  --problem_path                          ""
% 23.44/3.49  --include_path                          ""
% 23.44/3.49  --clausifier                            res/vclausify_rel
% 23.44/3.49  --clausifier_options                    ""
% 23.44/3.49  --stdin                                 false
% 23.44/3.49  --stats_out                             all
% 23.44/3.49  
% 23.44/3.49  ------ General Options
% 23.44/3.49  
% 23.44/3.49  --fof                                   false
% 23.44/3.49  --time_out_real                         305.
% 23.44/3.49  --time_out_virtual                      -1.
% 23.44/3.49  --symbol_type_check                     false
% 23.44/3.49  --clausify_out                          false
% 23.44/3.49  --sig_cnt_out                           false
% 23.44/3.49  --trig_cnt_out                          false
% 23.44/3.49  --trig_cnt_out_tolerance                1.
% 23.44/3.49  --trig_cnt_out_sk_spl                   false
% 23.44/3.49  --abstr_cl_out                          false
% 23.44/3.49  
% 23.44/3.49  ------ Global Options
% 23.44/3.49  
% 23.44/3.49  --schedule                              default
% 23.44/3.49  --add_important_lit                     false
% 23.44/3.49  --prop_solver_per_cl                    1000
% 23.44/3.49  --min_unsat_core                        false
% 23.44/3.49  --soft_assumptions                      false
% 23.44/3.49  --soft_lemma_size                       3
% 23.44/3.49  --prop_impl_unit_size                   0
% 23.44/3.49  --prop_impl_unit                        []
% 23.44/3.49  --share_sel_clauses                     true
% 23.44/3.49  --reset_solvers                         false
% 23.44/3.49  --bc_imp_inh                            [conj_cone]
% 23.44/3.49  --conj_cone_tolerance                   3.
% 23.44/3.49  --extra_neg_conj                        none
% 23.44/3.49  --large_theory_mode                     true
% 23.44/3.49  --prolific_symb_bound                   200
% 23.44/3.49  --lt_threshold                          2000
% 23.44/3.49  --clause_weak_htbl                      true
% 23.44/3.49  --gc_record_bc_elim                     false
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing Options
% 23.44/3.49  
% 23.44/3.49  --preprocessing_flag                    true
% 23.44/3.49  --time_out_prep_mult                    0.1
% 23.44/3.49  --splitting_mode                        input
% 23.44/3.49  --splitting_grd                         true
% 23.44/3.49  --splitting_cvd                         false
% 23.44/3.49  --splitting_cvd_svl                     false
% 23.44/3.49  --splitting_nvd                         32
% 23.44/3.49  --sub_typing                            true
% 23.44/3.49  --prep_gs_sim                           true
% 23.44/3.49  --prep_unflatten                        true
% 23.44/3.49  --prep_res_sim                          true
% 23.44/3.49  --prep_upred                            true
% 23.44/3.49  --prep_sem_filter                       exhaustive
% 23.44/3.49  --prep_sem_filter_out                   false
% 23.44/3.49  --pred_elim                             true
% 23.44/3.49  --res_sim_input                         true
% 23.44/3.49  --eq_ax_congr_red                       true
% 23.44/3.49  --pure_diseq_elim                       true
% 23.44/3.49  --brand_transform                       false
% 23.44/3.49  --non_eq_to_eq                          false
% 23.44/3.49  --prep_def_merge                        true
% 23.44/3.49  --prep_def_merge_prop_impl              false
% 23.44/3.49  --prep_def_merge_mbd                    true
% 23.44/3.49  --prep_def_merge_tr_red                 false
% 23.44/3.49  --prep_def_merge_tr_cl                  false
% 23.44/3.49  --smt_preprocessing                     true
% 23.44/3.49  --smt_ac_axioms                         fast
% 23.44/3.49  --preprocessed_out                      false
% 23.44/3.49  --preprocessed_stats                    false
% 23.44/3.49  
% 23.44/3.49  ------ Abstraction refinement Options
% 23.44/3.49  
% 23.44/3.49  --abstr_ref                             []
% 23.44/3.49  --abstr_ref_prep                        false
% 23.44/3.49  --abstr_ref_until_sat                   false
% 23.44/3.49  --abstr_ref_sig_restrict                funpre
% 23.44/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.44/3.49  --abstr_ref_under                       []
% 23.44/3.49  
% 23.44/3.49  ------ SAT Options
% 23.44/3.49  
% 23.44/3.49  --sat_mode                              false
% 23.44/3.49  --sat_fm_restart_options                ""
% 23.44/3.49  --sat_gr_def                            false
% 23.44/3.49  --sat_epr_types                         true
% 23.44/3.49  --sat_non_cyclic_types                  false
% 23.44/3.49  --sat_finite_models                     false
% 23.44/3.49  --sat_fm_lemmas                         false
% 23.44/3.49  --sat_fm_prep                           false
% 23.44/3.49  --sat_fm_uc_incr                        true
% 23.44/3.49  --sat_out_model                         small
% 23.44/3.49  --sat_out_clauses                       false
% 23.44/3.49  
% 23.44/3.49  ------ QBF Options
% 23.44/3.49  
% 23.44/3.49  --qbf_mode                              false
% 23.44/3.49  --qbf_elim_univ                         false
% 23.44/3.49  --qbf_dom_inst                          none
% 23.44/3.49  --qbf_dom_pre_inst                      false
% 23.44/3.49  --qbf_sk_in                             false
% 23.44/3.49  --qbf_pred_elim                         true
% 23.44/3.49  --qbf_split                             512
% 23.44/3.49  
% 23.44/3.49  ------ BMC1 Options
% 23.44/3.49  
% 23.44/3.49  --bmc1_incremental                      false
% 23.44/3.49  --bmc1_axioms                           reachable_all
% 23.44/3.49  --bmc1_min_bound                        0
% 23.44/3.49  --bmc1_max_bound                        -1
% 23.44/3.49  --bmc1_max_bound_default                -1
% 23.44/3.49  --bmc1_symbol_reachability              true
% 23.44/3.49  --bmc1_property_lemmas                  false
% 23.44/3.49  --bmc1_k_induction                      false
% 23.44/3.49  --bmc1_non_equiv_states                 false
% 23.44/3.49  --bmc1_deadlock                         false
% 23.44/3.49  --bmc1_ucm                              false
% 23.44/3.49  --bmc1_add_unsat_core                   none
% 23.44/3.49  --bmc1_unsat_core_children              false
% 23.44/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.44/3.49  --bmc1_out_stat                         full
% 23.44/3.49  --bmc1_ground_init                      false
% 23.44/3.49  --bmc1_pre_inst_next_state              false
% 23.44/3.49  --bmc1_pre_inst_state                   false
% 23.44/3.49  --bmc1_pre_inst_reach_state             false
% 23.44/3.49  --bmc1_out_unsat_core                   false
% 23.44/3.49  --bmc1_aig_witness_out                  false
% 23.44/3.49  --bmc1_verbose                          false
% 23.44/3.49  --bmc1_dump_clauses_tptp                false
% 23.44/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.44/3.49  --bmc1_dump_file                        -
% 23.44/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.44/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.44/3.49  --bmc1_ucm_extend_mode                  1
% 23.44/3.49  --bmc1_ucm_init_mode                    2
% 23.44/3.49  --bmc1_ucm_cone_mode                    none
% 23.44/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.44/3.49  --bmc1_ucm_relax_model                  4
% 23.44/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.44/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.44/3.49  --bmc1_ucm_layered_model                none
% 23.44/3.49  --bmc1_ucm_max_lemma_size               10
% 23.44/3.49  
% 23.44/3.49  ------ AIG Options
% 23.44/3.49  
% 23.44/3.49  --aig_mode                              false
% 23.44/3.49  
% 23.44/3.49  ------ Instantiation Options
% 23.44/3.49  
% 23.44/3.49  --instantiation_flag                    true
% 23.44/3.49  --inst_sos_flag                         true
% 23.44/3.49  --inst_sos_phase                        true
% 23.44/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.44/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.44/3.49  --inst_lit_sel_side                     none
% 23.44/3.49  --inst_solver_per_active                1400
% 23.44/3.49  --inst_solver_calls_frac                1.
% 23.44/3.49  --inst_passive_queue_type               priority_queues
% 23.44/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.44/3.49  --inst_passive_queues_freq              [25;2]
% 23.44/3.49  --inst_dismatching                      true
% 23.44/3.49  --inst_eager_unprocessed_to_passive     true
% 23.44/3.49  --inst_prop_sim_given                   true
% 23.44/3.49  --inst_prop_sim_new                     false
% 23.44/3.49  --inst_subs_new                         false
% 23.44/3.49  --inst_eq_res_simp                      false
% 23.44/3.49  --inst_subs_given                       false
% 23.44/3.49  --inst_orphan_elimination               true
% 23.44/3.49  --inst_learning_loop_flag               true
% 23.44/3.49  --inst_learning_start                   3000
% 23.44/3.49  --inst_learning_factor                  2
% 23.44/3.49  --inst_start_prop_sim_after_learn       3
% 23.44/3.49  --inst_sel_renew                        solver
% 23.44/3.49  --inst_lit_activity_flag                true
% 23.44/3.49  --inst_restr_to_given                   false
% 23.44/3.49  --inst_activity_threshold               500
% 23.44/3.49  --inst_out_proof                        true
% 23.44/3.49  
% 23.44/3.49  ------ Resolution Options
% 23.44/3.49  
% 23.44/3.49  --resolution_flag                       false
% 23.44/3.49  --res_lit_sel                           adaptive
% 23.44/3.49  --res_lit_sel_side                      none
% 23.44/3.49  --res_ordering                          kbo
% 23.44/3.49  --res_to_prop_solver                    active
% 23.44/3.49  --res_prop_simpl_new                    false
% 23.44/3.49  --res_prop_simpl_given                  true
% 23.44/3.49  --res_passive_queue_type                priority_queues
% 23.44/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.44/3.49  --res_passive_queues_freq               [15;5]
% 23.44/3.49  --res_forward_subs                      full
% 23.44/3.49  --res_backward_subs                     full
% 23.44/3.49  --res_forward_subs_resolution           true
% 23.44/3.49  --res_backward_subs_resolution          true
% 23.44/3.49  --res_orphan_elimination                true
% 23.44/3.49  --res_time_limit                        2.
% 23.44/3.49  --res_out_proof                         true
% 23.44/3.49  
% 23.44/3.49  ------ Superposition Options
% 23.44/3.49  
% 23.44/3.49  --superposition_flag                    true
% 23.44/3.49  --sup_passive_queue_type                priority_queues
% 23.44/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.44/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.44/3.49  --demod_completeness_check              fast
% 23.44/3.49  --demod_use_ground                      true
% 23.44/3.49  --sup_to_prop_solver                    passive
% 23.44/3.49  --sup_prop_simpl_new                    true
% 23.44/3.49  --sup_prop_simpl_given                  true
% 23.44/3.50  --sup_fun_splitting                     true
% 23.44/3.50  --sup_smt_interval                      50000
% 23.44/3.50  
% 23.44/3.50  ------ Superposition Simplification Setup
% 23.44/3.50  
% 23.44/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.44/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.44/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.44/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.44/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.44/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.44/3.50  --sup_immed_triv                        [TrivRules]
% 23.44/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.50  --sup_immed_bw_main                     []
% 23.44/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.44/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.44/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.50  --sup_input_bw                          []
% 23.44/3.50  
% 23.44/3.50  ------ Combination Options
% 23.44/3.50  
% 23.44/3.50  --comb_res_mult                         3
% 23.44/3.50  --comb_sup_mult                         2
% 23.44/3.50  --comb_inst_mult                        10
% 23.44/3.50  
% 23.44/3.50  ------ Debug Options
% 23.44/3.50  
% 23.44/3.50  --dbg_backtrace                         false
% 23.44/3.50  --dbg_dump_prop_clauses                 false
% 23.44/3.50  --dbg_dump_prop_clauses_file            -
% 23.44/3.50  --dbg_out_stat                          false
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  ------ Proving...
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  % SZS status Theorem for theBenchmark.p
% 23.44/3.50  
% 23.44/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.44/3.50  
% 23.44/3.50  fof(f11,axiom,(
% 23.44/3.50    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => (k1_xboole_0 != X0 => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))))))))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f19,plain,(
% 23.44/3.50    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 23.44/3.50    inference(ennf_transformation,[],[f11])).
% 23.44/3.50  
% 23.44/3.50  fof(f20,plain,(
% 23.44/3.50    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 23.44/3.50    inference(flattening,[],[f19])).
% 23.44/3.50  
% 23.44/3.50  fof(f79,plain,(
% 23.44/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f20])).
% 23.44/3.50  
% 23.44/3.50  fof(f7,axiom,(
% 23.44/3.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f16,plain,(
% 23.44/3.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 23.44/3.50    inference(ennf_transformation,[],[f7])).
% 23.44/3.50  
% 23.44/3.50  fof(f34,plain,(
% 23.44/3.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 23.44/3.50    inference(nnf_transformation,[],[f16])).
% 23.44/3.50  
% 23.44/3.50  fof(f59,plain,(
% 23.44/3.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f34])).
% 23.44/3.50  
% 23.44/3.50  fof(f9,axiom,(
% 23.44/3.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f77,plain,(
% 23.44/3.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 23.44/3.50    inference(cnf_transformation,[],[f9])).
% 23.44/3.50  
% 23.44/3.50  fof(f5,axiom,(
% 23.44/3.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f29,plain,(
% 23.44/3.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.44/3.50    inference(nnf_transformation,[],[f5])).
% 23.44/3.50  
% 23.44/3.50  fof(f30,plain,(
% 23.44/3.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.44/3.50    inference(rectify,[],[f29])).
% 23.44/3.50  
% 23.44/3.50  fof(f31,plain,(
% 23.44/3.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f32,plain,(
% 23.44/3.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.44/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 23.44/3.50  
% 23.44/3.50  fof(f53,plain,(
% 23.44/3.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 23.44/3.50    inference(cnf_transformation,[],[f32])).
% 23.44/3.50  
% 23.44/3.50  fof(f91,plain,(
% 23.44/3.50    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 23.44/3.50    inference(equality_resolution,[],[f53])).
% 23.44/3.50  
% 23.44/3.50  fof(f2,axiom,(
% 23.44/3.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f14,plain,(
% 23.44/3.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 23.44/3.50    inference(ennf_transformation,[],[f2])).
% 23.44/3.50  
% 23.44/3.50  fof(f15,plain,(
% 23.44/3.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 23.44/3.50    inference(flattening,[],[f14])).
% 23.44/3.50  
% 23.44/3.50  fof(f50,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f15])).
% 23.44/3.50  
% 23.44/3.50  fof(f54,plain,(
% 23.44/3.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 23.44/3.50    inference(cnf_transformation,[],[f32])).
% 23.44/3.50  
% 23.44/3.50  fof(f90,plain,(
% 23.44/3.50    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 23.44/3.50    inference(equality_resolution,[],[f54])).
% 23.44/3.50  
% 23.44/3.50  fof(f60,plain,(
% 23.44/3.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f34])).
% 23.44/3.50  
% 23.44/3.50  fof(f1,axiom,(
% 23.44/3.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f25,plain,(
% 23.44/3.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 23.44/3.50    inference(nnf_transformation,[],[f1])).
% 23.44/3.50  
% 23.44/3.50  fof(f26,plain,(
% 23.44/3.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.44/3.50    inference(rectify,[],[f25])).
% 23.44/3.50  
% 23.44/3.50  fof(f27,plain,(
% 23.44/3.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f28,plain,(
% 23.44/3.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.44/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 23.44/3.50  
% 23.44/3.50  fof(f48,plain,(
% 23.44/3.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f28])).
% 23.44/3.50  
% 23.44/3.50  fof(f12,conjecture,(
% 23.44/3.50    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f13,negated_conjecture,(
% 23.44/3.50    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => (k1_xboole_0 != X0 => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)))))))))),
% 23.44/3.50    inference(negated_conjecture,[],[f12])).
% 23.44/3.50  
% 23.44/3.50  fof(f21,plain,(
% 23.44/3.50    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 23.44/3.50    inference(ennf_transformation,[],[f13])).
% 23.44/3.50  
% 23.44/3.50  fof(f22,plain,(
% 23.44/3.50    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 23.44/3.50    inference(flattening,[],[f21])).
% 23.44/3.50  
% 23.44/3.50  fof(f46,plain,(
% 23.44/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) => (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,sK10),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(sK10,X0))) )),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f45,plain,(
% 23.44/3.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) => (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,sK9,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(sK9,X0))) )),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f44,plain,(
% 23.44/3.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,sK8,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(sK8,X0))) )),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f43,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) => (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,sK7,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(sK7,X0))) )),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f42,plain,(
% 23.44/3.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,sK6,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(sK6,X0))) )),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f41,plain,(
% 23.44/3.50    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~m1_subset_1(k4_enumset1(sK5,X2,X3,X4,X5,X6),k1_zfmisc_1(sK4)) & k1_xboole_0 != sK4 & m1_subset_1(X6,sK4)) & m1_subset_1(X5,sK4)) & m1_subset_1(X4,sK4)) & m1_subset_1(X3,sK4)) & m1_subset_1(X2,sK4)) & m1_subset_1(sK5,sK4))),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f47,plain,(
% 23.44/3.50    (((((~m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4)) & k1_xboole_0 != sK4 & m1_subset_1(sK10,sK4)) & m1_subset_1(sK9,sK4)) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,sK4)) & m1_subset_1(sK6,sK4)) & m1_subset_1(sK5,sK4)),
% 23.44/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f22,f46,f45,f44,f43,f42,f41])).
% 23.44/3.50  
% 23.44/3.50  fof(f87,plain,(
% 23.44/3.50    ~m1_subset_1(k4_enumset1(sK5,sK6,sK7,sK8,sK9,sK10),k1_zfmisc_1(sK4))),
% 23.44/3.50    inference(cnf_transformation,[],[f47])).
% 23.44/3.50  
% 23.44/3.50  fof(f3,axiom,(
% 23.44/3.50    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f51,plain,(
% 23.44/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f3])).
% 23.44/3.50  
% 23.44/3.50  fof(f89,plain,(
% 23.44/3.50    ~m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4))),
% 23.44/3.50    inference(definition_unfolding,[],[f87,f51])).
% 23.44/3.50  
% 23.44/3.50  fof(f6,axiom,(
% 23.44/3.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f33,plain,(
% 23.44/3.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 23.44/3.50    inference(nnf_transformation,[],[f6])).
% 23.44/3.50  
% 23.44/3.50  fof(f58,plain,(
% 23.44/3.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f33])).
% 23.44/3.50  
% 23.44/3.50  fof(f80,plain,(
% 23.44/3.50    m1_subset_1(sK5,sK4)),
% 23.44/3.50    inference(cnf_transformation,[],[f47])).
% 23.44/3.50  
% 23.44/3.50  fof(f85,plain,(
% 23.44/3.50    m1_subset_1(sK10,sK4)),
% 23.44/3.50    inference(cnf_transformation,[],[f47])).
% 23.44/3.50  
% 23.44/3.50  fof(f61,plain,(
% 23.44/3.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f34])).
% 23.44/3.50  
% 23.44/3.50  fof(f86,plain,(
% 23.44/3.50    k1_xboole_0 != sK4),
% 23.44/3.50    inference(cnf_transformation,[],[f47])).
% 23.44/3.50  
% 23.44/3.50  fof(f62,plain,(
% 23.44/3.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f34])).
% 23.44/3.50  
% 23.44/3.50  fof(f23,plain,(
% 23.44/3.50    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 23.44/3.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 23.44/3.50  
% 23.44/3.50  fof(f35,plain,(
% 23.44/3.50    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 23.44/3.50    inference(nnf_transformation,[],[f23])).
% 23.44/3.50  
% 23.44/3.50  fof(f36,plain,(
% 23.44/3.50    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 23.44/3.50    inference(flattening,[],[f35])).
% 23.44/3.50  
% 23.44/3.50  fof(f37,plain,(
% 23.44/3.50    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 23.44/3.50    inference(rectify,[],[f36])).
% 23.44/3.50  
% 23.44/3.50  fof(f38,plain,(
% 23.44/3.50    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK3(X0,X1,X2,X3,X4,X5) != X0 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X0 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5))))),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f39,plain,(
% 23.44/3.50    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK3(X0,X1,X2,X3,X4,X5) != X0 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X0 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 23.44/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 23.44/3.50  
% 23.44/3.50  fof(f64,plain,(
% 23.44/3.50    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f39])).
% 23.44/3.50  
% 23.44/3.50  fof(f96,plain,(
% 23.44/3.50    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X7,X5)) )),
% 23.44/3.50    inference(equality_resolution,[],[f64])).
% 23.44/3.50  
% 23.44/3.50  fof(f8,axiom,(
% 23.44/3.50    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f17,plain,(
% 23.44/3.50    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 23.44/3.50    inference(ennf_transformation,[],[f8])).
% 23.44/3.50  
% 23.44/3.50  fof(f24,plain,(
% 23.44/3.50    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 23.44/3.50    inference(definition_folding,[],[f17,f23])).
% 23.44/3.50  
% 23.44/3.50  fof(f40,plain,(
% 23.44/3.50    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 23.44/3.50    inference(nnf_transformation,[],[f24])).
% 23.44/3.50  
% 23.44/3.50  fof(f75,plain,(
% 23.44/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 23.44/3.50    inference(cnf_transformation,[],[f40])).
% 23.44/3.50  
% 23.44/3.50  fof(f97,plain,(
% 23.44/3.50    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 23.44/3.50    inference(equality_resolution,[],[f75])).
% 23.44/3.50  
% 23.44/3.50  fof(f10,axiom,(
% 23.44/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 23.44/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f18,plain,(
% 23.44/3.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.44/3.50    inference(ennf_transformation,[],[f10])).
% 23.44/3.50  
% 23.44/3.50  fof(f78,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.44/3.50    inference(cnf_transformation,[],[f18])).
% 23.44/3.50  
% 23.44/3.50  fof(f84,plain,(
% 23.44/3.50    m1_subset_1(sK9,sK4)),
% 23.44/3.50    inference(cnf_transformation,[],[f47])).
% 23.44/3.50  
% 23.44/3.50  fof(f83,plain,(
% 23.44/3.50    m1_subset_1(sK8,sK4)),
% 23.44/3.50    inference(cnf_transformation,[],[f47])).
% 23.44/3.50  
% 23.44/3.50  fof(f82,plain,(
% 23.44/3.50    m1_subset_1(sK7,sK4)),
% 23.44/3.50    inference(cnf_transformation,[],[f47])).
% 23.44/3.50  
% 23.44/3.50  fof(f81,plain,(
% 23.44/3.50    m1_subset_1(sK6,sK4)),
% 23.44/3.50    inference(cnf_transformation,[],[f47])).
% 23.44/3.50  
% 23.44/3.50  cnf(c_30,plain,
% 23.44/3.50      ( ~ m1_subset_1(X0,X1)
% 23.44/3.50      | ~ m1_subset_1(X2,X1)
% 23.44/3.50      | ~ m1_subset_1(X3,X1)
% 23.44/3.50      | ~ m1_subset_1(X4,X1)
% 23.44/3.50      | ~ m1_subset_1(X5,X1)
% 23.44/3.50      | m1_subset_1(k3_enumset1(X0,X5,X4,X3,X2),k1_zfmisc_1(X1))
% 23.44/3.50      | k1_xboole_0 = X1 ),
% 23.44/3.50      inference(cnf_transformation,[],[f79]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2229,plain,
% 23.44/3.50      ( k1_xboole_0 = X0
% 23.44/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X2,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X3,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X4,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X5,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_13,plain,
% 23.44/3.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.44/3.50      inference(cnf_transformation,[],[f59]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2246,plain,
% 23.44/3.50      ( m1_subset_1(X0,X1) != iProver_top
% 23.44/3.50      | r2_hidden(X0,X1) = iProver_top
% 23.44/3.50      | v1_xboole_0(X1) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_4468,plain,
% 23.44/3.50      ( k1_xboole_0 = X0
% 23.44/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X2,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X3,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X4,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X5,X0) != iProver_top
% 23.44/3.50      | r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
% 23.44/3.50      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_2229,c_2246]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_28,plain,
% 23.44/3.50      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 23.44/3.50      inference(cnf_transformation,[],[f77]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_50,plain,
% 23.44/3.50      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_8648,plain,
% 23.44/3.50      ( r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
% 23.44/3.50      | m1_subset_1(X5,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X4,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X3,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X2,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.44/3.50      | k1_xboole_0 = X0 ),
% 23.44/3.50      inference(global_propositional_subsumption,
% 23.44/3.50                [status(thm)],
% 23.44/3.50                [c_4468,c_50]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_8649,plain,
% 23.44/3.50      ( k1_xboole_0 = X0
% 23.44/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X2,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X3,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X4,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X5,X0) != iProver_top
% 23.44/3.50      | r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 23.44/3.50      inference(renaming,[status(thm)],[c_8648]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_7,plain,
% 23.44/3.50      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 23.44/3.50      inference(cnf_transformation,[],[f91]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2251,plain,
% 23.44/3.50      ( r1_tarski(X0,X1) = iProver_top
% 23.44/3.50      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_8656,plain,
% 23.44/3.50      ( k1_xboole_0 = X0
% 23.44/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X2,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X3,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X4,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X5,X0) != iProver_top
% 23.44/3.50      | r1_tarski(k3_enumset1(X1,X5,X4,X3,X2),X0) = iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_8649,c_2251]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2,plain,
% 23.44/3.50      ( ~ r1_tarski(X0,X1)
% 23.44/3.50      | ~ r1_tarski(X2,X1)
% 23.44/3.50      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 23.44/3.50      inference(cnf_transformation,[],[f50]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2255,plain,
% 23.44/3.50      ( r1_tarski(X0,X1) != iProver_top
% 23.44/3.50      | r1_tarski(X2,X1) != iProver_top
% 23.44/3.50      | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_6,plain,
% 23.44/3.50      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 23.44/3.50      inference(cnf_transformation,[],[f90]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2252,plain,
% 23.44/3.50      ( r1_tarski(X0,X1) != iProver_top
% 23.44/3.50      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_12,plain,
% 23.44/3.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.44/3.50      inference(cnf_transformation,[],[f60]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_1,plain,
% 23.44/3.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 23.44/3.50      inference(cnf_transformation,[],[f48]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_217,plain,
% 23.44/3.50      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 23.44/3.50      inference(global_propositional_subsumption,
% 23.44/3.50                [status(thm)],
% 23.44/3.50                [c_12,c_1]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_218,plain,
% 23.44/3.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 23.44/3.50      inference(renaming,[status(thm)],[c_217]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2221,plain,
% 23.44/3.50      ( m1_subset_1(X0,X1) = iProver_top
% 23.44/3.50      | r2_hidden(X0,X1) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_3820,plain,
% 23.44/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.44/3.50      | r1_tarski(X0,X1) != iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_2252,c_2221]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_31,negated_conjecture,
% 23.44/3.50      ( ~ m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
% 23.44/3.50      inference(cnf_transformation,[],[f89]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2228,plain,
% 23.44/3.50      ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_3826,plain,
% 23.44/3.50      ( r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4) != iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_3820,c_2228]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_5170,plain,
% 23.44/3.50      ( r1_tarski(k3_enumset1(sK6,sK7,sK8,sK9,sK10),sK4) != iProver_top
% 23.44/3.50      | r1_tarski(k1_tarski(sK5),sK4) != iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_2255,c_3826]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_45,plain,
% 23.44/3.50      ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2303,plain,
% 23.44/3.50      ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4))
% 23.44/3.50      | ~ r2_hidden(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_218]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2304,plain,
% 23.44/3.50      ( m1_subset_1(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) = iProver_top
% 23.44/3.50      | r2_hidden(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_2303]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2341,plain,
% 23.44/3.50      ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4)
% 23.44/3.50      | r2_hidden(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_6]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2342,plain,
% 23.44/3.50      ( r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4) != iProver_top
% 23.44/3.50      | r2_hidden(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),k1_zfmisc_1(sK4)) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_2341]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2480,plain,
% 23.44/3.50      ( ~ r1_tarski(k3_enumset1(sK6,sK7,sK8,sK9,sK10),sK4)
% 23.44/3.50      | r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4)
% 23.44/3.50      | ~ r1_tarski(k1_tarski(sK5),sK4) ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2481,plain,
% 23.44/3.50      ( r1_tarski(k3_enumset1(sK6,sK7,sK8,sK9,sK10),sK4) != iProver_top
% 23.44/3.50      | r1_tarski(k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK6,sK7,sK8,sK9,sK10)),sK4) = iProver_top
% 23.44/3.50      | r1_tarski(k1_tarski(sK5),sK4) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_2480]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_8,plain,
% 23.44/3.50      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 23.44/3.50      inference(cnf_transformation,[],[f58]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_3149,plain,
% 23.44/3.50      ( r1_tarski(k1_tarski(sK5),sK4) | ~ r2_hidden(sK5,sK4) ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_8]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_3150,plain,
% 23.44/3.50      ( r1_tarski(k1_tarski(sK5),sK4) = iProver_top
% 23.44/3.50      | r2_hidden(sK5,sK4) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_3149]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_38,negated_conjecture,
% 23.44/3.50      ( m1_subset_1(sK5,sK4) ),
% 23.44/3.50      inference(cnf_transformation,[],[f80]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2222,plain,
% 23.44/3.50      ( m1_subset_1(sK5,sK4) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_4467,plain,
% 23.44/3.50      ( r2_hidden(sK5,sK4) = iProver_top
% 23.44/3.50      | v1_xboole_0(sK4) = iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_2222,c_2246]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_33,negated_conjecture,
% 23.44/3.50      ( m1_subset_1(sK10,sK4) ),
% 23.44/3.50      inference(cnf_transformation,[],[f85]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2227,plain,
% 23.44/3.50      ( m1_subset_1(sK10,sK4) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_11,plain,
% 23.44/3.50      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 23.44/3.50      inference(cnf_transformation,[],[f61]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2247,plain,
% 23.44/3.50      ( m1_subset_1(X0,X1) != iProver_top
% 23.44/3.50      | v1_xboole_0(X1) != iProver_top
% 23.44/3.50      | v1_xboole_0(X0) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_4483,plain,
% 23.44/3.50      ( v1_xboole_0(sK4) != iProver_top
% 23.44/3.50      | v1_xboole_0(sK10) = iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_2227,c_2247]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_32,negated_conjecture,
% 23.44/3.50      ( k1_xboole_0 != sK4 ),
% 23.44/3.50      inference(cnf_transformation,[],[f86]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_10,plain,
% 23.44/3.50      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 23.44/3.50      inference(cnf_transformation,[],[f62]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_86,plain,
% 23.44/3.50      ( m1_subset_1(X0,X1) = iProver_top
% 23.44/3.50      | v1_xboole_0(X1) != iProver_top
% 23.44/3.50      | v1_xboole_0(X0) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_88,plain,
% 23.44/3.50      ( m1_subset_1(sK4,sK4) = iProver_top
% 23.44/3.50      | v1_xboole_0(sK4) != iProver_top ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_86]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_111,plain,
% 23.44/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.44/3.50      | v1_xboole_0(X1) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_113,plain,
% 23.44/3.50      ( r2_hidden(sK4,sK4) != iProver_top
% 23.44/3.50      | v1_xboole_0(sK4) != iProver_top ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_111]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_24,plain,
% 23.44/3.50      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X4,X5) ),
% 23.44/3.50      inference(cnf_transformation,[],[f96]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_27,plain,
% 23.44/3.50      ( sP0(X0,X1,X2,X3,X4,k3_enumset1(X4,X3,X2,X1,X0)) ),
% 23.44/3.50      inference(cnf_transformation,[],[f97]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_1203,plain,
% 23.44/3.50      ( r2_hidden(X0,X1)
% 23.44/3.50      | X2 != X3
% 23.44/3.50      | X4 != X0
% 23.44/3.50      | X5 != X6
% 23.44/3.50      | X7 != X8
% 23.44/3.50      | X9 != X10
% 23.44/3.50      | k3_enumset1(X4,X5,X7,X9,X2) != X1 ),
% 23.44/3.50      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_1204,plain,
% 23.44/3.50      ( r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
% 23.44/3.50      inference(unflattening,[status(thm)],[c_1203]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_1205,plain,
% 23.44/3.50      ( r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4)) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_1204]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_1207,plain,
% 23.44/3.50      ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_1205]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_29,plain,
% 23.44/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.44/3.50      | ~ r2_hidden(X2,X0)
% 23.44/3.50      | r2_hidden(X2,X1) ),
% 23.44/3.50      inference(cnf_transformation,[],[f78]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2230,plain,
% 23.44/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.44/3.50      | r2_hidden(X2,X0) != iProver_top
% 23.44/3.50      | r2_hidden(X2,X1) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_4417,plain,
% 23.44/3.50      ( k1_xboole_0 = X0
% 23.44/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X2,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X3,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X4,X0) != iProver_top
% 23.44/3.50      | m1_subset_1(X5,X0) != iProver_top
% 23.44/3.50      | r2_hidden(X6,X0) = iProver_top
% 23.44/3.50      | r2_hidden(X6,k3_enumset1(X1,X5,X4,X3,X2)) != iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_2229,c_2230]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_4420,plain,
% 23.44/3.50      ( k1_xboole_0 = sK4
% 23.44/3.50      | m1_subset_1(sK4,sK4) != iProver_top
% 23.44/3.50      | r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 23.44/3.50      | r2_hidden(sK4,sK4) = iProver_top ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_4417]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_4577,plain,
% 23.44/3.50      ( v1_xboole_0(sK4) != iProver_top ),
% 23.44/3.50      inference(global_propositional_subsumption,
% 23.44/3.50                [status(thm)],
% 23.44/3.50                [c_4483,c_32,c_88,c_113,c_1207,c_4420]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_5503,plain,
% 23.44/3.50      ( r1_tarski(k3_enumset1(sK6,sK7,sK8,sK9,sK10),sK4) != iProver_top ),
% 23.44/3.50      inference(global_propositional_subsumption,
% 23.44/3.50                [status(thm)],
% 23.44/3.50                [c_5170,c_32,c_45,c_88,c_113,c_1207,c_2304,c_2342,c_2481,
% 23.44/3.50                 c_3150,c_4420,c_4467]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_71831,plain,
% 23.44/3.50      ( sK4 = k1_xboole_0
% 23.44/3.50      | m1_subset_1(sK10,sK4) != iProver_top
% 23.44/3.50      | m1_subset_1(sK9,sK4) != iProver_top
% 23.44/3.50      | m1_subset_1(sK8,sK4) != iProver_top
% 23.44/3.50      | m1_subset_1(sK7,sK4) != iProver_top
% 23.44/3.50      | m1_subset_1(sK6,sK4) != iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_8656,c_5503]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_1424,plain,( X0 = X0 ),theory(equality) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_3209,plain,
% 23.44/3.50      ( k1_xboole_0 = k1_xboole_0 ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_1424]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_1425,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2318,plain,
% 23.44/3.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_1425]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2395,plain,
% 23.44/3.50      ( sK4 != k1_xboole_0
% 23.44/3.50      | k1_xboole_0 = sK4
% 23.44/3.50      | k1_xboole_0 != k1_xboole_0 ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_2318]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_44,plain,
% 23.44/3.50      ( m1_subset_1(sK10,sK4) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_34,negated_conjecture,
% 23.44/3.50      ( m1_subset_1(sK9,sK4) ),
% 23.44/3.50      inference(cnf_transformation,[],[f84]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_43,plain,
% 23.44/3.50      ( m1_subset_1(sK9,sK4) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_35,negated_conjecture,
% 23.44/3.50      ( m1_subset_1(sK8,sK4) ),
% 23.44/3.50      inference(cnf_transformation,[],[f83]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_42,plain,
% 23.44/3.50      ( m1_subset_1(sK8,sK4) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_36,negated_conjecture,
% 23.44/3.50      ( m1_subset_1(sK7,sK4) ),
% 23.44/3.50      inference(cnf_transformation,[],[f82]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_41,plain,
% 23.44/3.50      ( m1_subset_1(sK7,sK4) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_37,negated_conjecture,
% 23.44/3.50      ( m1_subset_1(sK6,sK4) ),
% 23.44/3.50      inference(cnf_transformation,[],[f81]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_40,plain,
% 23.44/3.50      ( m1_subset_1(sK6,sK4) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(contradiction,plain,
% 23.44/3.50      ( $false ),
% 23.44/3.50      inference(minisat,
% 23.44/3.50                [status(thm)],
% 23.44/3.50                [c_71831,c_3209,c_2395,c_32,c_44,c_43,c_42,c_41,c_40]) ).
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.44/3.50  
% 23.44/3.50  ------                               Statistics
% 23.44/3.50  
% 23.44/3.50  ------ General
% 23.44/3.50  
% 23.44/3.50  abstr_ref_over_cycles:                  0
% 23.44/3.50  abstr_ref_under_cycles:                 0
% 23.44/3.50  gc_basic_clause_elim:                   0
% 23.44/3.50  forced_gc_time:                         0
% 23.44/3.50  parsing_time:                           0.008
% 23.44/3.50  unif_index_cands_time:                  0.
% 23.44/3.50  unif_index_add_time:                    0.
% 23.44/3.50  orderings_time:                         0.
% 23.44/3.50  out_proof_time:                         0.013
% 23.44/3.50  total_time:                             2.925
% 23.44/3.50  num_of_symbols:                         51
% 23.44/3.50  num_of_terms:                           96376
% 23.44/3.50  
% 23.44/3.50  ------ Preprocessing
% 23.44/3.50  
% 23.44/3.50  num_of_splits:                          0
% 23.44/3.50  num_of_split_atoms:                     0
% 23.44/3.50  num_of_reused_defs:                     0
% 23.44/3.50  num_eq_ax_congr_red:                    30
% 23.44/3.50  num_of_sem_filtered_clauses:            1
% 23.44/3.50  num_of_subtypes:                        0
% 23.44/3.50  monotx_restored_types:                  0
% 23.44/3.50  sat_num_of_epr_types:                   0
% 23.44/3.50  sat_num_of_non_cyclic_types:            0
% 23.44/3.50  sat_guarded_non_collapsed_types:        0
% 23.44/3.50  num_pure_diseq_elim:                    0
% 23.44/3.50  simp_replaced_by:                       0
% 23.44/3.50  res_preprocessed:                       140
% 23.44/3.50  prep_upred:                             0
% 23.44/3.50  prep_unflattend:                        42
% 23.44/3.50  smt_new_axioms:                         0
% 23.44/3.50  pred_elim_cands:                        5
% 23.44/3.50  pred_elim:                              0
% 23.44/3.50  pred_elim_cl:                           0
% 23.44/3.50  pred_elim_cycles:                       1
% 23.44/3.50  merged_defs:                            12
% 23.44/3.50  merged_defs_ncl:                        0
% 23.44/3.50  bin_hyper_res:                          12
% 23.44/3.50  prep_cycles:                            3
% 23.44/3.50  pred_elim_time:                         0.01
% 23.44/3.50  splitting_time:                         0.
% 23.44/3.50  sem_filter_time:                        0.
% 23.44/3.50  monotx_time:                            0.
% 23.44/3.50  subtype_inf_time:                       0.
% 23.44/3.50  
% 23.44/3.50  ------ Problem properties
% 23.44/3.50  
% 23.44/3.50  clauses:                                39
% 23.44/3.50  conjectures:                            8
% 23.44/3.50  epr:                                    18
% 23.44/3.50  horn:                                   33
% 23.44/3.50  ground:                                 8
% 23.44/3.50  unary:                                  11
% 23.44/3.50  binary:                                 13
% 23.44/3.50  lits:                                   94
% 23.44/3.50  lits_eq:                                21
% 23.44/3.50  fd_pure:                                0
% 23.44/3.50  fd_pseudo:                              0
% 23.44/3.50  fd_cond:                                1
% 23.44/3.50  fd_pseudo_cond:                         4
% 23.44/3.50  ac_symbols:                             0
% 23.44/3.50  
% 23.44/3.50  ------ Propositional Solver
% 23.44/3.50  
% 23.44/3.50  prop_solver_calls:                      29
% 23.44/3.50  prop_fast_solver_calls:                 3604
% 23.44/3.50  smt_solver_calls:                       0
% 23.44/3.50  smt_fast_solver_calls:                  0
% 23.44/3.50  prop_num_of_clauses:                    28986
% 23.44/3.50  prop_preprocess_simplified:             75791
% 23.44/3.50  prop_fo_subsumed:                       17
% 23.44/3.50  prop_solver_time:                       0.
% 23.44/3.50  smt_solver_time:                        0.
% 23.44/3.50  smt_fast_solver_time:                   0.
% 23.44/3.50  prop_fast_solver_time:                  0.
% 23.44/3.50  prop_unsat_core_time:                   0.002
% 23.44/3.50  
% 23.44/3.50  ------ QBF
% 23.44/3.50  
% 23.44/3.50  qbf_q_res:                              0
% 23.44/3.50  qbf_num_tautologies:                    0
% 23.44/3.50  qbf_prep_cycles:                        0
% 23.44/3.50  
% 23.44/3.50  ------ BMC1
% 23.44/3.50  
% 23.44/3.50  bmc1_current_bound:                     -1
% 23.44/3.50  bmc1_last_solved_bound:                 -1
% 23.44/3.50  bmc1_unsat_core_size:                   -1
% 23.44/3.50  bmc1_unsat_core_parents_size:           -1
% 23.44/3.50  bmc1_merge_next_fun:                    0
% 23.44/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.44/3.50  
% 23.44/3.50  ------ Instantiation
% 23.44/3.50  
% 23.44/3.50  inst_num_of_clauses:                    8015
% 23.44/3.50  inst_num_in_passive:                    6605
% 23.44/3.50  inst_num_in_active:                     1087
% 23.44/3.50  inst_num_in_unprocessed:                323
% 23.44/3.50  inst_num_of_loops:                      1370
% 23.44/3.50  inst_num_of_learning_restarts:          0
% 23.44/3.50  inst_num_moves_active_passive:          282
% 23.44/3.50  inst_lit_activity:                      0
% 23.44/3.50  inst_lit_activity_moves:                0
% 23.44/3.50  inst_num_tautologies:                   0
% 23.44/3.50  inst_num_prop_implied:                  0
% 23.44/3.50  inst_num_existing_simplified:           0
% 23.44/3.50  inst_num_eq_res_simplified:             0
% 23.44/3.50  inst_num_child_elim:                    0
% 23.44/3.50  inst_num_of_dismatching_blockings:      8863
% 23.44/3.50  inst_num_of_non_proper_insts:           8698
% 23.44/3.50  inst_num_of_duplicates:                 0
% 23.44/3.50  inst_inst_num_from_inst_to_res:         0
% 23.44/3.50  inst_dismatching_checking_time:         0.
% 23.44/3.50  
% 23.44/3.50  ------ Resolution
% 23.44/3.50  
% 23.44/3.50  res_num_of_clauses:                     0
% 23.44/3.50  res_num_in_passive:                     0
% 23.44/3.50  res_num_in_active:                      0
% 23.44/3.50  res_num_of_loops:                       143
% 23.44/3.50  res_forward_subset_subsumed:            1456
% 23.44/3.50  res_backward_subset_subsumed:           2
% 23.44/3.50  res_forward_subsumed:                   0
% 23.44/3.50  res_backward_subsumed:                  0
% 23.44/3.50  res_forward_subsumption_resolution:     0
% 23.44/3.50  res_backward_subsumption_resolution:    0
% 23.44/3.50  res_clause_to_clause_subsumption:       33290
% 23.44/3.50  res_orphan_elimination:                 0
% 23.44/3.50  res_tautology_del:                      117
% 23.44/3.50  res_num_eq_res_simplified:              0
% 23.44/3.50  res_num_sel_changes:                    0
% 23.44/3.50  res_moves_from_active_to_pass:          0
% 23.44/3.50  
% 23.44/3.50  ------ Superposition
% 23.44/3.50  
% 23.44/3.50  sup_time_total:                         0.
% 23.44/3.50  sup_time_generating:                    0.
% 23.44/3.50  sup_time_sim_full:                      0.
% 23.44/3.50  sup_time_sim_immed:                     0.
% 23.44/3.50  
% 23.44/3.50  sup_num_of_clauses:                     1939
% 23.44/3.50  sup_num_in_active:                      274
% 23.44/3.50  sup_num_in_passive:                     1665
% 23.44/3.50  sup_num_of_loops:                       273
% 23.44/3.50  sup_fw_superposition:                   1169
% 23.44/3.50  sup_bw_superposition:                   1122
% 23.44/3.50  sup_immediate_simplified:               181
% 23.44/3.50  sup_given_eliminated:                   0
% 23.44/3.50  comparisons_done:                       0
% 23.44/3.50  comparisons_avoided:                    24
% 23.44/3.50  
% 23.44/3.50  ------ Simplifications
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  sim_fw_subset_subsumed:                 24
% 23.44/3.50  sim_bw_subset_subsumed:                 7
% 23.44/3.50  sim_fw_subsumed:                        149
% 23.44/3.50  sim_bw_subsumed:                        5
% 23.44/3.50  sim_fw_subsumption_res:                 0
% 23.44/3.50  sim_bw_subsumption_res:                 0
% 23.44/3.50  sim_tautology_del:                      7
% 23.44/3.50  sim_eq_tautology_del:                   30
% 23.44/3.50  sim_eq_res_simp:                        3
% 23.44/3.50  sim_fw_demodulated:                     3
% 23.44/3.50  sim_bw_demodulated:                     0
% 23.44/3.50  sim_light_normalised:                   0
% 23.44/3.50  sim_joinable_taut:                      0
% 23.44/3.50  sim_joinable_simp:                      0
% 23.44/3.50  sim_ac_normalised:                      0
% 23.44/3.50  sim_smt_subsumption:                    0
% 23.44/3.50  
%------------------------------------------------------------------------------
