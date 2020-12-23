%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:11 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 396 expanded)
%              Number of clauses        :   73 (  97 expanded)
%              Number of leaves         :   25 ( 143 expanded)
%              Depth                    :   15
%              Number of atoms          :  652 (2759 expanded)
%              Number of equality atoms :  256 ( 646 expanded)
%              Maximal formula depth    :   19 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f82,plain,(
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

fof(f35,plain,(
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

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f3])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X7,X0) )
     => ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,sK11),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK11,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f49,plain,
    ( ~ m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4))
    & k1_xboole_0 != sK4
    & m1_subset_1(sK11,sK4)
    & m1_subset_1(sK10,sK4)
    & m1_subset_1(sK9,sK4)
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,sK4)
    & m1_subset_1(sK6,sK4)
    & m1_subset_1(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f22,f48,f47,f46,f45,f44,f43,f42])).

fof(f91,plain,(
    ~ m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    ~ m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) ),
    inference(definition_unfolding,[],[f91,f53])).

fof(f89,plain,(
    m1_subset_1(sK11,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f90,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f67,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X7,X5) ) ),
    inference(equality_resolution,[],[f67])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f78])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f88,plain,(
    m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X5,X1)
    | m1_subset_1(k3_enumset1(X0,X5,X4,X3,X2),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2352,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2369,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4139,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_2369])).

cnf(c_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_53,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10900,plain,
    ( r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4139,c_53])).

cnf(c_10901,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10900])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2375,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10908,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | r1_tarski(k3_enumset1(X1,X5,X4,X3,X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10901,c_2375])).

cnf(c_3,plain,
    ( k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2379,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4896,plain,
    ( r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),X5) != iProver_top
    | r1_tarski(k2_tarski(X6,X7),X5) != iProver_top
    | r1_tarski(k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X6,X7)),X5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2379])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2376,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_226,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_1])).

cnf(c_227,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_226])).

cnf(c_2343,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_3076,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2376,c_2343])).

cnf(c_32,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2351,plain,
    ( m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8110,plain,
    ( r1_tarski(k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK7,sK8,sK9,sK10,sK11)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3076,c_2351])).

cnf(c_11418,plain,
    ( r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) != iProver_top
    | r1_tarski(k2_tarski(sK10,sK11),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4896,c_8110])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK11,sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3224,plain,
    ( r2_hidden(sK11,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_14,c_34])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_50,plain,
    ( m1_subset_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK4,sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_90,plain,
    ( m1_subset_1(sK4,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_116,plain,
    ( ~ r2_hidden(sK4,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_25,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X4,X5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_28,plain,
    ( sP0(X0,X1,X2,X3,X4,k3_enumset1(X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1220,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | k3_enumset1(X4,X5,X7,X9,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_28])).

cnf(c_1221,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(unflattening,[status(thm)],[c_1220])).

cnf(c_1223,plain,
    ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2736,plain,
    ( ~ m1_subset_1(k3_enumset1(X0,X1,X2,X3,X4),k1_zfmisc_1(X5))
    | r2_hidden(X4,X5)
    | ~ r2_hidden(X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2738,plain,
    ( ~ m1_subset_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2736])).

cnf(c_2879,plain,
    ( ~ m1_subset_1(sK11,sK4)
    | r2_hidden(sK11,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3239,plain,
    ( r2_hidden(sK11,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3224,c_34,c_33,c_50,c_90,c_116,c_1223,c_2738,c_2879])).

cnf(c_3241,plain,
    ( r2_hidden(sK11,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3239])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK10,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3226,plain,
    ( r2_hidden(sK10,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[status(thm)],[c_14,c_35])).

cnf(c_2882,plain,
    ( ~ m1_subset_1(sK10,sK4)
    | r2_hidden(sK10,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3386,plain,
    ( r2_hidden(sK10,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3226,c_35,c_33,c_50,c_90,c_116,c_1223,c_2738,c_2882])).

cnf(c_3388,plain,
    ( r2_hidden(sK10,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3386])).

cnf(c_8,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3533,plain,
    ( r1_tarski(k2_tarski(X0,sK11),sK4)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(sK11,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7263,plain,
    ( r1_tarski(k2_tarski(sK10,sK11),sK4)
    | ~ r2_hidden(sK11,sK4)
    | ~ r2_hidden(sK10,sK4) ),
    inference(instantiation,[status(thm)],[c_3533])).

cnf(c_7264,plain,
    ( r1_tarski(k2_tarski(sK10,sK11),sK4) = iProver_top
    | r2_hidden(sK11,sK4) != iProver_top
    | r2_hidden(sK10,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7263])).

cnf(c_15900,plain,
    ( r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11418,c_3241,c_3388,c_7264])).

cnf(c_25818,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK9,sK4) != iProver_top
    | m1_subset_1(sK8,sK4) != iProver_top
    | m1_subset_1(sK7,sK4) != iProver_top
    | m1_subset_1(sK6,sK4) != iProver_top
    | m1_subset_1(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10908,c_15900])).

cnf(c_1441,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2650,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_1442,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2519,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_2649,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK9,sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_45,plain,
    ( m1_subset_1(sK9,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_44,plain,
    ( m1_subset_1(sK8,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK7,sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_43,plain,
    ( m1_subset_1(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_42,plain,
    ( m1_subset_1(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25818,c_2650,c_2649,c_33,c_45,c_44,c_43,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:07:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.73/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.50  
% 7.73/1.50  ------  iProver source info
% 7.73/1.50  
% 7.73/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.50  git: non_committed_changes: false
% 7.73/1.50  git: last_make_outside_of_git: false
% 7.73/1.50  
% 7.73/1.50  ------ 
% 7.73/1.50  ------ Parsing...
% 7.73/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.50  
% 7.73/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.50  ------ Proving...
% 7.73/1.50  ------ Problem Properties 
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  clauses                                 41
% 7.73/1.50  conjectures                             9
% 7.73/1.50  EPR                                     19
% 7.73/1.50  Horn                                    35
% 7.73/1.50  unary                                   12
% 7.73/1.50  binary                                  13
% 7.73/1.50  lits                                    98
% 7.73/1.50  lits eq                                 21
% 7.73/1.50  fd_pure                                 0
% 7.73/1.50  fd_pseudo                               0
% 7.73/1.50  fd_cond                                 1
% 7.73/1.50  fd_pseudo_cond                          4
% 7.73/1.50  AC symbols                              0
% 7.73/1.50  
% 7.73/1.50  ------ Input Options Time Limit: Unbounded
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ 
% 7.73/1.50  Current options:
% 7.73/1.50  ------ 
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  ------ Proving...
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  % SZS status Theorem for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  fof(f11,axiom,(
% 7.73/1.50    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => (k1_xboole_0 != X0 => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))))))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f19,plain,(
% 7.73/1.50    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 7.73/1.50    inference(ennf_transformation,[],[f11])).
% 7.73/1.50  
% 7.73/1.50  fof(f20,plain,(
% 7.73/1.50    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 7.73/1.50    inference(flattening,[],[f19])).
% 7.73/1.50  
% 7.73/1.50  fof(f82,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f20])).
% 7.73/1.50  
% 7.73/1.50  fof(f7,axiom,(
% 7.73/1.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f16,plain,(
% 7.73/1.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.73/1.50    inference(ennf_transformation,[],[f7])).
% 7.73/1.50  
% 7.73/1.50  fof(f35,plain,(
% 7.73/1.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.73/1.50    inference(nnf_transformation,[],[f16])).
% 7.73/1.50  
% 7.73/1.50  fof(f62,plain,(
% 7.73/1.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f35])).
% 7.73/1.50  
% 7.73/1.50  fof(f9,axiom,(
% 7.73/1.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f80,plain,(
% 7.73/1.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f9])).
% 7.73/1.50  
% 7.73/1.50  fof(f5,axiom,(
% 7.73/1.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f29,plain,(
% 7.73/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.73/1.50    inference(nnf_transformation,[],[f5])).
% 7.73/1.50  
% 7.73/1.50  fof(f30,plain,(
% 7.73/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.73/1.50    inference(rectify,[],[f29])).
% 7.73/1.50  
% 7.73/1.50  fof(f31,plain,(
% 7.73/1.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f32,plain,(
% 7.73/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 7.73/1.50  
% 7.73/1.50  fof(f55,plain,(
% 7.73/1.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.73/1.50    inference(cnf_transformation,[],[f32])).
% 7.73/1.50  
% 7.73/1.50  fof(f95,plain,(
% 7.73/1.50    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.73/1.50    inference(equality_resolution,[],[f55])).
% 7.73/1.50  
% 7.73/1.50  fof(f4,axiom,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f54,plain,(
% 7.73/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f4])).
% 7.73/1.50  
% 7.73/1.50  fof(f3,axiom,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f53,plain,(
% 7.73/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f3])).
% 7.73/1.50  
% 7.73/1.50  fof(f92,plain,(
% 7.73/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 7.73/1.50    inference(definition_unfolding,[],[f54,f53])).
% 7.73/1.50  
% 7.73/1.50  fof(f2,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f14,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.73/1.50    inference(ennf_transformation,[],[f2])).
% 7.73/1.50  
% 7.73/1.50  fof(f15,plain,(
% 7.73/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.73/1.50    inference(flattening,[],[f14])).
% 7.73/1.50  
% 7.73/1.50  fof(f52,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f15])).
% 7.73/1.50  
% 7.73/1.50  fof(f56,plain,(
% 7.73/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.73/1.50    inference(cnf_transformation,[],[f32])).
% 7.73/1.50  
% 7.73/1.50  fof(f94,plain,(
% 7.73/1.50    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.73/1.50    inference(equality_resolution,[],[f56])).
% 7.73/1.50  
% 7.73/1.50  fof(f63,plain,(
% 7.73/1.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f35])).
% 7.73/1.50  
% 7.73/1.50  fof(f1,axiom,(
% 7.73/1.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f25,plain,(
% 7.73/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.50    inference(nnf_transformation,[],[f1])).
% 7.73/1.50  
% 7.73/1.50  fof(f26,plain,(
% 7.73/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.50    inference(rectify,[],[f25])).
% 7.73/1.50  
% 7.73/1.50  fof(f27,plain,(
% 7.73/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f28,plain,(
% 7.73/1.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 7.73/1.50  
% 7.73/1.50  fof(f50,plain,(
% 7.73/1.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f28])).
% 7.73/1.50  
% 7.73/1.50  fof(f12,conjecture,(
% 7.73/1.50    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => (k1_xboole_0 != X0 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))))))))))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f13,negated_conjecture,(
% 7.73/1.50    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => (k1_xboole_0 != X0 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))))))))))),
% 7.73/1.50    inference(negated_conjecture,[],[f12])).
% 7.73/1.50  
% 7.73/1.50  fof(f21,plain,(
% 7.73/1.50    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 7.73/1.50    inference(ennf_transformation,[],[f13])).
% 7.73/1.50  
% 7.73/1.50  fof(f22,plain,(
% 7.73/1.50    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 7.73/1.50    inference(flattening,[],[f21])).
% 7.73/1.50  
% 7.73/1.50  fof(f48,plain,(
% 7.73/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) => (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,sK11),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(sK11,X0))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f47,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) => (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,sK10,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(sK10,X0))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f46,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,sK9,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(sK9,X0))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f45,plain,(
% 7.73/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,sK8,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(sK8,X0))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f44,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,sK7,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(sK7,X0))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f43,plain,(
% 7.73/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,sK6,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(sK6,X0))) )),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f42,plain,(
% 7.73/1.50    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X7,X0)) & m1_subset_1(X6,X0)) & m1_subset_1(X5,X0)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,X0)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (~m1_subset_1(k5_enumset1(sK5,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK4)) & k1_xboole_0 != sK4 & m1_subset_1(X7,sK4)) & m1_subset_1(X6,sK4)) & m1_subset_1(X5,sK4)) & m1_subset_1(X4,sK4)) & m1_subset_1(X3,sK4)) & m1_subset_1(X2,sK4)) & m1_subset_1(sK5,sK4))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f49,plain,(
% 7.73/1.50    ((((((~m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4)) & k1_xboole_0 != sK4 & m1_subset_1(sK11,sK4)) & m1_subset_1(sK10,sK4)) & m1_subset_1(sK9,sK4)) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,sK4)) & m1_subset_1(sK6,sK4)) & m1_subset_1(sK5,sK4)),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f22,f48,f47,f46,f45,f44,f43,f42])).
% 7.73/1.50  
% 7.73/1.50  fof(f91,plain,(
% 7.73/1.50    ~m1_subset_1(k5_enumset1(sK5,sK6,sK7,sK8,sK9,sK10,sK11),k1_zfmisc_1(sK4))),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f93,plain,(
% 7.73/1.50    ~m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4))),
% 7.73/1.50    inference(definition_unfolding,[],[f91,f53])).
% 7.73/1.50  
% 7.73/1.50  fof(f89,plain,(
% 7.73/1.50    m1_subset_1(sK11,sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f90,plain,(
% 7.73/1.50    k1_xboole_0 != sK4),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f65,plain,(
% 7.73/1.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f35])).
% 7.73/1.50  
% 7.73/1.50  fof(f23,plain,(
% 7.73/1.50    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 7.73/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.73/1.50  
% 7.73/1.50  fof(f36,plain,(
% 7.73/1.50    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 7.73/1.50    inference(nnf_transformation,[],[f23])).
% 7.73/1.50  
% 7.73/1.50  fof(f37,plain,(
% 7.73/1.50    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 7.73/1.50    inference(flattening,[],[f36])).
% 7.73/1.50  
% 7.73/1.50  fof(f38,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 7.73/1.50    inference(rectify,[],[f37])).
% 7.73/1.50  
% 7.73/1.50  fof(f39,plain,(
% 7.73/1.50    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK3(X0,X1,X2,X3,X4,X5) != X0 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X0 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5))))),
% 7.73/1.50    introduced(choice_axiom,[])).
% 7.73/1.50  
% 7.73/1.50  fof(f40,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK3(X0,X1,X2,X3,X4,X5) != X0 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X0 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 7.73/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 7.73/1.50  
% 7.73/1.50  fof(f67,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f40])).
% 7.73/1.50  
% 7.73/1.50  fof(f100,plain,(
% 7.73/1.50    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X7,X5)) )),
% 7.73/1.50    inference(equality_resolution,[],[f67])).
% 7.73/1.50  
% 7.73/1.50  fof(f8,axiom,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f17,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 7.73/1.50    inference(ennf_transformation,[],[f8])).
% 7.73/1.50  
% 7.73/1.50  fof(f24,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 7.73/1.50    inference(definition_folding,[],[f17,f23])).
% 7.73/1.50  
% 7.73/1.50  fof(f41,plain,(
% 7.73/1.50    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 7.73/1.50    inference(nnf_transformation,[],[f24])).
% 7.73/1.50  
% 7.73/1.50  fof(f78,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 7.73/1.50    inference(cnf_transformation,[],[f41])).
% 7.73/1.50  
% 7.73/1.50  fof(f101,plain,(
% 7.73/1.50    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 7.73/1.50    inference(equality_resolution,[],[f78])).
% 7.73/1.50  
% 7.73/1.50  fof(f10,axiom,(
% 7.73/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f18,plain,(
% 7.73/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.73/1.50    inference(ennf_transformation,[],[f10])).
% 7.73/1.50  
% 7.73/1.50  fof(f81,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.73/1.50    inference(cnf_transformation,[],[f18])).
% 7.73/1.50  
% 7.73/1.50  fof(f88,plain,(
% 7.73/1.50    m1_subset_1(sK10,sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f6,axiom,(
% 7.73/1.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.73/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.50  
% 7.73/1.50  fof(f33,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.73/1.50    inference(nnf_transformation,[],[f6])).
% 7.73/1.50  
% 7.73/1.50  fof(f34,plain,(
% 7.73/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.73/1.50    inference(flattening,[],[f33])).
% 7.73/1.50  
% 7.73/1.50  fof(f61,plain,(
% 7.73/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.73/1.50    inference(cnf_transformation,[],[f34])).
% 7.73/1.50  
% 7.73/1.50  fof(f87,plain,(
% 7.73/1.50    m1_subset_1(sK9,sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f86,plain,(
% 7.73/1.50    m1_subset_1(sK8,sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f85,plain,(
% 7.73/1.50    m1_subset_1(sK7,sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f84,plain,(
% 7.73/1.50    m1_subset_1(sK6,sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  fof(f83,plain,(
% 7.73/1.50    m1_subset_1(sK5,sK4)),
% 7.73/1.50    inference(cnf_transformation,[],[f49])).
% 7.73/1.50  
% 7.73/1.50  cnf(c_31,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(X2,X1)
% 7.73/1.50      | ~ m1_subset_1(X3,X1)
% 7.73/1.50      | ~ m1_subset_1(X4,X1)
% 7.73/1.50      | ~ m1_subset_1(X5,X1)
% 7.73/1.50      | m1_subset_1(k3_enumset1(X0,X5,X4,X3,X2),k1_zfmisc_1(X1))
% 7.73/1.50      | k1_xboole_0 = X1 ),
% 7.73/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2352,plain,
% 7.73/1.50      ( k1_xboole_0 = X0
% 7.73/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X3,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X4,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2369,plain,
% 7.73/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.73/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.73/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4139,plain,
% 7.73/1.50      ( k1_xboole_0 = X0
% 7.73/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X3,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X4,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.73/1.50      | r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
% 7.73/1.50      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2352,c_2369]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_29,plain,
% 7.73/1.50      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_53,plain,
% 7.73/1.50      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10900,plain,
% 7.73/1.50      ( r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top
% 7.73/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X4,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X3,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.73/1.50      | k1_xboole_0 = X0 ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_4139,c_53]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10901,plain,
% 7.73/1.50      ( k1_xboole_0 = X0
% 7.73/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X3,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X4,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.73/1.50      | r2_hidden(k3_enumset1(X1,X5,X4,X3,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_10900]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_7,plain,
% 7.73/1.50      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2375,plain,
% 7.73/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.73/1.50      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10908,plain,
% 7.73/1.50      ( k1_xboole_0 = X0
% 7.73/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X3,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X4,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.73/1.50      | r1_tarski(k3_enumset1(X1,X5,X4,X3,X2),X0) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_10901,c_2375]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3,plain,
% 7.73/1.50      ( k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2,plain,
% 7.73/1.50      ( ~ r1_tarski(X0,X1)
% 7.73/1.50      | ~ r1_tarski(X2,X1)
% 7.73/1.50      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2379,plain,
% 7.73/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.73/1.50      | r1_tarski(X2,X1) != iProver_top
% 7.73/1.50      | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_4896,plain,
% 7.73/1.50      ( r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),X5) != iProver_top
% 7.73/1.50      | r1_tarski(k2_tarski(X6,X7),X5) != iProver_top
% 7.73/1.50      | r1_tarski(k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X6,X7)),X5) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3,c_2379]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_6,plain,
% 7.73/1.50      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2376,plain,
% 7.73/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.73/1.50      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_13,plain,
% 7.73/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1,plain,
% 7.73/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_226,plain,
% 7.73/1.50      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_13,c_1]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_227,plain,
% 7.73/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_226]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2343,plain,
% 7.73/1.50      ( m1_subset_1(X0,X1) = iProver_top
% 7.73/1.50      | r2_hidden(X0,X1) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3076,plain,
% 7.73/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.73/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_2376,c_2343]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_32,negated_conjecture,
% 7.73/1.50      ( ~ m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2351,plain,
% 7.73/1.50      ( m1_subset_1(k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK7,sK8,sK9,sK10,sK11)),k1_zfmisc_1(sK4)) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_8110,plain,
% 7.73/1.50      ( r1_tarski(k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK7,sK8,sK9,sK10,sK11)),sK4) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_3076,c_2351]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11418,plain,
% 7.73/1.50      ( r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) != iProver_top
% 7.73/1.50      | r1_tarski(k2_tarski(sK10,sK11),sK4) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_4896,c_8110]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_34,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK11,sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3224,plain,
% 7.73/1.50      ( r2_hidden(sK11,sK4) | v1_xboole_0(sK4) ),
% 7.73/1.50      inference(resolution,[status(thm)],[c_14,c_34]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_33,negated_conjecture,
% 7.73/1.50      ( k1_xboole_0 != sK4 ),
% 7.73/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_50,plain,
% 7.73/1.50      ( m1_subset_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
% 7.73/1.50      | ~ m1_subset_1(sK4,sK4)
% 7.73/1.50      | k1_xboole_0 = sK4 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_31]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11,plain,
% 7.73/1.50      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_90,plain,
% 7.73/1.50      ( m1_subset_1(sK4,sK4) | ~ v1_xboole_0(sK4) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_116,plain,
% 7.73/1.50      ( ~ r2_hidden(sK4,sK4) | ~ v1_xboole_0(sK4) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_25,plain,
% 7.73/1.50      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X4,X5) ),
% 7.73/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_28,plain,
% 7.73/1.50      ( sP0(X0,X1,X2,X3,X4,k3_enumset1(X4,X3,X2,X1,X0)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1220,plain,
% 7.73/1.50      ( r2_hidden(X0,X1)
% 7.73/1.50      | X2 != X3
% 7.73/1.50      | X4 != X0
% 7.73/1.50      | X5 != X6
% 7.73/1.50      | X7 != X8
% 7.73/1.50      | X9 != X10
% 7.73/1.50      | k3_enumset1(X4,X5,X7,X9,X2) != X1 ),
% 7.73/1.50      inference(resolution_lifted,[status(thm)],[c_25,c_28]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1221,plain,
% 7.73/1.50      ( r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
% 7.73/1.50      inference(unflattening,[status(thm)],[c_1220]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1223,plain,
% 7.73/1.50      ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1221]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_30,plain,
% 7.73/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.73/1.50      | ~ r2_hidden(X2,X0)
% 7.73/1.50      | r2_hidden(X2,X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2736,plain,
% 7.73/1.50      ( ~ m1_subset_1(k3_enumset1(X0,X1,X2,X3,X4),k1_zfmisc_1(X5))
% 7.73/1.50      | r2_hidden(X4,X5)
% 7.73/1.50      | ~ r2_hidden(X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_30]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2738,plain,
% 7.73/1.50      ( ~ m1_subset_1(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(sK4))
% 7.73/1.50      | ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 7.73/1.50      | r2_hidden(sK4,sK4) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_2736]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2879,plain,
% 7.73/1.50      ( ~ m1_subset_1(sK11,sK4)
% 7.73/1.50      | r2_hidden(sK11,sK4)
% 7.73/1.50      | v1_xboole_0(sK4) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3239,plain,
% 7.73/1.50      ( r2_hidden(sK11,sK4) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_3224,c_34,c_33,c_50,c_90,c_116,c_1223,c_2738,c_2879]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3241,plain,
% 7.73/1.50      ( r2_hidden(sK11,sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3239]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_35,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK10,sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3226,plain,
% 7.73/1.50      ( r2_hidden(sK10,sK4) | v1_xboole_0(sK4) ),
% 7.73/1.50      inference(resolution,[status(thm)],[c_14,c_35]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2882,plain,
% 7.73/1.50      ( ~ m1_subset_1(sK10,sK4)
% 7.73/1.50      | r2_hidden(sK10,sK4)
% 7.73/1.50      | v1_xboole_0(sK4) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3386,plain,
% 7.73/1.50      ( r2_hidden(sK10,sK4) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_3226,c_35,c_33,c_50,c_90,c_116,c_1223,c_2738,c_2882]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3388,plain,
% 7.73/1.50      ( r2_hidden(sK10,sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_3386]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_8,plain,
% 7.73/1.50      ( r1_tarski(k2_tarski(X0,X1),X2)
% 7.73/1.50      | ~ r2_hidden(X0,X2)
% 7.73/1.50      | ~ r2_hidden(X1,X2) ),
% 7.73/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_3533,plain,
% 7.73/1.50      ( r1_tarski(k2_tarski(X0,sK11),sK4)
% 7.73/1.50      | ~ r2_hidden(X0,sK4)
% 7.73/1.50      | ~ r2_hidden(sK11,sK4) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_7263,plain,
% 7.73/1.50      ( r1_tarski(k2_tarski(sK10,sK11),sK4)
% 7.73/1.50      | ~ r2_hidden(sK11,sK4)
% 7.73/1.50      | ~ r2_hidden(sK10,sK4) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_3533]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_7264,plain,
% 7.73/1.50      ( r1_tarski(k2_tarski(sK10,sK11),sK4) = iProver_top
% 7.73/1.50      | r2_hidden(sK11,sK4) != iProver_top
% 7.73/1.50      | r2_hidden(sK10,sK4) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_7263]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_15900,plain,
% 7.73/1.50      ( r1_tarski(k3_enumset1(sK5,sK6,sK7,sK8,sK9),sK4) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_11418,c_3241,c_3388,c_7264]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_25818,plain,
% 7.73/1.50      ( sK4 = k1_xboole_0
% 7.73/1.50      | m1_subset_1(sK9,sK4) != iProver_top
% 7.73/1.50      | m1_subset_1(sK8,sK4) != iProver_top
% 7.73/1.50      | m1_subset_1(sK7,sK4) != iProver_top
% 7.73/1.50      | m1_subset_1(sK6,sK4) != iProver_top
% 7.73/1.50      | m1_subset_1(sK5,sK4) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_10908,c_15900]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1441,plain,( X0 = X0 ),theory(equality) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2650,plain,
% 7.73/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1441]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1442,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2519,plain,
% 7.73/1.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1442]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_2649,plain,
% 7.73/1.50      ( sK4 != k1_xboole_0
% 7.73/1.50      | k1_xboole_0 = sK4
% 7.73/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_2519]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_36,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK9,sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_45,plain,
% 7.73/1.50      ( m1_subset_1(sK9,sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_37,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK8,sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_44,plain,
% 7.73/1.50      ( m1_subset_1(sK8,sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_38,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK7,sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_43,plain,
% 7.73/1.50      ( m1_subset_1(sK7,sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_39,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK6,sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_42,plain,
% 7.73/1.50      ( m1_subset_1(sK6,sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_40,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK5,sK4) ),
% 7.73/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_41,plain,
% 7.73/1.50      ( m1_subset_1(sK5,sK4) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(contradiction,plain,
% 7.73/1.50      ( $false ),
% 7.73/1.50      inference(minisat,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_25818,c_2650,c_2649,c_33,c_45,c_44,c_43,c_42,c_41]) ).
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  ------                               Statistics
% 7.73/1.50  
% 7.73/1.50  ------ Selected
% 7.73/1.50  
% 7.73/1.50  total_time:                             0.772
% 7.73/1.50  
%------------------------------------------------------------------------------
