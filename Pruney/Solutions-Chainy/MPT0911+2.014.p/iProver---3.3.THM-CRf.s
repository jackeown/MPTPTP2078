%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:03 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  171 (1549 expanded)
%              Number of clauses        :   89 ( 468 expanded)
%              Number of leaves         :   22 ( 346 expanded)
%              Depth                    :   17
%              Number of atoms          :  539 (8121 expanded)
%              Number of equality atoms :  351 (5101 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f30,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k7_mcart_1(sK8,sK9,sK10,sK12) != sK11
      & k1_xboole_0 != sK10
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK11 = X7
                  | k3_mcart_1(X5,X6,X7) != sK12
                  | ~ m1_subset_1(X7,sK10) )
              | ~ m1_subset_1(X6,sK9) )
          | ~ m1_subset_1(X5,sK8) )
      & m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( k7_mcart_1(sK8,sK9,sK10,sK12) != sK11
    & k1_xboole_0 != sK10
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK11 = X7
                | k3_mcart_1(X5,X6,X7) != sK12
                | ~ m1_subset_1(X7,sK10) )
            | ~ m1_subset_1(X6,sK9) )
        | ~ m1_subset_1(X5,sK8) )
    & m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12])],[f31,f47])).

fof(f82,plain,(
    m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,(
    m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) ),
    inference(definition_unfolding,[],[f82,f67])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK6(X0),sK7(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK6(X0),sK7(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f22,f41])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK6(X0),sK7(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f36,f39,f38,f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f43])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f62])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f45])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f73,f67])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f15,axiom,(
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

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f78,f67])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f74,f67])).

fof(f109,plain,(
    ! [X2,X1] : k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) = k1_xboole_0 ),
    inference(equality_resolution,[],[f93])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f68,f67])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f77,f67])).

fof(f83,plain,(
    ! [X6,X7,X5] :
      ( sK11 = X7
      | k3_mcart_1(X5,X6,X7) != sK12
      | ~ m1_subset_1(X7,sK10)
      | ~ m1_subset_1(X6,sK9)
      | ~ m1_subset_1(X5,sK8) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f98,plain,(
    ! [X6,X7,X5] :
      ( sK11 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK12
      | ~ m1_subset_1(X7,sK10)
      | ~ m1_subset_1(X6,sK9)
      | ~ m1_subset_1(X5,sK8) ) ),
    inference(definition_unfolding,[],[f83,f66])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f79,f67])).

fof(f87,plain,(
    k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f70,f67])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_701,plain,
    ( m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_711,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2170,plain,
    ( r2_hidden(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_711])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_706,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2466,plain,
    ( r2_hidden(k1_mcart_1(sK12),k2_zfmisc_1(sK8,sK9)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2170,c_706])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK6(X0),sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_713,plain,
    ( k4_tarski(sK6(X0),sK7(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2576,plain,
    ( k4_tarski(sK6(k1_mcart_1(sK12)),sK7(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2466,c_713])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_718,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_712,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1380,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_712])).

cnf(c_5977,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_1380])).

cnf(c_13,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_6001,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5977,c_13])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_724,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6174,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6001,c_724])).

cnf(c_6668,plain,
    ( k4_tarski(sK6(k1_mcart_1(sK12)),sK7(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
    | k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2576,c_6174])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_25,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_954,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,sK9),X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1203,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_1807,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_9850,plain,
    ( k4_tarski(sK6(k1_mcart_1(sK12)),sK7(k1_mcart_1(sK12))) = k1_mcart_1(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6668,c_34,c_33,c_32,c_1807])).

cnf(c_2464,plain,
    ( k4_tarski(sK6(sK12),sK7(sK12)) = sK12
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2170,c_713])).

cnf(c_6672,plain,
    ( k4_tarski(sK6(sK12),sK7(sK12)) = sK12
    | k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2464,c_6174])).

cnf(c_7033,plain,
    ( k4_tarski(sK6(sK12),sK7(sK12)) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6672,c_34,c_33,c_32,c_1807])).

cnf(c_30,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7037,plain,
    ( k1_mcart_1(sK12) = sK6(sK12) ),
    inference(superposition,[status(thm)],[c_7033,c_30])).

cnf(c_9852,plain,
    ( k4_tarski(sK6(sK6(sK12)),sK7(sK6(sK12))) = sK6(sK12) ),
    inference(light_normalisation,[status(thm)],[c_9850,c_7037])).

cnf(c_29,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9857,plain,
    ( k2_mcart_1(sK6(sK12)) = sK7(sK6(sK12)) ),
    inference(superposition,[status(thm)],[c_9852,c_29])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_709,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3868,plain,
    ( m1_subset_1(k6_mcart_1(sK8,sK9,sK10,sK12),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_709])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_704,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1984,plain,
    ( k6_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(k1_mcart_1(sK12))
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_701,c_704])).

cnf(c_52,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_24,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_53,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_302,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_958,plain,
    ( sK10 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_959,plain,
    ( sK10 != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_960,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_961,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_962,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_963,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_2563,plain,
    ( k6_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(k1_mcart_1(sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1984,c_34,c_33,c_32,c_52,c_53,c_959,c_961,c_963])).

cnf(c_3897,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3868,c_2563])).

cnf(c_7178,plain,
    ( m1_subset_1(k2_mcart_1(sK6(sK12)),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7037,c_3897])).

cnf(c_10057,plain,
    ( m1_subset_1(sK7(sK6(sK12)),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9857,c_7178])).

cnf(c_9856,plain,
    ( k1_mcart_1(sK6(sK12)) = sK6(sK6(sK12)) ),
    inference(superposition,[status(thm)],[c_9852,c_30])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_710,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4090,plain,
    ( m1_subset_1(k5_mcart_1(sK8,sK9,sK10,sK12),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_710])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_703,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1050,plain,
    ( k5_mcart_1(sK8,sK9,sK10,sK12) = k1_mcart_1(k1_mcart_1(sK12))
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_701,c_703])).

cnf(c_1268,plain,
    ( k5_mcart_1(sK8,sK9,sK10,sK12) = k1_mcart_1(k1_mcart_1(sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1050,c_34,c_33,c_32,c_52,c_53,c_959,c_961,c_963])).

cnf(c_4129,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4090,c_1268])).

cnf(c_7177,plain,
    ( m1_subset_1(k1_mcart_1(sK6(sK12)),sK8) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7037,c_4129])).

cnf(c_9994,plain,
    ( m1_subset_1(sK6(sK6(sK12)),sK8) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9856,c_7177])).

cnf(c_35,negated_conjecture,
    ( ~ m1_subset_1(X0,sK10)
    | ~ m1_subset_1(X1,sK9)
    | ~ m1_subset_1(X2,sK8)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK12
    | sK11 = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_702,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK12
    | sK11 = X2
    | m1_subset_1(X2,sK10) != iProver_top
    | m1_subset_1(X1,sK9) != iProver_top
    | m1_subset_1(X0,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_9858,plain,
    ( k4_tarski(sK6(sK12),X0) != sK12
    | sK11 = X0
    | m1_subset_1(X0,sK10) != iProver_top
    | m1_subset_1(sK7(sK6(sK12)),sK9) != iProver_top
    | m1_subset_1(sK6(sK6(sK12)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9852,c_702])).

cnf(c_9902,plain,
    ( sK7(sK12) = sK11
    | m1_subset_1(sK7(sK6(sK12)),sK9) != iProver_top
    | m1_subset_1(sK7(sK12),sK10) != iProver_top
    | m1_subset_1(sK6(sK6(sK12)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7033,c_9858])).

cnf(c_7038,plain,
    ( k2_mcart_1(sK12) = sK7(sK12) ),
    inference(superposition,[status(thm)],[c_7033,c_29])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_705,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3402,plain,
    ( k7_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(sK12)
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_701,c_705])).

cnf(c_3813,plain,
    ( k7_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3402,c_34,c_33,c_32,c_52,c_53,c_959,c_961,c_963])).

cnf(c_31,negated_conjecture,
    ( k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3817,plain,
    ( k2_mcart_1(sK12) != sK11 ),
    inference(demodulation,[status(thm)],[c_3813,c_31])).

cnf(c_7522,plain,
    ( sK7(sK12) != sK11 ),
    inference(demodulation,[status(thm)],[c_7038,c_3817])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_708,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3627,plain,
    ( m1_subset_1(k7_mcart_1(sK8,sK9,sK10,sK12),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_708])).

cnf(c_3816,plain,
    ( m1_subset_1(k2_mcart_1(sK12),sK10) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3813,c_3627])).

cnf(c_7521,plain,
    ( m1_subset_1(sK7(sK12),sK10) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7038,c_3816])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10057,c_9994,c_9902,c_7522,c_7521])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:15:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.47/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.00  
% 3.47/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/1.00  
% 3.47/1.00  ------  iProver source info
% 3.47/1.00  
% 3.47/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.47/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/1.00  git: non_committed_changes: false
% 3.47/1.00  git: last_make_outside_of_git: false
% 3.47/1.00  
% 3.47/1.00  ------ 
% 3.47/1.00  
% 3.47/1.00  ------ Input Options
% 3.47/1.00  
% 3.47/1.00  --out_options                           all
% 3.47/1.00  --tptp_safe_out                         true
% 3.47/1.00  --problem_path                          ""
% 3.47/1.00  --include_path                          ""
% 3.47/1.00  --clausifier                            res/vclausify_rel
% 3.47/1.00  --clausifier_options                    --mode clausify
% 3.47/1.00  --stdin                                 false
% 3.47/1.00  --stats_out                             all
% 3.47/1.00  
% 3.47/1.00  ------ General Options
% 3.47/1.00  
% 3.47/1.00  --fof                                   false
% 3.47/1.00  --time_out_real                         305.
% 3.47/1.00  --time_out_virtual                      -1.
% 3.47/1.00  --symbol_type_check                     false
% 3.47/1.00  --clausify_out                          false
% 3.47/1.00  --sig_cnt_out                           false
% 3.47/1.00  --trig_cnt_out                          false
% 3.47/1.00  --trig_cnt_out_tolerance                1.
% 3.47/1.00  --trig_cnt_out_sk_spl                   false
% 3.47/1.00  --abstr_cl_out                          false
% 3.47/1.00  
% 3.47/1.00  ------ Global Options
% 3.47/1.00  
% 3.47/1.00  --schedule                              default
% 3.47/1.00  --add_important_lit                     false
% 3.47/1.00  --prop_solver_per_cl                    1000
% 3.47/1.00  --min_unsat_core                        false
% 3.47/1.00  --soft_assumptions                      false
% 3.47/1.00  --soft_lemma_size                       3
% 3.47/1.00  --prop_impl_unit_size                   0
% 3.47/1.00  --prop_impl_unit                        []
% 3.47/1.00  --share_sel_clauses                     true
% 3.47/1.00  --reset_solvers                         false
% 3.47/1.00  --bc_imp_inh                            [conj_cone]
% 3.47/1.00  --conj_cone_tolerance                   3.
% 3.47/1.00  --extra_neg_conj                        none
% 3.47/1.00  --large_theory_mode                     true
% 3.47/1.00  --prolific_symb_bound                   200
% 3.47/1.00  --lt_threshold                          2000
% 3.47/1.00  --clause_weak_htbl                      true
% 3.47/1.00  --gc_record_bc_elim                     false
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing Options
% 3.47/1.00  
% 3.47/1.00  --preprocessing_flag                    true
% 3.47/1.00  --time_out_prep_mult                    0.1
% 3.47/1.00  --splitting_mode                        input
% 3.47/1.00  --splitting_grd                         true
% 3.47/1.00  --splitting_cvd                         false
% 3.47/1.00  --splitting_cvd_svl                     false
% 3.47/1.00  --splitting_nvd                         32
% 3.47/1.00  --sub_typing                            true
% 3.47/1.00  --prep_gs_sim                           true
% 3.47/1.00  --prep_unflatten                        true
% 3.47/1.00  --prep_res_sim                          true
% 3.47/1.00  --prep_upred                            true
% 3.47/1.00  --prep_sem_filter                       exhaustive
% 3.47/1.00  --prep_sem_filter_out                   false
% 3.47/1.00  --pred_elim                             true
% 3.47/1.00  --res_sim_input                         true
% 3.47/1.00  --eq_ax_congr_red                       true
% 3.47/1.00  --pure_diseq_elim                       true
% 3.47/1.00  --brand_transform                       false
% 3.47/1.00  --non_eq_to_eq                          false
% 3.47/1.00  --prep_def_merge                        true
% 3.47/1.00  --prep_def_merge_prop_impl              false
% 3.47/1.00  --prep_def_merge_mbd                    true
% 3.47/1.00  --prep_def_merge_tr_red                 false
% 3.47/1.00  --prep_def_merge_tr_cl                  false
% 3.47/1.00  --smt_preprocessing                     true
% 3.47/1.00  --smt_ac_axioms                         fast
% 3.47/1.00  --preprocessed_out                      false
% 3.47/1.00  --preprocessed_stats                    false
% 3.47/1.00  
% 3.47/1.00  ------ Abstraction refinement Options
% 3.47/1.00  
% 3.47/1.00  --abstr_ref                             []
% 3.47/1.00  --abstr_ref_prep                        false
% 3.47/1.00  --abstr_ref_until_sat                   false
% 3.47/1.00  --abstr_ref_sig_restrict                funpre
% 3.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/1.00  --abstr_ref_under                       []
% 3.47/1.00  
% 3.47/1.00  ------ SAT Options
% 3.47/1.00  
% 3.47/1.00  --sat_mode                              false
% 3.47/1.00  --sat_fm_restart_options                ""
% 3.47/1.00  --sat_gr_def                            false
% 3.47/1.00  --sat_epr_types                         true
% 3.47/1.00  --sat_non_cyclic_types                  false
% 3.47/1.00  --sat_finite_models                     false
% 3.47/1.00  --sat_fm_lemmas                         false
% 3.47/1.00  --sat_fm_prep                           false
% 3.47/1.00  --sat_fm_uc_incr                        true
% 3.47/1.00  --sat_out_model                         small
% 3.47/1.00  --sat_out_clauses                       false
% 3.47/1.00  
% 3.47/1.00  ------ QBF Options
% 3.47/1.00  
% 3.47/1.00  --qbf_mode                              false
% 3.47/1.00  --qbf_elim_univ                         false
% 3.47/1.00  --qbf_dom_inst                          none
% 3.47/1.00  --qbf_dom_pre_inst                      false
% 3.47/1.00  --qbf_sk_in                             false
% 3.47/1.00  --qbf_pred_elim                         true
% 3.47/1.00  --qbf_split                             512
% 3.47/1.00  
% 3.47/1.00  ------ BMC1 Options
% 3.47/1.00  
% 3.47/1.00  --bmc1_incremental                      false
% 3.47/1.00  --bmc1_axioms                           reachable_all
% 3.47/1.00  --bmc1_min_bound                        0
% 3.47/1.00  --bmc1_max_bound                        -1
% 3.47/1.00  --bmc1_max_bound_default                -1
% 3.47/1.00  --bmc1_symbol_reachability              true
% 3.47/1.00  --bmc1_property_lemmas                  false
% 3.47/1.00  --bmc1_k_induction                      false
% 3.47/1.00  --bmc1_non_equiv_states                 false
% 3.47/1.00  --bmc1_deadlock                         false
% 3.47/1.00  --bmc1_ucm                              false
% 3.47/1.00  --bmc1_add_unsat_core                   none
% 3.47/1.00  --bmc1_unsat_core_children              false
% 3.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/1.00  --bmc1_out_stat                         full
% 3.47/1.00  --bmc1_ground_init                      false
% 3.47/1.00  --bmc1_pre_inst_next_state              false
% 3.47/1.00  --bmc1_pre_inst_state                   false
% 3.47/1.00  --bmc1_pre_inst_reach_state             false
% 3.47/1.00  --bmc1_out_unsat_core                   false
% 3.47/1.00  --bmc1_aig_witness_out                  false
% 3.47/1.00  --bmc1_verbose                          false
% 3.47/1.00  --bmc1_dump_clauses_tptp                false
% 3.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.47/1.00  --bmc1_dump_file                        -
% 3.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.47/1.00  --bmc1_ucm_extend_mode                  1
% 3.47/1.00  --bmc1_ucm_init_mode                    2
% 3.47/1.00  --bmc1_ucm_cone_mode                    none
% 3.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.47/1.00  --bmc1_ucm_relax_model                  4
% 3.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/1.00  --bmc1_ucm_layered_model                none
% 3.47/1.00  --bmc1_ucm_max_lemma_size               10
% 3.47/1.00  
% 3.47/1.00  ------ AIG Options
% 3.47/1.00  
% 3.47/1.00  --aig_mode                              false
% 3.47/1.00  
% 3.47/1.00  ------ Instantiation Options
% 3.47/1.00  
% 3.47/1.00  --instantiation_flag                    true
% 3.47/1.00  --inst_sos_flag                         false
% 3.47/1.00  --inst_sos_phase                        true
% 3.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/1.00  --inst_lit_sel_side                     num_symb
% 3.47/1.00  --inst_solver_per_active                1400
% 3.47/1.00  --inst_solver_calls_frac                1.
% 3.47/1.00  --inst_passive_queue_type               priority_queues
% 3.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/1.00  --inst_passive_queues_freq              [25;2]
% 3.47/1.00  --inst_dismatching                      true
% 3.47/1.00  --inst_eager_unprocessed_to_passive     true
% 3.47/1.00  --inst_prop_sim_given                   true
% 3.47/1.00  --inst_prop_sim_new                     false
% 3.47/1.00  --inst_subs_new                         false
% 3.47/1.00  --inst_eq_res_simp                      false
% 3.47/1.00  --inst_subs_given                       false
% 3.47/1.00  --inst_orphan_elimination               true
% 3.47/1.00  --inst_learning_loop_flag               true
% 3.47/1.00  --inst_learning_start                   3000
% 3.47/1.00  --inst_learning_factor                  2
% 3.47/1.00  --inst_start_prop_sim_after_learn       3
% 3.47/1.00  --inst_sel_renew                        solver
% 3.47/1.00  --inst_lit_activity_flag                true
% 3.47/1.00  --inst_restr_to_given                   false
% 3.47/1.00  --inst_activity_threshold               500
% 3.47/1.00  --inst_out_proof                        true
% 3.47/1.00  
% 3.47/1.00  ------ Resolution Options
% 3.47/1.00  
% 3.47/1.00  --resolution_flag                       true
% 3.47/1.00  --res_lit_sel                           adaptive
% 3.47/1.00  --res_lit_sel_side                      none
% 3.47/1.00  --res_ordering                          kbo
% 3.47/1.00  --res_to_prop_solver                    active
% 3.47/1.00  --res_prop_simpl_new                    false
% 3.47/1.00  --res_prop_simpl_given                  true
% 3.47/1.00  --res_passive_queue_type                priority_queues
% 3.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/1.00  --res_passive_queues_freq               [15;5]
% 3.47/1.00  --res_forward_subs                      full
% 3.47/1.00  --res_backward_subs                     full
% 3.47/1.00  --res_forward_subs_resolution           true
% 3.47/1.00  --res_backward_subs_resolution          true
% 3.47/1.00  --res_orphan_elimination                true
% 3.47/1.00  --res_time_limit                        2.
% 3.47/1.00  --res_out_proof                         true
% 3.47/1.00  
% 3.47/1.00  ------ Superposition Options
% 3.47/1.00  
% 3.47/1.00  --superposition_flag                    true
% 3.47/1.00  --sup_passive_queue_type                priority_queues
% 3.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.47/1.00  --demod_completeness_check              fast
% 3.47/1.00  --demod_use_ground                      true
% 3.47/1.00  --sup_to_prop_solver                    passive
% 3.47/1.00  --sup_prop_simpl_new                    true
% 3.47/1.00  --sup_prop_simpl_given                  true
% 3.47/1.00  --sup_fun_splitting                     false
% 3.47/1.00  --sup_smt_interval                      50000
% 3.47/1.00  
% 3.47/1.00  ------ Superposition Simplification Setup
% 3.47/1.00  
% 3.47/1.00  --sup_indices_passive                   []
% 3.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_full_bw                           [BwDemod]
% 3.47/1.00  --sup_immed_triv                        [TrivRules]
% 3.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_immed_bw_main                     []
% 3.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/1.00  
% 3.47/1.00  ------ Combination Options
% 3.47/1.00  
% 3.47/1.00  --comb_res_mult                         3
% 3.47/1.00  --comb_sup_mult                         2
% 3.47/1.00  --comb_inst_mult                        10
% 3.47/1.00  
% 3.47/1.00  ------ Debug Options
% 3.47/1.00  
% 3.47/1.00  --dbg_backtrace                         false
% 3.47/1.00  --dbg_dump_prop_clauses                 false
% 3.47/1.00  --dbg_dump_prop_clauses_file            -
% 3.47/1.00  --dbg_out_stat                          false
% 3.47/1.00  ------ Parsing...
% 3.47/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/1.00  ------ Proving...
% 3.47/1.00  ------ Problem Properties 
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  clauses                                 37
% 3.47/1.00  conjectures                             6
% 3.47/1.00  EPR                                     5
% 3.47/1.00  Horn                                    27
% 3.47/1.00  unary                                   13
% 3.47/1.00  binary                                  10
% 3.47/1.00  lits                                    86
% 3.47/1.00  lits eq                                 42
% 3.47/1.00  fd_pure                                 0
% 3.47/1.00  fd_pseudo                               0
% 3.47/1.00  fd_cond                                 6
% 3.47/1.00  fd_pseudo_cond                          6
% 3.47/1.00  AC symbols                              0
% 3.47/1.00  
% 3.47/1.00  ------ Schedule dynamic 5 is on 
% 3.47/1.00  
% 3.47/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  ------ 
% 3.47/1.00  Current options:
% 3.47/1.00  ------ 
% 3.47/1.00  
% 3.47/1.00  ------ Input Options
% 3.47/1.00  
% 3.47/1.00  --out_options                           all
% 3.47/1.00  --tptp_safe_out                         true
% 3.47/1.00  --problem_path                          ""
% 3.47/1.00  --include_path                          ""
% 3.47/1.00  --clausifier                            res/vclausify_rel
% 3.47/1.00  --clausifier_options                    --mode clausify
% 3.47/1.00  --stdin                                 false
% 3.47/1.00  --stats_out                             all
% 3.47/1.00  
% 3.47/1.00  ------ General Options
% 3.47/1.00  
% 3.47/1.00  --fof                                   false
% 3.47/1.00  --time_out_real                         305.
% 3.47/1.00  --time_out_virtual                      -1.
% 3.47/1.00  --symbol_type_check                     false
% 3.47/1.00  --clausify_out                          false
% 3.47/1.00  --sig_cnt_out                           false
% 3.47/1.00  --trig_cnt_out                          false
% 3.47/1.00  --trig_cnt_out_tolerance                1.
% 3.47/1.00  --trig_cnt_out_sk_spl                   false
% 3.47/1.00  --abstr_cl_out                          false
% 3.47/1.00  
% 3.47/1.00  ------ Global Options
% 3.47/1.00  
% 3.47/1.00  --schedule                              default
% 3.47/1.00  --add_important_lit                     false
% 3.47/1.00  --prop_solver_per_cl                    1000
% 3.47/1.00  --min_unsat_core                        false
% 3.47/1.00  --soft_assumptions                      false
% 3.47/1.00  --soft_lemma_size                       3
% 3.47/1.00  --prop_impl_unit_size                   0
% 3.47/1.00  --prop_impl_unit                        []
% 3.47/1.00  --share_sel_clauses                     true
% 3.47/1.00  --reset_solvers                         false
% 3.47/1.00  --bc_imp_inh                            [conj_cone]
% 3.47/1.00  --conj_cone_tolerance                   3.
% 3.47/1.00  --extra_neg_conj                        none
% 3.47/1.00  --large_theory_mode                     true
% 3.47/1.00  --prolific_symb_bound                   200
% 3.47/1.00  --lt_threshold                          2000
% 3.47/1.00  --clause_weak_htbl                      true
% 3.47/1.00  --gc_record_bc_elim                     false
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing Options
% 3.47/1.00  
% 3.47/1.00  --preprocessing_flag                    true
% 3.47/1.00  --time_out_prep_mult                    0.1
% 3.47/1.00  --splitting_mode                        input
% 3.47/1.00  --splitting_grd                         true
% 3.47/1.00  --splitting_cvd                         false
% 3.47/1.00  --splitting_cvd_svl                     false
% 3.47/1.00  --splitting_nvd                         32
% 3.47/1.00  --sub_typing                            true
% 3.47/1.00  --prep_gs_sim                           true
% 3.47/1.00  --prep_unflatten                        true
% 3.47/1.00  --prep_res_sim                          true
% 3.47/1.00  --prep_upred                            true
% 3.47/1.00  --prep_sem_filter                       exhaustive
% 3.47/1.00  --prep_sem_filter_out                   false
% 3.47/1.00  --pred_elim                             true
% 3.47/1.00  --res_sim_input                         true
% 3.47/1.00  --eq_ax_congr_red                       true
% 3.47/1.00  --pure_diseq_elim                       true
% 3.47/1.00  --brand_transform                       false
% 3.47/1.00  --non_eq_to_eq                          false
% 3.47/1.00  --prep_def_merge                        true
% 3.47/1.00  --prep_def_merge_prop_impl              false
% 3.47/1.00  --prep_def_merge_mbd                    true
% 3.47/1.00  --prep_def_merge_tr_red                 false
% 3.47/1.00  --prep_def_merge_tr_cl                  false
% 3.47/1.00  --smt_preprocessing                     true
% 3.47/1.00  --smt_ac_axioms                         fast
% 3.47/1.00  --preprocessed_out                      false
% 3.47/1.00  --preprocessed_stats                    false
% 3.47/1.00  
% 3.47/1.00  ------ Abstraction refinement Options
% 3.47/1.00  
% 3.47/1.00  --abstr_ref                             []
% 3.47/1.00  --abstr_ref_prep                        false
% 3.47/1.00  --abstr_ref_until_sat                   false
% 3.47/1.00  --abstr_ref_sig_restrict                funpre
% 3.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/1.00  --abstr_ref_under                       []
% 3.47/1.00  
% 3.47/1.00  ------ SAT Options
% 3.47/1.00  
% 3.47/1.00  --sat_mode                              false
% 3.47/1.00  --sat_fm_restart_options                ""
% 3.47/1.00  --sat_gr_def                            false
% 3.47/1.00  --sat_epr_types                         true
% 3.47/1.00  --sat_non_cyclic_types                  false
% 3.47/1.00  --sat_finite_models                     false
% 3.47/1.00  --sat_fm_lemmas                         false
% 3.47/1.00  --sat_fm_prep                           false
% 3.47/1.00  --sat_fm_uc_incr                        true
% 3.47/1.00  --sat_out_model                         small
% 3.47/1.00  --sat_out_clauses                       false
% 3.47/1.00  
% 3.47/1.00  ------ QBF Options
% 3.47/1.00  
% 3.47/1.00  --qbf_mode                              false
% 3.47/1.00  --qbf_elim_univ                         false
% 3.47/1.00  --qbf_dom_inst                          none
% 3.47/1.00  --qbf_dom_pre_inst                      false
% 3.47/1.00  --qbf_sk_in                             false
% 3.47/1.00  --qbf_pred_elim                         true
% 3.47/1.00  --qbf_split                             512
% 3.47/1.00  
% 3.47/1.00  ------ BMC1 Options
% 3.47/1.00  
% 3.47/1.00  --bmc1_incremental                      false
% 3.47/1.00  --bmc1_axioms                           reachable_all
% 3.47/1.00  --bmc1_min_bound                        0
% 3.47/1.00  --bmc1_max_bound                        -1
% 3.47/1.00  --bmc1_max_bound_default                -1
% 3.47/1.00  --bmc1_symbol_reachability              true
% 3.47/1.00  --bmc1_property_lemmas                  false
% 3.47/1.00  --bmc1_k_induction                      false
% 3.47/1.00  --bmc1_non_equiv_states                 false
% 3.47/1.00  --bmc1_deadlock                         false
% 3.47/1.00  --bmc1_ucm                              false
% 3.47/1.00  --bmc1_add_unsat_core                   none
% 3.47/1.00  --bmc1_unsat_core_children              false
% 3.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/1.00  --bmc1_out_stat                         full
% 3.47/1.00  --bmc1_ground_init                      false
% 3.47/1.00  --bmc1_pre_inst_next_state              false
% 3.47/1.00  --bmc1_pre_inst_state                   false
% 3.47/1.00  --bmc1_pre_inst_reach_state             false
% 3.47/1.00  --bmc1_out_unsat_core                   false
% 3.47/1.00  --bmc1_aig_witness_out                  false
% 3.47/1.00  --bmc1_verbose                          false
% 3.47/1.00  --bmc1_dump_clauses_tptp                false
% 3.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.47/1.00  --bmc1_dump_file                        -
% 3.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.47/1.00  --bmc1_ucm_extend_mode                  1
% 3.47/1.00  --bmc1_ucm_init_mode                    2
% 3.47/1.00  --bmc1_ucm_cone_mode                    none
% 3.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.47/1.00  --bmc1_ucm_relax_model                  4
% 3.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/1.00  --bmc1_ucm_layered_model                none
% 3.47/1.00  --bmc1_ucm_max_lemma_size               10
% 3.47/1.00  
% 3.47/1.00  ------ AIG Options
% 3.47/1.00  
% 3.47/1.00  --aig_mode                              false
% 3.47/1.00  
% 3.47/1.00  ------ Instantiation Options
% 3.47/1.00  
% 3.47/1.00  --instantiation_flag                    true
% 3.47/1.00  --inst_sos_flag                         false
% 3.47/1.00  --inst_sos_phase                        true
% 3.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/1.00  --inst_lit_sel_side                     none
% 3.47/1.00  --inst_solver_per_active                1400
% 3.47/1.00  --inst_solver_calls_frac                1.
% 3.47/1.00  --inst_passive_queue_type               priority_queues
% 3.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/1.00  --inst_passive_queues_freq              [25;2]
% 3.47/1.00  --inst_dismatching                      true
% 3.47/1.00  --inst_eager_unprocessed_to_passive     true
% 3.47/1.00  --inst_prop_sim_given                   true
% 3.47/1.00  --inst_prop_sim_new                     false
% 3.47/1.00  --inst_subs_new                         false
% 3.47/1.00  --inst_eq_res_simp                      false
% 3.47/1.00  --inst_subs_given                       false
% 3.47/1.00  --inst_orphan_elimination               true
% 3.47/1.00  --inst_learning_loop_flag               true
% 3.47/1.00  --inst_learning_start                   3000
% 3.47/1.00  --inst_learning_factor                  2
% 3.47/1.00  --inst_start_prop_sim_after_learn       3
% 3.47/1.00  --inst_sel_renew                        solver
% 3.47/1.00  --inst_lit_activity_flag                true
% 3.47/1.00  --inst_restr_to_given                   false
% 3.47/1.00  --inst_activity_threshold               500
% 3.47/1.00  --inst_out_proof                        true
% 3.47/1.00  
% 3.47/1.00  ------ Resolution Options
% 3.47/1.00  
% 3.47/1.00  --resolution_flag                       false
% 3.47/1.00  --res_lit_sel                           adaptive
% 3.47/1.00  --res_lit_sel_side                      none
% 3.47/1.00  --res_ordering                          kbo
% 3.47/1.00  --res_to_prop_solver                    active
% 3.47/1.00  --res_prop_simpl_new                    false
% 3.47/1.00  --res_prop_simpl_given                  true
% 3.47/1.00  --res_passive_queue_type                priority_queues
% 3.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/1.00  --res_passive_queues_freq               [15;5]
% 3.47/1.00  --res_forward_subs                      full
% 3.47/1.00  --res_backward_subs                     full
% 3.47/1.00  --res_forward_subs_resolution           true
% 3.47/1.00  --res_backward_subs_resolution          true
% 3.47/1.00  --res_orphan_elimination                true
% 3.47/1.00  --res_time_limit                        2.
% 3.47/1.00  --res_out_proof                         true
% 3.47/1.00  
% 3.47/1.00  ------ Superposition Options
% 3.47/1.00  
% 3.47/1.00  --superposition_flag                    true
% 3.47/1.00  --sup_passive_queue_type                priority_queues
% 3.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.47/1.00  --demod_completeness_check              fast
% 3.47/1.00  --demod_use_ground                      true
% 3.47/1.00  --sup_to_prop_solver                    passive
% 3.47/1.00  --sup_prop_simpl_new                    true
% 3.47/1.00  --sup_prop_simpl_given                  true
% 3.47/1.00  --sup_fun_splitting                     false
% 3.47/1.00  --sup_smt_interval                      50000
% 3.47/1.00  
% 3.47/1.00  ------ Superposition Simplification Setup
% 3.47/1.00  
% 3.47/1.00  --sup_indices_passive                   []
% 3.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_full_bw                           [BwDemod]
% 3.47/1.00  --sup_immed_triv                        [TrivRules]
% 3.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_immed_bw_main                     []
% 3.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/1.00  
% 3.47/1.00  ------ Combination Options
% 3.47/1.00  
% 3.47/1.00  --comb_res_mult                         3
% 3.47/1.00  --comb_sup_mult                         2
% 3.47/1.00  --comb_inst_mult                        10
% 3.47/1.00  
% 3.47/1.00  ------ Debug Options
% 3.47/1.00  
% 3.47/1.00  --dbg_backtrace                         false
% 3.47/1.00  --dbg_dump_prop_clauses                 false
% 3.47/1.00  --dbg_dump_prop_clauses_file            -
% 3.47/1.00  --dbg_out_stat                          false
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  ------ Proving...
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  % SZS status Theorem for theBenchmark.p
% 3.47/1.00  
% 3.47/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/1.00  
% 3.47/1.00  fof(f17,conjecture,(
% 3.47/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f18,negated_conjecture,(
% 3.47/1.00    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.47/1.00    inference(negated_conjecture,[],[f17])).
% 3.47/1.00  
% 3.47/1.00  fof(f30,plain,(
% 3.47/1.00    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.47/1.00    inference(ennf_transformation,[],[f18])).
% 3.47/1.00  
% 3.47/1.00  fof(f31,plain,(
% 3.47/1.00    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.47/1.00    inference(flattening,[],[f30])).
% 3.47/1.00  
% 3.47/1.00  fof(f47,plain,(
% 3.47/1.00    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5] : (! [X6] : (! [X7] : (sK11 = X7 | k3_mcart_1(X5,X6,X7) != sK12 | ~m1_subset_1(X7,sK10)) | ~m1_subset_1(X6,sK9)) | ~m1_subset_1(X5,sK8)) & m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10)))),
% 3.47/1.00    introduced(choice_axiom,[])).
% 3.47/1.00  
% 3.47/1.00  fof(f48,plain,(
% 3.47/1.00    k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5] : (! [X6] : (! [X7] : (sK11 = X7 | k3_mcart_1(X5,X6,X7) != sK12 | ~m1_subset_1(X7,sK10)) | ~m1_subset_1(X6,sK9)) | ~m1_subset_1(X5,sK8)) & m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10))),
% 3.47/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12])],[f31,f47])).
% 3.47/1.00  
% 3.47/1.00  fof(f82,plain,(
% 3.47/1.00    m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10))),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f9,axiom,(
% 3.47/1.00    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f67,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f9])).
% 3.47/1.00  
% 3.47/1.00  fof(f99,plain,(
% 3.47/1.00    m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10))),
% 3.47/1.00    inference(definition_unfolding,[],[f82,f67])).
% 3.47/1.00  
% 3.47/1.00  fof(f7,axiom,(
% 3.47/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f23,plain,(
% 3.47/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.47/1.00    inference(ennf_transformation,[],[f7])).
% 3.47/1.00  
% 3.47/1.00  fof(f24,plain,(
% 3.47/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.47/1.00    inference(flattening,[],[f23])).
% 3.47/1.00  
% 3.47/1.00  fof(f65,plain,(
% 3.47/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f24])).
% 3.47/1.00  
% 3.47/1.00  fof(f13,axiom,(
% 3.47/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f28,plain,(
% 3.47/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.47/1.00    inference(ennf_transformation,[],[f13])).
% 3.47/1.00  
% 3.47/1.00  fof(f71,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f28])).
% 3.47/1.00  
% 3.47/1.00  fof(f4,axiom,(
% 3.47/1.00    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f22,plain,(
% 3.47/1.00    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.47/1.00    inference(ennf_transformation,[],[f4])).
% 3.47/1.00  
% 3.47/1.00  fof(f41,plain,(
% 3.47/1.00    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK6(X0),sK7(X0)) = X0)),
% 3.47/1.00    introduced(choice_axiom,[])).
% 3.47/1.00  
% 3.47/1.00  fof(f42,plain,(
% 3.47/1.00    ! [X0,X1,X2] : (k4_tarski(sK6(X0),sK7(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.47/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f22,f41])).
% 3.47/1.00  
% 3.47/1.00  fof(f60,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (k4_tarski(sK6(X0),sK7(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f42])).
% 3.47/1.00  
% 3.47/1.00  fof(f3,axiom,(
% 3.47/1.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f35,plain,(
% 3.47/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.47/1.00    inference(nnf_transformation,[],[f3])).
% 3.47/1.00  
% 3.47/1.00  fof(f36,plain,(
% 3.47/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.47/1.00    inference(rectify,[],[f35])).
% 3.47/1.00  
% 3.47/1.00  fof(f39,plain,(
% 3.47/1.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 3.47/1.00    introduced(choice_axiom,[])).
% 3.47/1.00  
% 3.47/1.00  fof(f38,plain,(
% 3.47/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 3.47/1.00    introduced(choice_axiom,[])).
% 3.47/1.00  
% 3.47/1.00  fof(f37,plain,(
% 3.47/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.47/1.00    introduced(choice_axiom,[])).
% 3.47/1.00  
% 3.47/1.00  fof(f40,plain,(
% 3.47/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.47/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f36,f39,f38,f37])).
% 3.47/1.00  
% 3.47/1.00  fof(f56,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f40])).
% 3.47/1.00  
% 3.47/1.00  fof(f5,axiom,(
% 3.47/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f43,plain,(
% 3.47/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.47/1.00    inference(nnf_transformation,[],[f5])).
% 3.47/1.00  
% 3.47/1.00  fof(f44,plain,(
% 3.47/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.47/1.00    inference(flattening,[],[f43])).
% 3.47/1.00  
% 3.47/1.00  fof(f63,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.47/1.00    inference(cnf_transformation,[],[f44])).
% 3.47/1.00  
% 3.47/1.00  fof(f105,plain,(
% 3.47/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.47/1.00    inference(equality_resolution,[],[f63])).
% 3.47/1.00  
% 3.47/1.00  fof(f6,axiom,(
% 3.47/1.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f64,plain,(
% 3.47/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f6])).
% 3.47/1.00  
% 3.47/1.00  fof(f62,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.47/1.00    inference(cnf_transformation,[],[f44])).
% 3.47/1.00  
% 3.47/1.00  fof(f106,plain,(
% 3.47/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.47/1.00    inference(equality_resolution,[],[f62])).
% 3.47/1.00  
% 3.47/1.00  fof(f1,axiom,(
% 3.47/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f19,plain,(
% 3.47/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.47/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.47/1.00  
% 3.47/1.00  fof(f20,plain,(
% 3.47/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.47/1.00    inference(ennf_transformation,[],[f19])).
% 3.47/1.00  
% 3.47/1.00  fof(f49,plain,(
% 3.47/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f20])).
% 3.47/1.00  
% 3.47/1.00  fof(f84,plain,(
% 3.47/1.00    k1_xboole_0 != sK8),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f85,plain,(
% 3.47/1.00    k1_xboole_0 != sK9),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f86,plain,(
% 3.47/1.00    k1_xboole_0 != sK10),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f14,axiom,(
% 3.47/1.00    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f45,plain,(
% 3.47/1.00    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.47/1.00    inference(nnf_transformation,[],[f14])).
% 3.47/1.00  
% 3.47/1.00  fof(f46,plain,(
% 3.47/1.00    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.47/1.00    inference(flattening,[],[f45])).
% 3.47/1.00  
% 3.47/1.00  fof(f73,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.47/1.00    inference(cnf_transformation,[],[f46])).
% 3.47/1.00  
% 3.47/1.00  fof(f94,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.47/1.00    inference(definition_unfolding,[],[f73,f67])).
% 3.47/1.00  
% 3.47/1.00  fof(f16,axiom,(
% 3.47/1.00    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f80,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.47/1.00    inference(cnf_transformation,[],[f16])).
% 3.47/1.00  
% 3.47/1.00  fof(f81,plain,(
% 3.47/1.00    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.47/1.00    inference(cnf_transformation,[],[f16])).
% 3.47/1.00  
% 3.47/1.00  fof(f11,axiom,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f26,plain,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.47/1.00    inference(ennf_transformation,[],[f11])).
% 3.47/1.00  
% 3.47/1.00  fof(f69,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f26])).
% 3.47/1.00  
% 3.47/1.00  fof(f89,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.47/1.00    inference(definition_unfolding,[],[f69,f67])).
% 3.47/1.00  
% 3.47/1.00  fof(f15,axiom,(
% 3.47/1.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f29,plain,(
% 3.47/1.00    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.47/1.00    inference(ennf_transformation,[],[f15])).
% 3.47/1.00  
% 3.47/1.00  fof(f78,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.47/1.00    inference(cnf_transformation,[],[f29])).
% 3.47/1.00  
% 3.47/1.00  fof(f96,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.47/1.00    inference(definition_unfolding,[],[f78,f67])).
% 3.47/1.00  
% 3.47/1.00  fof(f74,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f46])).
% 3.47/1.00  
% 3.47/1.00  fof(f93,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0) )),
% 3.47/1.00    inference(definition_unfolding,[],[f74,f67])).
% 3.47/1.00  
% 3.47/1.00  fof(f109,plain,(
% 3.47/1.00    ( ! [X2,X1] : (k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) = k1_xboole_0) )),
% 3.47/1.00    inference(equality_resolution,[],[f93])).
% 3.47/1.00  
% 3.47/1.00  fof(f10,axiom,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f25,plain,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.47/1.00    inference(ennf_transformation,[],[f10])).
% 3.47/1.00  
% 3.47/1.00  fof(f68,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f25])).
% 3.47/1.00  
% 3.47/1.00  fof(f88,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.47/1.00    inference(definition_unfolding,[],[f68,f67])).
% 3.47/1.00  
% 3.47/1.00  fof(f77,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.47/1.00    inference(cnf_transformation,[],[f29])).
% 3.47/1.00  
% 3.47/1.00  fof(f97,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.47/1.00    inference(definition_unfolding,[],[f77,f67])).
% 3.47/1.00  
% 3.47/1.00  fof(f83,plain,(
% 3.47/1.00    ( ! [X6,X7,X5] : (sK11 = X7 | k3_mcart_1(X5,X6,X7) != sK12 | ~m1_subset_1(X7,sK10) | ~m1_subset_1(X6,sK9) | ~m1_subset_1(X5,sK8)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f8,axiom,(
% 3.47/1.00    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f66,plain,(
% 3.47/1.00    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.47/1.00    inference(cnf_transformation,[],[f8])).
% 3.47/1.00  
% 3.47/1.00  fof(f98,plain,(
% 3.47/1.00    ( ! [X6,X7,X5] : (sK11 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK12 | ~m1_subset_1(X7,sK10) | ~m1_subset_1(X6,sK9) | ~m1_subset_1(X5,sK8)) )),
% 3.47/1.00    inference(definition_unfolding,[],[f83,f66])).
% 3.47/1.00  
% 3.47/1.00  fof(f79,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.47/1.00    inference(cnf_transformation,[],[f29])).
% 3.47/1.00  
% 3.47/1.00  fof(f95,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.47/1.00    inference(definition_unfolding,[],[f79,f67])).
% 3.47/1.00  
% 3.47/1.00  fof(f87,plain,(
% 3.47/1.00    k7_mcart_1(sK8,sK9,sK10,sK12) != sK11),
% 3.47/1.00    inference(cnf_transformation,[],[f48])).
% 3.47/1.00  
% 3.47/1.00  fof(f12,axiom,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 3.47/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/1.00  
% 3.47/1.00  fof(f27,plain,(
% 3.47/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.47/1.00    inference(ennf_transformation,[],[f12])).
% 3.47/1.00  
% 3.47/1.00  fof(f70,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.47/1.00    inference(cnf_transformation,[],[f27])).
% 3.47/1.00  
% 3.47/1.00  fof(f90,plain,(
% 3.47/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.47/1.00    inference(definition_unfolding,[],[f70,f67])).
% 3.47/1.00  
% 3.47/1.00  cnf(c_36,negated_conjecture,
% 3.47/1.00      ( m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) ),
% 3.47/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_701,plain,
% 3.47/1.00      ( m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_16,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.47/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_711,plain,
% 3.47/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.47/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.47/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2170,plain,
% 3.47/1.00      ( r2_hidden(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top
% 3.47/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_701,c_711]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_21,plain,
% 3.47/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.47/1.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.47/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_706,plain,
% 3.47/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.47/1.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2466,plain,
% 3.47/1.00      ( r2_hidden(k1_mcart_1(sK12),k2_zfmisc_1(sK8,sK9)) = iProver_top
% 3.47/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2170,c_706]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_11,plain,
% 3.47/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.47/1.00      | k4_tarski(sK6(X0),sK7(X0)) = X0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_713,plain,
% 3.47/1.00      ( k4_tarski(sK6(X0),sK7(X0)) = X0
% 3.47/1.00      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2576,plain,
% 3.47/1.00      ( k4_tarski(sK6(k1_mcart_1(sK12)),sK7(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
% 3.47/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2466,c_713]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_6,plain,
% 3.47/1.00      ( r2_hidden(sK2(X0,X1,X2),X0)
% 3.47/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.47/1.00      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.47/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_718,plain,
% 3.47/1.00      ( k2_zfmisc_1(X0,X1) = X2
% 3.47/1.00      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 3.47/1.00      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_12,plain,
% 3.47/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_15,plain,
% 3.47/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.47/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_712,plain,
% 3.47/1.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1380,plain,
% 3.47/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_12,c_712]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_5977,plain,
% 3.47/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 3.47/1.00      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_718,c_1380]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_13,plain,
% 3.47/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_6001,plain,
% 3.47/1.00      ( k1_xboole_0 = X0
% 3.47/1.00      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_5977,c_13]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_0,plain,
% 3.47/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.47/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_724,plain,
% 3.47/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.47/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_6174,plain,
% 3.47/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_6001,c_724]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_6668,plain,
% 3.47/1.00      ( k4_tarski(sK6(k1_mcart_1(sK12)),sK7(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
% 3.47/1.00      | k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0 ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2576,c_6174]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_34,negated_conjecture,
% 3.47/1.00      ( k1_xboole_0 != sK8 ),
% 3.47/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_33,negated_conjecture,
% 3.47/1.00      ( k1_xboole_0 != sK9 ),
% 3.47/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_32,negated_conjecture,
% 3.47/1.00      ( k1_xboole_0 != sK10 ),
% 3.47/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_25,plain,
% 3.47/1.00      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
% 3.47/1.00      | k1_xboole_0 = X1
% 3.47/1.00      | k1_xboole_0 = X0
% 3.47/1.00      | k1_xboole_0 = X2 ),
% 3.47/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_954,plain,
% 3.47/1.00      ( k2_zfmisc_1(k2_zfmisc_1(X0,sK9),X1) != k1_xboole_0
% 3.47/1.00      | k1_xboole_0 = X0
% 3.47/1.00      | k1_xboole_0 = X1
% 3.47/1.00      | k1_xboole_0 = sK9 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1203,plain,
% 3.47/1.00      ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),X0) != k1_xboole_0
% 3.47/1.00      | k1_xboole_0 = X0
% 3.47/1.00      | k1_xboole_0 = sK9
% 3.47/1.00      | k1_xboole_0 = sK8 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_954]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1807,plain,
% 3.47/1.00      ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) != k1_xboole_0
% 3.47/1.00      | k1_xboole_0 = sK10
% 3.47/1.00      | k1_xboole_0 = sK9
% 3.47/1.00      | k1_xboole_0 = sK8 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_1203]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9850,plain,
% 3.47/1.00      ( k4_tarski(sK6(k1_mcart_1(sK12)),sK7(k1_mcart_1(sK12))) = k1_mcart_1(sK12) ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_6668,c_34,c_33,c_32,c_1807]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2464,plain,
% 3.47/1.00      ( k4_tarski(sK6(sK12),sK7(sK12)) = sK12
% 3.47/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2170,c_713]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_6672,plain,
% 3.47/1.00      ( k4_tarski(sK6(sK12),sK7(sK12)) = sK12
% 3.47/1.00      | k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0 ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_2464,c_6174]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_7033,plain,
% 3.47/1.00      ( k4_tarski(sK6(sK12),sK7(sK12)) = sK12 ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_6672,c_34,c_33,c_32,c_1807]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_30,plain,
% 3.47/1.00      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_7037,plain,
% 3.47/1.00      ( k1_mcart_1(sK12) = sK6(sK12) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_7033,c_30]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9852,plain,
% 3.47/1.00      ( k4_tarski(sK6(sK6(sK12)),sK7(sK6(sK12))) = sK6(sK12) ),
% 3.47/1.00      inference(light_normalisation,[status(thm)],[c_9850,c_7037]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_29,plain,
% 3.47/1.00      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.47/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9857,plain,
% 3.47/1.00      ( k2_mcart_1(sK6(sK12)) = sK7(sK6(sK12)) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_9852,c_29]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_18,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.47/1.00      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
% 3.47/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_709,plain,
% 3.47/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.47/1.00      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3868,plain,
% 3.47/1.00      ( m1_subset_1(k6_mcart_1(sK8,sK9,sK10,sK12),sK9) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_701,c_709]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_27,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.47/1.00      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.47/1.00      | k1_xboole_0 = X2
% 3.47/1.00      | k1_xboole_0 = X1
% 3.47/1.00      | k1_xboole_0 = X3 ),
% 3.47/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_704,plain,
% 3.47/1.00      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.47/1.00      | k1_xboole_0 = X0
% 3.47/1.00      | k1_xboole_0 = X1
% 3.47/1.00      | k1_xboole_0 = X2
% 3.47/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1984,plain,
% 3.47/1.00      ( k6_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(k1_mcart_1(sK12))
% 3.47/1.00      | sK10 = k1_xboole_0
% 3.47/1.00      | sK9 = k1_xboole_0
% 3.47/1.00      | sK8 = k1_xboole_0 ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_701,c_704]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_52,plain,
% 3.47/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.47/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_24,plain,
% 3.47/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) = k1_xboole_0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_53,plain,
% 3.47/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_302,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_958,plain,
% 3.47/1.00      ( sK10 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK10 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_302]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_959,plain,
% 3.47/1.00      ( sK10 != k1_xboole_0
% 3.47/1.00      | k1_xboole_0 = sK10
% 3.47/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_958]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_960,plain,
% 3.47/1.00      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_302]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_961,plain,
% 3.47/1.00      ( sK9 != k1_xboole_0
% 3.47/1.00      | k1_xboole_0 = sK9
% 3.47/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_960]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_962,plain,
% 3.47/1.00      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_302]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_963,plain,
% 3.47/1.00      ( sK8 != k1_xboole_0
% 3.47/1.00      | k1_xboole_0 = sK8
% 3.47/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.47/1.00      inference(instantiation,[status(thm)],[c_962]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_2563,plain,
% 3.47/1.00      ( k6_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(k1_mcart_1(sK12)) ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_1984,c_34,c_33,c_32,c_52,c_53,c_959,c_961,c_963]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3897,plain,
% 3.47/1.00      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top ),
% 3.47/1.00      inference(light_normalisation,[status(thm)],[c_3868,c_2563]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_7178,plain,
% 3.47/1.00      ( m1_subset_1(k2_mcart_1(sK6(sK12)),sK9) = iProver_top ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_7037,c_3897]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_10057,plain,
% 3.47/1.00      ( m1_subset_1(sK7(sK6(sK12)),sK9) = iProver_top ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_9857,c_7178]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9856,plain,
% 3.47/1.00      ( k1_mcart_1(sK6(sK12)) = sK6(sK6(sK12)) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_9852,c_30]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_17,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.47/1.00      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
% 3.47/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_710,plain,
% 3.47/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.47/1.00      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4090,plain,
% 3.47/1.00      ( m1_subset_1(k5_mcart_1(sK8,sK9,sK10,sK12),sK8) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_701,c_710]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_28,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.47/1.00      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.47/1.00      | k1_xboole_0 = X2
% 3.47/1.00      | k1_xboole_0 = X1
% 3.47/1.00      | k1_xboole_0 = X3 ),
% 3.47/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_703,plain,
% 3.47/1.00      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.47/1.00      | k1_xboole_0 = X0
% 3.47/1.00      | k1_xboole_0 = X1
% 3.47/1.00      | k1_xboole_0 = X2
% 3.47/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1050,plain,
% 3.47/1.00      ( k5_mcart_1(sK8,sK9,sK10,sK12) = k1_mcart_1(k1_mcart_1(sK12))
% 3.47/1.00      | sK10 = k1_xboole_0
% 3.47/1.00      | sK9 = k1_xboole_0
% 3.47/1.00      | sK8 = k1_xboole_0 ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_701,c_703]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_1268,plain,
% 3.47/1.00      ( k5_mcart_1(sK8,sK9,sK10,sK12) = k1_mcart_1(k1_mcart_1(sK12)) ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_1050,c_34,c_33,c_32,c_52,c_53,c_959,c_961,c_963]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_4129,plain,
% 3.47/1.00      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top ),
% 3.47/1.00      inference(light_normalisation,[status(thm)],[c_4090,c_1268]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_7177,plain,
% 3.47/1.00      ( m1_subset_1(k1_mcart_1(sK6(sK12)),sK8) = iProver_top ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_7037,c_4129]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9994,plain,
% 3.47/1.00      ( m1_subset_1(sK6(sK6(sK12)),sK8) = iProver_top ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_9856,c_7177]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_35,negated_conjecture,
% 3.47/1.00      ( ~ m1_subset_1(X0,sK10)
% 3.47/1.00      | ~ m1_subset_1(X1,sK9)
% 3.47/1.00      | ~ m1_subset_1(X2,sK8)
% 3.47/1.00      | k4_tarski(k4_tarski(X2,X1),X0) != sK12
% 3.47/1.00      | sK11 = X0 ),
% 3.47/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_702,plain,
% 3.47/1.00      ( k4_tarski(k4_tarski(X0,X1),X2) != sK12
% 3.47/1.00      | sK11 = X2
% 3.47/1.00      | m1_subset_1(X2,sK10) != iProver_top
% 3.47/1.00      | m1_subset_1(X1,sK9) != iProver_top
% 3.47/1.00      | m1_subset_1(X0,sK8) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9858,plain,
% 3.47/1.00      ( k4_tarski(sK6(sK12),X0) != sK12
% 3.47/1.00      | sK11 = X0
% 3.47/1.00      | m1_subset_1(X0,sK10) != iProver_top
% 3.47/1.00      | m1_subset_1(sK7(sK6(sK12)),sK9) != iProver_top
% 3.47/1.00      | m1_subset_1(sK6(sK6(sK12)),sK8) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_9852,c_702]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_9902,plain,
% 3.47/1.00      ( sK7(sK12) = sK11
% 3.47/1.00      | m1_subset_1(sK7(sK6(sK12)),sK9) != iProver_top
% 3.47/1.00      | m1_subset_1(sK7(sK12),sK10) != iProver_top
% 3.47/1.00      | m1_subset_1(sK6(sK6(sK12)),sK8) != iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_7033,c_9858]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_7038,plain,
% 3.47/1.00      ( k2_mcart_1(sK12) = sK7(sK12) ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_7033,c_29]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_26,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.47/1.00      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.47/1.00      | k1_xboole_0 = X2
% 3.47/1.00      | k1_xboole_0 = X1
% 3.47/1.00      | k1_xboole_0 = X3 ),
% 3.47/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_705,plain,
% 3.47/1.00      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.47/1.00      | k1_xboole_0 = X0
% 3.47/1.00      | k1_xboole_0 = X1
% 3.47/1.00      | k1_xboole_0 = X2
% 3.47/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3402,plain,
% 3.47/1.00      ( k7_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(sK12)
% 3.47/1.00      | sK10 = k1_xboole_0
% 3.47/1.00      | sK9 = k1_xboole_0
% 3.47/1.00      | sK8 = k1_xboole_0 ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_701,c_705]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3813,plain,
% 3.47/1.00      ( k7_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(sK12) ),
% 3.47/1.00      inference(global_propositional_subsumption,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_3402,c_34,c_33,c_32,c_52,c_53,c_959,c_961,c_963]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_31,negated_conjecture,
% 3.47/1.00      ( k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 ),
% 3.47/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3817,plain,
% 3.47/1.00      ( k2_mcart_1(sK12) != sK11 ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_3813,c_31]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_7522,plain,
% 3.47/1.00      ( sK7(sK12) != sK11 ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_7038,c_3817]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_19,plain,
% 3.47/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.47/1.00      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 3.47/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_708,plain,
% 3.47/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.47/1.00      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 3.47/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3627,plain,
% 3.47/1.00      ( m1_subset_1(k7_mcart_1(sK8,sK9,sK10,sK12),sK10) = iProver_top ),
% 3.47/1.00      inference(superposition,[status(thm)],[c_701,c_708]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_3816,plain,
% 3.47/1.00      ( m1_subset_1(k2_mcart_1(sK12),sK10) = iProver_top ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_3813,c_3627]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(c_7521,plain,
% 3.47/1.00      ( m1_subset_1(sK7(sK12),sK10) = iProver_top ),
% 3.47/1.00      inference(demodulation,[status(thm)],[c_7038,c_3816]) ).
% 3.47/1.00  
% 3.47/1.00  cnf(contradiction,plain,
% 3.47/1.00      ( $false ),
% 3.47/1.00      inference(minisat,
% 3.47/1.00                [status(thm)],
% 3.47/1.00                [c_10057,c_9994,c_9902,c_7522,c_7521]) ).
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/1.00  
% 3.47/1.00  ------                               Statistics
% 3.47/1.00  
% 3.47/1.00  ------ General
% 3.47/1.00  
% 3.47/1.00  abstr_ref_over_cycles:                  0
% 3.47/1.00  abstr_ref_under_cycles:                 0
% 3.47/1.00  gc_basic_clause_elim:                   0
% 3.47/1.00  forced_gc_time:                         0
% 3.47/1.00  parsing_time:                           0.011
% 3.47/1.00  unif_index_cands_time:                  0.
% 3.47/1.00  unif_index_add_time:                    0.
% 3.47/1.00  orderings_time:                         0.
% 3.47/1.00  out_proof_time:                         0.01
% 3.47/1.00  total_time:                             0.295
% 3.47/1.00  num_of_symbols:                         55
% 3.47/1.00  num_of_terms:                           13329
% 3.47/1.00  
% 3.47/1.00  ------ Preprocessing
% 3.47/1.00  
% 3.47/1.00  num_of_splits:                          0
% 3.47/1.00  num_of_split_atoms:                     0
% 3.47/1.00  num_of_reused_defs:                     0
% 3.47/1.00  num_eq_ax_congr_red:                    56
% 3.47/1.00  num_of_sem_filtered_clauses:            1
% 3.47/1.00  num_of_subtypes:                        0
% 3.47/1.00  monotx_restored_types:                  0
% 3.47/1.00  sat_num_of_epr_types:                   0
% 3.47/1.00  sat_num_of_non_cyclic_types:            0
% 3.47/1.00  sat_guarded_non_collapsed_types:        0
% 3.47/1.00  num_pure_diseq_elim:                    0
% 3.47/1.00  simp_replaced_by:                       0
% 3.47/1.00  res_preprocessed:                       130
% 3.47/1.00  prep_upred:                             0
% 3.47/1.00  prep_unflattend:                        0
% 3.47/1.00  smt_new_axioms:                         0
% 3.47/1.00  pred_elim_cands:                        3
% 3.47/1.00  pred_elim:                              0
% 3.47/1.00  pred_elim_cl:                           0
% 3.47/1.00  pred_elim_cycles:                       1
% 3.47/1.00  merged_defs:                            0
% 3.47/1.00  merged_defs_ncl:                        0
% 3.47/1.00  bin_hyper_res:                          0
% 3.47/1.00  prep_cycles:                            3
% 3.47/1.00  pred_elim_time:                         0.
% 3.47/1.00  splitting_time:                         0.
% 3.47/1.00  sem_filter_time:                        0.
% 3.47/1.00  monotx_time:                            0.001
% 3.47/1.00  subtype_inf_time:                       0.
% 3.47/1.00  
% 3.47/1.00  ------ Problem properties
% 3.47/1.00  
% 3.47/1.00  clauses:                                37
% 3.47/1.00  conjectures:                            6
% 3.47/1.00  epr:                                    5
% 3.47/1.00  horn:                                   27
% 3.47/1.00  ground:                                 5
% 3.47/1.00  unary:                                  13
% 3.47/1.00  binary:                                 10
% 3.47/1.00  lits:                                   86
% 3.47/1.00  lits_eq:                                42
% 3.47/1.00  fd_pure:                                0
% 3.47/1.00  fd_pseudo:                              0
% 3.47/1.00  fd_cond:                                6
% 3.47/1.00  fd_pseudo_cond:                         6
% 3.47/1.00  ac_symbols:                             0
% 3.47/1.00  
% 3.47/1.00  ------ Propositional Solver
% 3.47/1.00  
% 3.47/1.00  prop_solver_calls:                      24
% 3.47/1.00  prop_fast_solver_calls:                 906
% 3.47/1.00  smt_solver_calls:                       0
% 3.47/1.00  smt_fast_solver_calls:                  0
% 3.47/1.00  prop_num_of_clauses:                    4609
% 3.47/1.00  prop_preprocess_simplified:             10795
% 3.47/1.00  prop_fo_subsumed:                       24
% 3.47/1.00  prop_solver_time:                       0.
% 3.47/1.00  smt_solver_time:                        0.
% 3.47/1.00  smt_fast_solver_time:                   0.
% 3.47/1.00  prop_fast_solver_time:                  0.
% 3.47/1.00  prop_unsat_core_time:                   0.
% 3.47/1.00  
% 3.47/1.00  ------ QBF
% 3.47/1.00  
% 3.47/1.00  qbf_q_res:                              0
% 3.47/1.00  qbf_num_tautologies:                    0
% 3.47/1.00  qbf_prep_cycles:                        0
% 3.47/1.00  
% 3.47/1.00  ------ BMC1
% 3.47/1.00  
% 3.47/1.00  bmc1_current_bound:                     -1
% 3.47/1.00  bmc1_last_solved_bound:                 -1
% 3.47/1.00  bmc1_unsat_core_size:                   -1
% 3.47/1.00  bmc1_unsat_core_parents_size:           -1
% 3.47/1.00  bmc1_merge_next_fun:                    0
% 3.47/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.47/1.00  
% 3.47/1.00  ------ Instantiation
% 3.47/1.00  
% 3.47/1.00  inst_num_of_clauses:                    1623
% 3.47/1.00  inst_num_in_passive:                    400
% 3.47/1.00  inst_num_in_active:                     518
% 3.47/1.00  inst_num_in_unprocessed:                705
% 3.47/1.00  inst_num_of_loops:                      570
% 3.47/1.00  inst_num_of_learning_restarts:          0
% 3.47/1.00  inst_num_moves_active_passive:          51
% 3.47/1.00  inst_lit_activity:                      0
% 3.47/1.00  inst_lit_activity_moves:                0
% 3.47/1.00  inst_num_tautologies:                   0
% 3.47/1.00  inst_num_prop_implied:                  0
% 3.47/1.00  inst_num_existing_simplified:           0
% 3.47/1.00  inst_num_eq_res_simplified:             0
% 3.47/1.00  inst_num_child_elim:                    0
% 3.47/1.00  inst_num_of_dismatching_blockings:      50
% 3.47/1.00  inst_num_of_non_proper_insts:           874
% 3.47/1.00  inst_num_of_duplicates:                 0
% 3.47/1.00  inst_inst_num_from_inst_to_res:         0
% 3.47/1.00  inst_dismatching_checking_time:         0.
% 3.47/1.00  
% 3.47/1.00  ------ Resolution
% 3.47/1.00  
% 3.47/1.00  res_num_of_clauses:                     0
% 3.47/1.00  res_num_in_passive:                     0
% 3.47/1.00  res_num_in_active:                      0
% 3.47/1.00  res_num_of_loops:                       133
% 3.47/1.00  res_forward_subset_subsumed:            19
% 3.47/1.00  res_backward_subset_subsumed:           0
% 3.47/1.00  res_forward_subsumed:                   0
% 3.47/1.00  res_backward_subsumed:                  0
% 3.47/1.00  res_forward_subsumption_resolution:     0
% 3.47/1.00  res_backward_subsumption_resolution:    0
% 3.47/1.00  res_clause_to_clause_subsumption:       853
% 3.47/1.00  res_orphan_elimination:                 0
% 3.47/1.00  res_tautology_del:                      3
% 3.47/1.00  res_num_eq_res_simplified:              0
% 3.47/1.00  res_num_sel_changes:                    0
% 3.47/1.00  res_moves_from_active_to_pass:          0
% 3.47/1.00  
% 3.47/1.00  ------ Superposition
% 3.47/1.00  
% 3.47/1.00  sup_time_total:                         0.
% 3.47/1.00  sup_time_generating:                    0.
% 3.47/1.00  sup_time_sim_full:                      0.
% 3.47/1.00  sup_time_sim_immed:                     0.
% 3.47/1.00  
% 3.47/1.00  sup_num_of_clauses:                     289
% 3.47/1.00  sup_num_in_active:                      84
% 3.47/1.00  sup_num_in_passive:                     205
% 3.47/1.00  sup_num_of_loops:                       112
% 3.47/1.00  sup_fw_superposition:                   143
% 3.47/1.00  sup_bw_superposition:                   253
% 3.47/1.00  sup_immediate_simplified:               69
% 3.47/1.00  sup_given_eliminated:                   1
% 3.47/1.00  comparisons_done:                       0
% 3.47/1.00  comparisons_avoided:                    11
% 3.47/1.00  
% 3.47/1.00  ------ Simplifications
% 3.47/1.00  
% 3.47/1.00  
% 3.47/1.00  sim_fw_subset_subsumed:                 20
% 3.47/1.00  sim_bw_subset_subsumed:                 11
% 3.47/1.00  sim_fw_subsumed:                        24
% 3.47/1.00  sim_bw_subsumed:                        1
% 3.47/1.00  sim_fw_subsumption_res:                 0
% 3.47/1.00  sim_bw_subsumption_res:                 0
% 3.47/1.00  sim_tautology_del:                      10
% 3.47/1.00  sim_eq_tautology_del:                   19
% 3.47/1.00  sim_eq_res_simp:                        0
% 3.47/1.00  sim_fw_demodulated:                     24
% 3.47/1.00  sim_bw_demodulated:                     26
% 3.47/1.00  sim_light_normalised:                   18
% 3.47/1.00  sim_joinable_taut:                      0
% 3.47/1.00  sim_joinable_simp:                      0
% 3.47/1.00  sim_ac_normalised:                      0
% 3.47/1.00  sim_smt_subsumption:                    0
% 3.47/1.00  
%------------------------------------------------------------------------------
