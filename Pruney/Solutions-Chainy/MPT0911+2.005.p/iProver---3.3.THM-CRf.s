%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:01 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  176 (2026 expanded)
%              Number of clauses        :   92 ( 634 expanded)
%              Number of leaves         :   24 ( 431 expanded)
%              Depth                    :   22
%              Number of atoms          :  584 (10062 expanded)
%              Number of equality atoms :  350 (5407 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f50,plain,
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
   => ( k7_mcart_1(sK7,sK8,sK9,sK11) != sK10
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK10 = X7
                  | k3_mcart_1(X5,X6,X7) != sK11
                  | ~ m1_subset_1(X7,sK9) )
              | ~ m1_subset_1(X6,sK8) )
          | ~ m1_subset_1(X5,sK7) )
      & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) != sK10
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK10 = X7
                | k3_mcart_1(X5,X6,X7) != sK11
                | ~ m1_subset_1(X7,sK9) )
            | ~ m1_subset_1(X6,sK8) )
        | ~ m1_subset_1(X5,sK7) )
    & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f31,f50])).

fof(f91,plain,(
    m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f108,plain,(
    m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) ),
    inference(definition_unfolding,[],[f91,f77])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2)
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f40,f43,f42,f41])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f115,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    ! [X6,X7,X5] :
      ( sK10 = X7
      | k3_mcart_1(X5,X6,X7) != sK11
      | ~ m1_subset_1(X7,sK9)
      | ~ m1_subset_1(X6,sK8)
      | ~ m1_subset_1(X5,sK7) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f107,plain,(
    ! [X6,X7,X5] :
      ( sK10 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK11
      | ~ m1_subset_1(X7,sK9)
      | ~ m1_subset_1(X6,sK8)
      | ~ m1_subset_1(X5,sK7) ) ),
    inference(definition_unfolding,[],[f92,f76])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f85,f77])).

fof(f93,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f79,f77])).

fof(f96,plain,(
    k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f48])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f78,f77])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f87,f97])).

fof(f119,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f105])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f86,f97])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1021,plain,
    ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1029,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2281,plain,
    ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1021,c_1029])).

cnf(c_23,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_345,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_346,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1019,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_2463,plain,
    ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2281,c_1019])).

cnf(c_8,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1038,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1032,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1601,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1032])).

cnf(c_5078,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1038,c_1601])).

cnf(c_15,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_5081,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5078,c_15])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1045,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5277,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5081,c_1045])).

cnf(c_6594,plain,
    ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
    | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2463,c_5277])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1030,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2039,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_1021,c_1030])).

cnf(c_2811,plain,
    ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_2463,c_2039])).

cnf(c_6596,plain,
    ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
    | sK11 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2811,c_5277])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1026,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2462,plain,
    ( r2_hidden(k1_mcart_1(sK11),k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2281,c_1026])).

cnf(c_2887,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2462,c_1019])).

cnf(c_6285,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_2887,c_2039])).

cnf(c_6754,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | sK11 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6285,c_5277])).

cnf(c_40,negated_conjecture,
    ( ~ m1_subset_1(X0,sK9)
    | ~ m1_subset_1(X1,sK8)
    | ~ m1_subset_1(X2,sK7)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK11
    | sK10 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1022,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK11
    | sK10 = X2
    | m1_subset_1(X2,sK9) != iProver_top
    | m1_subset_1(X1,sK8) != iProver_top
    | m1_subset_1(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_6957,plain,
    ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
    | sK10 = X0
    | sK11 = k1_xboole_0
    | m1_subset_1(X0,sK9) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6754,c_1022])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1027,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2885,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2462,c_1027])).

cnf(c_4740,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_2885,c_2039])).

cnf(c_20,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_1])).

cnf(c_186,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_1020,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_4838,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_4740,c_1020])).

cnf(c_2886,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2462,c_1026])).

cnf(c_5665,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_2886,c_2039])).

cnf(c_5671,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_5665,c_1020])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1033,plain,
    ( v1_xboole_0(k4_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6829,plain,
    ( sK11 = k1_xboole_0
    | v1_xboole_0(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_6596,c_1033])).

cnf(c_7003,plain,
    ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
    | sK10 = X0
    | sK11 = k1_xboole_0
    | m1_subset_1(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6957,c_4838,c_5671,c_6829])).

cnf(c_7013,plain,
    ( k2_mcart_1(sK11) = sK10
    | sK11 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK11),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6596,c_7003])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1025,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4126,plain,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1021,c_1025])).

cnf(c_39,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_38,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1400,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK8),X2))
    | k7_mcart_1(X1,sK8,X2,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1640,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK8),sK9))
    | k7_mcart_1(X1,sK8,sK9,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_2358,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
    | k7_mcart_1(sK7,sK8,sK9,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_3620,plain,
    ( ~ m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
    | k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_4475,plain,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4126,c_41,c_39,c_38,c_37,c_3620])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1028,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3466,plain,
    ( m1_subset_1(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1021,c_1028])).

cnf(c_4479,plain,
    ( m1_subset_1(k2_mcart_1(sK11),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4475,c_3466])).

cnf(c_36,negated_conjecture,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4480,plain,
    ( k2_mcart_1(sK11) != sK10 ),
    inference(demodulation,[status(thm)],[c_4475,c_36])).

cnf(c_7087,plain,
    ( sK11 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7013,c_4479,c_4480])).

cnf(c_8365,plain,
    ( k4_tarski(k1_mcart_1(k1_xboole_0),k2_mcart_1(k1_xboole_0)) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6594,c_7087])).

cnf(c_7119,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != k1_xboole_0
    | sK10 = X2
    | m1_subset_1(X2,sK9) != iProver_top
    | m1_subset_1(X1,sK8) != iProver_top
    | m1_subset_1(X0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7087,c_1022])).

cnf(c_8370,plain,
    ( k4_tarski(k1_xboole_0,X0) != k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
    | sK10 = X0
    | m1_subset_1(X0,sK9) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_xboole_0),sK7) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_xboole_0),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8365,c_7119])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_107,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8371,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8365,c_1033])).

cnf(c_8417,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8370,c_107,c_8371])).

cnf(c_16,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_8435,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8417,c_16])).

cnf(c_1294,plain,
    ( k2_zfmisc_1(X0,sK8) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1557,plain,
    ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_549,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1330,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_1331,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_34,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_47,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_35,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_46,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8435,c_1557,c_1331,c_47,c_46,c_37,c_38,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:56:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.43/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.43/1.00  
% 3.43/1.00  ------  iProver source info
% 3.43/1.00  
% 3.43/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.43/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.43/1.00  git: non_committed_changes: false
% 3.43/1.00  git: last_make_outside_of_git: false
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    --mode clausify
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    true
% 3.43/1.00  --inst_sos_flag                         false
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     num_symb
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       true
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    passive
% 3.43/1.00  --sup_prop_simpl_new                    true
% 3.43/1.00  --sup_prop_simpl_given                  true
% 3.43/1.00  --sup_fun_splitting                     false
% 3.43/1.00  --sup_smt_interval                      50000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   []
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_full_bw                           [BwDemod]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         3
% 3.43/1.00  --comb_sup_mult                         2
% 3.43/1.00  --comb_inst_mult                        10
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  ------ Parsing...
% 3.43/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.43/1.00  ------ Proving...
% 3.43/1.00  ------ Problem Properties 
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  clauses                                 40
% 3.43/1.00  conjectures                             6
% 3.43/1.00  EPR                                     9
% 3.43/1.00  Horn                                    29
% 3.43/1.00  unary                                   14
% 3.43/1.00  binary                                  10
% 3.43/1.00  lits                                    94
% 3.43/1.00  lits eq                                 42
% 3.43/1.00  fd_pure                                 0
% 3.43/1.00  fd_pseudo                               0
% 3.43/1.00  fd_cond                                 6
% 3.43/1.00  fd_pseudo_cond                          6
% 3.43/1.00  AC symbols                              0
% 3.43/1.00  
% 3.43/1.00  ------ Schedule dynamic 5 is on 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  Current options:
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    --mode clausify
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    true
% 3.43/1.00  --inst_sos_flag                         false
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     none
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       false
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    passive
% 3.43/1.00  --sup_prop_simpl_new                    true
% 3.43/1.00  --sup_prop_simpl_given                  true
% 3.43/1.00  --sup_fun_splitting                     false
% 3.43/1.00  --sup_smt_interval                      50000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   []
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_full_bw                           [BwDemod]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         3
% 3.43/1.00  --comb_sup_mult                         2
% 3.43/1.00  --comb_inst_mult                        10
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ Proving...
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  % SZS status Theorem for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  fof(f19,conjecture,(
% 3.43/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f20,negated_conjecture,(
% 3.43/1.00    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.43/1.00    inference(negated_conjecture,[],[f19])).
% 3.43/1.00  
% 3.43/1.00  fof(f30,plain,(
% 3.43/1.00    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.43/1.00    inference(ennf_transformation,[],[f20])).
% 3.43/1.00  
% 3.43/1.00  fof(f31,plain,(
% 3.43/1.00    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.43/1.00    inference(flattening,[],[f30])).
% 3.43/1.00  
% 3.43/1.00  fof(f50,plain,(
% 3.43/1.00    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & ! [X5] : (! [X6] : (! [X7] : (sK10 = X7 | k3_mcart_1(X5,X6,X7) != sK11 | ~m1_subset_1(X7,sK9)) | ~m1_subset_1(X6,sK8)) | ~m1_subset_1(X5,sK7)) & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f51,plain,(
% 3.43/1.00    k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & ! [X5] : (! [X6] : (! [X7] : (sK10 = X7 | k3_mcart_1(X5,X6,X7) != sK11 | ~m1_subset_1(X7,sK9)) | ~m1_subset_1(X6,sK8)) | ~m1_subset_1(X5,sK7)) & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9))),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f31,f50])).
% 3.43/1.00  
% 3.43/1.00  fof(f91,plain,(
% 3.43/1.00    m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9))),
% 3.43/1.00    inference(cnf_transformation,[],[f51])).
% 3.43/1.00  
% 3.43/1.00  fof(f12,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f77,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f12])).
% 3.43/1.00  
% 3.43/1.00  fof(f108,plain,(
% 3.43/1.00    m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))),
% 3.43/1.00    inference(definition_unfolding,[],[f91,f77])).
% 3.43/1.00  
% 3.43/1.00  fof(f9,axiom,(
% 3.43/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f23,plain,(
% 3.43/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.43/1.00    inference(ennf_transformation,[],[f9])).
% 3.43/1.00  
% 3.43/1.00  fof(f24,plain,(
% 3.43/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.43/1.00    inference(flattening,[],[f23])).
% 3.43/1.00  
% 3.43/1.00  fof(f74,plain,(
% 3.43/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f24])).
% 3.43/1.00  
% 3.43/1.00  fof(f10,axiom,(
% 3.43/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f75,plain,(
% 3.43/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f10])).
% 3.43/1.00  
% 3.43/1.00  fof(f16,axiom,(
% 3.43/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f27,plain,(
% 3.43/1.00    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 3.43/1.00    inference(ennf_transformation,[],[f16])).
% 3.43/1.00  
% 3.43/1.00  fof(f28,plain,(
% 3.43/1.00    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 3.43/1.00    inference(flattening,[],[f27])).
% 3.43/1.00  
% 3.43/1.00  fof(f82,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f28])).
% 3.43/1.00  
% 3.43/1.00  fof(f4,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f39,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.43/1.00    inference(nnf_transformation,[],[f4])).
% 3.43/1.00  
% 3.43/1.00  fof(f40,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.43/1.00    inference(rectify,[],[f39])).
% 3.43/1.00  
% 3.43/1.00  fof(f43,plain,(
% 3.43/1.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f42,plain,(
% 3.43/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f41,plain,(
% 3.43/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f44,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f40,f43,f42,f41])).
% 3.43/1.00  
% 3.43/1.00  fof(f61,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f44])).
% 3.43/1.00  
% 3.43/1.00  fof(f6,axiom,(
% 3.43/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f45,plain,(
% 3.43/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.43/1.00    inference(nnf_transformation,[],[f6])).
% 3.43/1.00  
% 3.43/1.00  fof(f46,plain,(
% 3.43/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.43/1.00    inference(flattening,[],[f45])).
% 3.43/1.00  
% 3.43/1.00  fof(f68,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.43/1.00    inference(cnf_transformation,[],[f46])).
% 3.43/1.00  
% 3.43/1.00  fof(f114,plain,(
% 3.43/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.43/1.00    inference(equality_resolution,[],[f68])).
% 3.43/1.00  
% 3.43/1.00  fof(f7,axiom,(
% 3.43/1.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f69,plain,(
% 3.43/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f7])).
% 3.43/1.00  
% 3.43/1.00  fof(f67,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f46])).
% 3.43/1.00  
% 3.43/1.00  fof(f115,plain,(
% 3.43/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.43/1.00    inference(equality_resolution,[],[f67])).
% 3.43/1.00  
% 3.43/1.00  fof(f1,axiom,(
% 3.43/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f32,plain,(
% 3.43/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.43/1.00    inference(nnf_transformation,[],[f1])).
% 3.43/1.00  
% 3.43/1.00  fof(f33,plain,(
% 3.43/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.43/1.00    inference(rectify,[],[f32])).
% 3.43/1.00  
% 3.43/1.00  fof(f34,plain,(
% 3.43/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f35,plain,(
% 3.43/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.43/1.00  
% 3.43/1.00  fof(f52,plain,(
% 3.43/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f35])).
% 3.43/1.00  
% 3.43/1.00  fof(f8,axiom,(
% 3.43/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f22,plain,(
% 3.43/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.43/1.00    inference(ennf_transformation,[],[f8])).
% 3.43/1.00  
% 3.43/1.00  fof(f47,plain,(
% 3.43/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.43/1.00    inference(nnf_transformation,[],[f22])).
% 3.43/1.00  
% 3.43/1.00  fof(f72,plain,(
% 3.43/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f47])).
% 3.43/1.00  
% 3.43/1.00  fof(f15,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f26,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.43/1.00    inference(ennf_transformation,[],[f15])).
% 3.43/1.00  
% 3.43/1.00  fof(f80,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f26])).
% 3.43/1.00  
% 3.43/1.00  fof(f92,plain,(
% 3.43/1.00    ( ! [X6,X7,X5] : (sK10 = X7 | k3_mcart_1(X5,X6,X7) != sK11 | ~m1_subset_1(X7,sK9) | ~m1_subset_1(X6,sK8) | ~m1_subset_1(X5,sK7)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f51])).
% 3.43/1.00  
% 3.43/1.00  fof(f11,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f76,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f11])).
% 3.43/1.00  
% 3.43/1.00  fof(f107,plain,(
% 3.43/1.00    ( ! [X6,X7,X5] : (sK10 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK11 | ~m1_subset_1(X7,sK9) | ~m1_subset_1(X6,sK8) | ~m1_subset_1(X5,sK7)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f92,f76])).
% 3.43/1.00  
% 3.43/1.00  fof(f81,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f26])).
% 3.43/1.00  
% 3.43/1.00  fof(f71,plain,(
% 3.43/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f47])).
% 3.43/1.00  
% 3.43/1.00  fof(f5,axiom,(
% 3.43/1.00    ! [X0,X1] : ~v1_xboole_0(k4_tarski(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f65,plain,(
% 3.43/1.00    ( ! [X0,X1] : (~v1_xboole_0(k4_tarski(X0,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f5])).
% 3.43/1.00  
% 3.43/1.00  fof(f17,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f29,plain,(
% 3.43/1.00    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.43/1.00    inference(ennf_transformation,[],[f17])).
% 3.43/1.00  
% 3.43/1.00  fof(f85,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f29])).
% 3.43/1.00  
% 3.43/1.00  fof(f99,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.43/1.00    inference(definition_unfolding,[],[f85,f77])).
% 3.43/1.00  
% 3.43/1.00  fof(f93,plain,(
% 3.43/1.00    k1_xboole_0 != sK7),
% 3.43/1.00    inference(cnf_transformation,[],[f51])).
% 3.43/1.00  
% 3.43/1.00  fof(f94,plain,(
% 3.43/1.00    k1_xboole_0 != sK8),
% 3.43/1.00    inference(cnf_transformation,[],[f51])).
% 3.43/1.00  
% 3.43/1.00  fof(f95,plain,(
% 3.43/1.00    k1_xboole_0 != sK9),
% 3.43/1.00    inference(cnf_transformation,[],[f51])).
% 3.43/1.00  
% 3.43/1.00  fof(f14,axiom,(
% 3.43/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f25,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.43/1.00    inference(ennf_transformation,[],[f14])).
% 3.43/1.00  
% 3.43/1.00  fof(f79,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f25])).
% 3.43/1.00  
% 3.43/1.00  fof(f98,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f79,f77])).
% 3.43/1.00  
% 3.43/1.00  fof(f96,plain,(
% 3.43/1.00    k7_mcart_1(sK7,sK8,sK9,sK11) != sK10),
% 3.43/1.00    inference(cnf_transformation,[],[f51])).
% 3.43/1.00  
% 3.43/1.00  fof(f2,axiom,(
% 3.43/1.00    v1_xboole_0(k1_xboole_0)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f54,plain,(
% 3.43/1.00    v1_xboole_0(k1_xboole_0)),
% 3.43/1.00    inference(cnf_transformation,[],[f2])).
% 3.43/1.00  
% 3.43/1.00  fof(f66,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f46])).
% 3.43/1.00  
% 3.43/1.00  fof(f18,axiom,(
% 3.43/1.00    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f48,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.43/1.00    inference(nnf_transformation,[],[f18])).
% 3.43/1.00  
% 3.43/1.00  fof(f49,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.43/1.00    inference(flattening,[],[f48])).
% 3.43/1.00  
% 3.43/1.00  fof(f87,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f49])).
% 3.43/1.00  
% 3.43/1.00  fof(f13,axiom,(
% 3.43/1.00    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f78,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f13])).
% 3.43/1.00  
% 3.43/1.00  fof(f97,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f78,f77])).
% 3.43/1.00  
% 3.43/1.00  fof(f105,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f87,f97])).
% 3.43/1.00  
% 3.43/1.00  fof(f119,plain,(
% 3.43/1.00    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 3.43/1.00    inference(equality_resolution,[],[f105])).
% 3.43/1.00  
% 3.43/1.00  fof(f86,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f49])).
% 3.43/1.00  
% 3.43/1.00  fof(f106,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.43/1.00    inference(definition_unfolding,[],[f86,f97])).
% 3.43/1.00  
% 3.43/1.00  cnf(c_41,negated_conjecture,
% 3.43/1.00      ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1021,plain,
% 3.43/1.00      ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_22,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1029,plain,
% 3.43/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.43/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.43/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2281,plain,
% 3.43/1.00      ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
% 3.43/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1021,c_1029]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_23,plain,
% 3.43/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_27,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,X1)
% 3.43/1.00      | ~ v1_relat_1(X1)
% 3.43/1.00      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_345,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,X1)
% 3.43/1.00      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.43/1.00      | k2_zfmisc_1(X2,X3) != X1 ),
% 3.43/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_346,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.43/1.00      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.43/1.00      inference(unflattening,[status(thm)],[c_345]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1019,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.43/1.00      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2463,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
% 3.43/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2281,c_1019]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8,plain,
% 3.43/1.00      ( r2_hidden(sK3(X0,X1,X2),X0)
% 3.43/1.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.43/1.00      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.43/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1038,plain,
% 3.43/1.00      ( k2_zfmisc_1(X0,X1) = X2
% 3.43/1.00      | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
% 3.43/1.00      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_14,plain,
% 3.43/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_17,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1032,plain,
% 3.43/1.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1601,plain,
% 3.43/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_14,c_1032]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5078,plain,
% 3.43/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 3.43/1.00      | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1038,c_1601]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_15,plain,
% 3.43/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5081,plain,
% 3.43/1.00      ( k1_xboole_0 = X0
% 3.43/1.00      | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_5078,c_15]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1045,plain,
% 3.43/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.43/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5277,plain,
% 3.43/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_5081,c_1045]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6594,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
% 3.43/1.00      | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2463,c_5277]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_19,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.43/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1030,plain,
% 3.43/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.43/1.00      | v1_xboole_0(X1) != iProver_top
% 3.43/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2039,plain,
% 3.43/1.00      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
% 3.43/1.00      | v1_xboole_0(sK11) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1021,c_1030]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2811,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
% 3.43/1.00      | v1_xboole_0(sK11) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2463,c_2039]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6596,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
% 3.43/1.00      | sK11 = k1_xboole_0 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2811,c_5277]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_26,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.43/1.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1026,plain,
% 3.43/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.43/1.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2462,plain,
% 3.43/1.00      ( r2_hidden(k1_mcart_1(sK11),k2_zfmisc_1(sK7,sK8)) = iProver_top
% 3.43/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2281,c_1026]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2887,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.43/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2462,c_1019]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6285,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.43/1.00      | v1_xboole_0(sK11) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2887,c_2039]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6754,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.43/1.00      | sK11 = k1_xboole_0 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_6285,c_5277]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_40,negated_conjecture,
% 3.43/1.00      ( ~ m1_subset_1(X0,sK9)
% 3.43/1.00      | ~ m1_subset_1(X1,sK8)
% 3.43/1.00      | ~ m1_subset_1(X2,sK7)
% 3.43/1.00      | k4_tarski(k4_tarski(X2,X1),X0) != sK11
% 3.43/1.00      | sK10 = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1022,plain,
% 3.43/1.00      ( k4_tarski(k4_tarski(X0,X1),X2) != sK11
% 3.43/1.00      | sK10 = X2
% 3.43/1.00      | m1_subset_1(X2,sK9) != iProver_top
% 3.43/1.00      | m1_subset_1(X1,sK8) != iProver_top
% 3.43/1.00      | m1_subset_1(X0,sK7) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6957,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
% 3.43/1.00      | sK10 = X0
% 3.43/1.00      | sK11 = k1_xboole_0
% 3.43/1.00      | m1_subset_1(X0,sK9) != iProver_top
% 3.43/1.00      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) != iProver_top
% 3.43/1.00      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_6754,c_1022]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_25,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.43/1.00      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.43/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1027,plain,
% 3.43/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.43/1.00      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2885,plain,
% 3.43/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top
% 3.43/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2462,c_1027]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4740,plain,
% 3.43/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top
% 3.43/1.00      | v1_xboole_0(sK11) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2885,c_2039]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_20,plain,
% 3.43/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_185,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_20,c_1]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_186,plain,
% 3.43/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.43/1.00      inference(renaming,[status(thm)],[c_185]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1020,plain,
% 3.43/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.43/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4838,plain,
% 3.43/1.00      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top
% 3.43/1.00      | v1_xboole_0(sK11) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_4740,c_1020]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2886,plain,
% 3.43/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top
% 3.43/1.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2462,c_1026]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5665,plain,
% 3.43/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top
% 3.43/1.00      | v1_xboole_0(sK11) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2886,c_2039]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5671,plain,
% 3.43/1.00      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top
% 3.43/1.00      | v1_xboole_0(sK11) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_5665,c_1020]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_13,plain,
% 3.43/1.00      ( ~ v1_xboole_0(k4_tarski(X0,X1)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1033,plain,
% 3.43/1.00      ( v1_xboole_0(k4_tarski(X0,X1)) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6829,plain,
% 3.43/1.00      ( sK11 = k1_xboole_0 | v1_xboole_0(sK11) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_6596,c_1033]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_7003,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
% 3.43/1.00      | sK10 = X0
% 3.43/1.00      | sK11 = k1_xboole_0
% 3.43/1.00      | m1_subset_1(X0,sK9) != iProver_top ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_6957,c_4838,c_5671,c_6829]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_7013,plain,
% 3.43/1.00      ( k2_mcart_1(sK11) = sK10
% 3.43/1.00      | sK11 = k1_xboole_0
% 3.43/1.00      | m1_subset_1(k2_mcart_1(sK11),sK9) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_6596,c_7003]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_28,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.43/1.00      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.43/1.00      | k1_xboole_0 = X2
% 3.43/1.00      | k1_xboole_0 = X1
% 3.43/1.00      | k1_xboole_0 = X3 ),
% 3.43/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1025,plain,
% 3.43/1.00      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.43/1.00      | k1_xboole_0 = X1
% 3.43/1.00      | k1_xboole_0 = X0
% 3.43/1.00      | k1_xboole_0 = X2
% 3.43/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4126,plain,
% 3.43/1.00      ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
% 3.43/1.00      | sK9 = k1_xboole_0
% 3.43/1.00      | sK8 = k1_xboole_0
% 3.43/1.00      | sK7 = k1_xboole_0 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1021,c_1025]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_39,negated_conjecture,
% 3.43/1.00      ( k1_xboole_0 != sK7 ),
% 3.43/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_38,negated_conjecture,
% 3.43/1.00      ( k1_xboole_0 != sK8 ),
% 3.43/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_37,negated_conjecture,
% 3.43/1.00      ( k1_xboole_0 != sK9 ),
% 3.43/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1400,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK8),X2))
% 3.43/1.00      | k7_mcart_1(X1,sK8,X2,X0) = k2_mcart_1(X0)
% 3.43/1.00      | k1_xboole_0 = X2
% 3.43/1.00      | k1_xboole_0 = X1
% 3.43/1.00      | k1_xboole_0 = sK8 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1640,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK8),sK9))
% 3.43/1.00      | k7_mcart_1(X1,sK8,sK9,X0) = k2_mcart_1(X0)
% 3.43/1.00      | k1_xboole_0 = X1
% 3.43/1.00      | k1_xboole_0 = sK9
% 3.43/1.00      | k1_xboole_0 = sK8 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_1400]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2358,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
% 3.43/1.00      | k7_mcart_1(sK7,sK8,sK9,X0) = k2_mcart_1(X0)
% 3.43/1.00      | k1_xboole_0 = sK9
% 3.43/1.00      | k1_xboole_0 = sK8
% 3.43/1.00      | k1_xboole_0 = sK7 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_1640]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3620,plain,
% 3.43/1.00      ( ~ m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
% 3.43/1.00      | k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
% 3.43/1.00      | k1_xboole_0 = sK9
% 3.43/1.00      | k1_xboole_0 = sK8
% 3.43/1.00      | k1_xboole_0 = sK7 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_2358]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4475,plain,
% 3.43/1.00      ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11) ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_4126,c_41,c_39,c_38,c_37,c_3620]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_24,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.43/1.00      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 3.43/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1028,plain,
% 3.43/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.43/1.00      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3466,plain,
% 3.43/1.00      ( m1_subset_1(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1021,c_1028]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4479,plain,
% 3.43/1.00      ( m1_subset_1(k2_mcart_1(sK11),sK9) = iProver_top ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_4475,c_3466]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_36,negated_conjecture,
% 3.43/1.00      ( k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 ),
% 3.43/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4480,plain,
% 3.43/1.00      ( k2_mcart_1(sK11) != sK10 ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_4475,c_36]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_7087,plain,
% 3.43/1.00      ( sK11 = k1_xboole_0 ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_7013,c_4479,c_4480]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8365,plain,
% 3.43/1.00      ( k4_tarski(k1_mcart_1(k1_xboole_0),k2_mcart_1(k1_xboole_0)) = k1_xboole_0
% 3.43/1.00      | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_6594,c_7087]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_7119,plain,
% 3.43/1.00      ( k4_tarski(k4_tarski(X0,X1),X2) != k1_xboole_0
% 3.43/1.00      | sK10 = X2
% 3.43/1.00      | m1_subset_1(X2,sK9) != iProver_top
% 3.43/1.00      | m1_subset_1(X1,sK8) != iProver_top
% 3.43/1.00      | m1_subset_1(X0,sK7) != iProver_top ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_7087,c_1022]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8370,plain,
% 3.43/1.00      ( k4_tarski(k1_xboole_0,X0) != k1_xboole_0
% 3.43/1.00      | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
% 3.43/1.00      | sK10 = X0
% 3.43/1.00      | m1_subset_1(X0,sK9) != iProver_top
% 3.43/1.00      | m1_subset_1(k1_mcart_1(k1_xboole_0),sK7) != iProver_top
% 3.43/1.00      | m1_subset_1(k2_mcart_1(k1_xboole_0),sK8) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_8365,c_7119]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2,plain,
% 3.43/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.43/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_107,plain,
% 3.43/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8371,plain,
% 3.43/1.00      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
% 3.43/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_8365,c_1033]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8417,plain,
% 3.43/1.00      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_8370,c_107,c_8371]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_16,plain,
% 3.43/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.43/1.00      | k1_xboole_0 = X1
% 3.43/1.00      | k1_xboole_0 = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8435,plain,
% 3.43/1.00      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0 | sK9 = k1_xboole_0 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_8417,c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1294,plain,
% 3.43/1.00      ( k2_zfmisc_1(X0,sK8) != k1_xboole_0
% 3.43/1.00      | k1_xboole_0 = X0
% 3.43/1.00      | k1_xboole_0 = sK8 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1557,plain,
% 3.43/1.00      ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
% 3.43/1.00      | k1_xboole_0 = sK8
% 3.43/1.00      | k1_xboole_0 = sK7 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_1294]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_549,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1330,plain,
% 3.43/1.00      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_549]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1331,plain,
% 3.43/1.00      ( sK9 != k1_xboole_0
% 3.43/1.00      | k1_xboole_0 = sK9
% 3.43/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_1330]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_34,plain,
% 3.43/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_47,plain,
% 3.43/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_34]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_35,plain,
% 3.43/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.43/1.00      | k1_xboole_0 = X1
% 3.43/1.00      | k1_xboole_0 = X0
% 3.43/1.00      | k1_xboole_0 = X2
% 3.43/1.00      | k1_xboole_0 = X3 ),
% 3.43/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_46,plain,
% 3.43/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.43/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_35]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(contradiction,plain,
% 3.43/1.00      ( $false ),
% 3.43/1.00      inference(minisat,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_8435,c_1557,c_1331,c_47,c_46,c_37,c_38,c_39]) ).
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  ------                               Statistics
% 3.43/1.00  
% 3.43/1.00  ------ General
% 3.43/1.00  
% 3.43/1.00  abstr_ref_over_cycles:                  0
% 3.43/1.00  abstr_ref_under_cycles:                 0
% 3.43/1.00  gc_basic_clause_elim:                   0
% 3.43/1.00  forced_gc_time:                         0
% 3.43/1.00  parsing_time:                           0.01
% 3.43/1.00  unif_index_cands_time:                  0.
% 3.43/1.00  unif_index_add_time:                    0.
% 3.43/1.00  orderings_time:                         0.
% 3.43/1.00  out_proof_time:                         0.014
% 3.43/1.00  total_time:                             0.28
% 3.43/1.00  num_of_symbols:                         55
% 3.43/1.00  num_of_terms:                           11162
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing
% 3.43/1.00  
% 3.43/1.00  num_of_splits:                          0
% 3.43/1.00  num_of_split_atoms:                     0
% 3.43/1.00  num_of_reused_defs:                     0
% 3.43/1.00  num_eq_ax_congr_red:                    78
% 3.43/1.00  num_of_sem_filtered_clauses:            1
% 3.43/1.00  num_of_subtypes:                        0
% 3.43/1.00  monotx_restored_types:                  0
% 3.43/1.00  sat_num_of_epr_types:                   0
% 3.43/1.00  sat_num_of_non_cyclic_types:            0
% 3.43/1.00  sat_guarded_non_collapsed_types:        0
% 3.43/1.00  num_pure_diseq_elim:                    0
% 3.43/1.00  simp_replaced_by:                       0
% 3.43/1.00  res_preprocessed:                       182
% 3.43/1.00  prep_upred:                             0
% 3.43/1.00  prep_unflattend:                        1
% 3.43/1.00  smt_new_axioms:                         0
% 3.43/1.00  pred_elim_cands:                        3
% 3.43/1.00  pred_elim:                              1
% 3.43/1.00  pred_elim_cl:                           1
% 3.43/1.00  pred_elim_cycles:                       3
% 3.43/1.00  merged_defs:                            0
% 3.43/1.00  merged_defs_ncl:                        0
% 3.43/1.00  bin_hyper_res:                          0
% 3.43/1.00  prep_cycles:                            4
% 3.43/1.00  pred_elim_time:                         0.001
% 3.43/1.00  splitting_time:                         0.
% 3.43/1.00  sem_filter_time:                        0.
% 3.43/1.00  monotx_time:                            0.
% 3.43/1.00  subtype_inf_time:                       0.
% 3.43/1.00  
% 3.43/1.00  ------ Problem properties
% 3.43/1.00  
% 3.43/1.00  clauses:                                40
% 3.43/1.00  conjectures:                            6
% 3.43/1.00  epr:                                    9
% 3.43/1.00  horn:                                   29
% 3.43/1.00  ground:                                 6
% 3.43/1.00  unary:                                  14
% 3.43/1.00  binary:                                 10
% 3.43/1.00  lits:                                   94
% 3.43/1.00  lits_eq:                                42
% 3.43/1.00  fd_pure:                                0
% 3.43/1.00  fd_pseudo:                              0
% 3.43/1.00  fd_cond:                                6
% 3.43/1.00  fd_pseudo_cond:                         6
% 3.43/1.00  ac_symbols:                             0
% 3.43/1.00  
% 3.43/1.00  ------ Propositional Solver
% 3.43/1.00  
% 3.43/1.00  prop_solver_calls:                      27
% 3.43/1.00  prop_fast_solver_calls:                 1135
% 3.43/1.00  smt_solver_calls:                       0
% 3.43/1.00  smt_fast_solver_calls:                  0
% 3.43/1.00  prop_num_of_clauses:                    3210
% 3.43/1.00  prop_preprocess_simplified:             10621
% 3.43/1.00  prop_fo_subsumed:                       24
% 3.43/1.00  prop_solver_time:                       0.
% 3.43/1.00  smt_solver_time:                        0.
% 3.43/1.00  smt_fast_solver_time:                   0.
% 3.43/1.00  prop_fast_solver_time:                  0.
% 3.43/1.00  prop_unsat_core_time:                   0.
% 3.43/1.00  
% 3.43/1.00  ------ QBF
% 3.43/1.00  
% 3.43/1.00  qbf_q_res:                              0
% 3.43/1.00  qbf_num_tautologies:                    0
% 3.43/1.00  qbf_prep_cycles:                        0
% 3.43/1.00  
% 3.43/1.00  ------ BMC1
% 3.43/1.00  
% 3.43/1.00  bmc1_current_bound:                     -1
% 3.43/1.00  bmc1_last_solved_bound:                 -1
% 3.43/1.00  bmc1_unsat_core_size:                   -1
% 3.43/1.00  bmc1_unsat_core_parents_size:           -1
% 3.43/1.00  bmc1_merge_next_fun:                    0
% 3.43/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation
% 3.43/1.00  
% 3.43/1.00  inst_num_of_clauses:                    1060
% 3.43/1.00  inst_num_in_passive:                    437
% 3.43/1.00  inst_num_in_active:                     424
% 3.43/1.00  inst_num_in_unprocessed:                199
% 3.43/1.00  inst_num_of_loops:                      500
% 3.43/1.00  inst_num_of_learning_restarts:          0
% 3.43/1.00  inst_num_moves_active_passive:          75
% 3.43/1.00  inst_lit_activity:                      0
% 3.43/1.00  inst_lit_activity_moves:                0
% 3.43/1.00  inst_num_tautologies:                   0
% 3.43/1.00  inst_num_prop_implied:                  0
% 3.43/1.00  inst_num_existing_simplified:           0
% 3.43/1.00  inst_num_eq_res_simplified:             0
% 3.43/1.00  inst_num_child_elim:                    0
% 3.43/1.00  inst_num_of_dismatching_blockings:      758
% 3.43/1.00  inst_num_of_non_proper_insts:           1154
% 3.43/1.00  inst_num_of_duplicates:                 0
% 3.43/1.00  inst_inst_num_from_inst_to_res:         0
% 3.43/1.00  inst_dismatching_checking_time:         0.
% 3.43/1.00  
% 3.43/1.00  ------ Resolution
% 3.43/1.00  
% 3.43/1.00  res_num_of_clauses:                     0
% 3.43/1.00  res_num_in_passive:                     0
% 3.43/1.00  res_num_in_active:                      0
% 3.43/1.00  res_num_of_loops:                       186
% 3.43/1.00  res_forward_subset_subsumed:            23
% 3.43/1.00  res_backward_subset_subsumed:           0
% 3.43/1.00  res_forward_subsumed:                   0
% 3.43/1.00  res_backward_subsumed:                  0
% 3.43/1.00  res_forward_subsumption_resolution:     0
% 3.43/1.00  res_backward_subsumption_resolution:    0
% 3.43/1.00  res_clause_to_clause_subsumption:       403
% 3.43/1.00  res_orphan_elimination:                 0
% 3.43/1.00  res_tautology_del:                      2
% 3.43/1.00  res_num_eq_res_simplified:              0
% 3.43/1.00  res_num_sel_changes:                    0
% 3.43/1.00  res_moves_from_active_to_pass:          0
% 3.43/1.00  
% 3.43/1.00  ------ Superposition
% 3.43/1.00  
% 3.43/1.00  sup_time_total:                         0.
% 3.43/1.00  sup_time_generating:                    0.
% 3.43/1.00  sup_time_sim_full:                      0.
% 3.43/1.00  sup_time_sim_immed:                     0.
% 3.43/1.00  
% 3.43/1.00  sup_num_of_clauses:                     202
% 3.43/1.00  sup_num_in_active:                      59
% 3.43/1.00  sup_num_in_passive:                     143
% 3.43/1.00  sup_num_of_loops:                       99
% 3.43/1.00  sup_fw_superposition:                   63
% 3.43/1.00  sup_bw_superposition:                   243
% 3.43/1.00  sup_immediate_simplified:               67
% 3.43/1.00  sup_given_eliminated:                   0
% 3.43/1.00  comparisons_done:                       0
% 3.43/1.00  comparisons_avoided:                    14
% 3.43/1.00  
% 3.43/1.00  ------ Simplifications
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  sim_fw_subset_subsumed:                 49
% 3.43/1.00  sim_bw_subset_subsumed:                 12
% 3.43/1.00  sim_fw_subsumed:                        13
% 3.43/1.00  sim_bw_subsumed:                        1
% 3.43/1.00  sim_fw_subsumption_res:                 0
% 3.43/1.00  sim_bw_subsumption_res:                 0
% 3.43/1.00  sim_tautology_del:                      9
% 3.43/1.00  sim_eq_tautology_del:                   27
% 3.43/1.00  sim_eq_res_simp:                        1
% 3.43/1.00  sim_fw_demodulated:                     10
% 3.43/1.00  sim_bw_demodulated:                     38
% 3.43/1.00  sim_light_normalised:                   13
% 3.43/1.00  sim_joinable_taut:                      0
% 3.43/1.00  sim_joinable_simp:                      0
% 3.43/1.00  sim_ac_normalised:                      0
% 3.43/1.00  sim_smt_subsumption:                    0
% 3.43/1.00  
%------------------------------------------------------------------------------
