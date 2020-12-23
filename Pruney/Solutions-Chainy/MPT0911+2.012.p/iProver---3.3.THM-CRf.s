%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:02 EST 2020

% Result     : Theorem 15.96s
% Output     : CNFRefutation 15.96s
% Verified   : 
% Statistics : Number of formulae       :  233 (3029 expanded)
%              Number of clauses        :  139 ( 931 expanded)
%              Number of leaves         :   25 ( 694 expanded)
%              Depth                    :   28
%              Number of atoms          :  731 (15005 expanded)
%              Number of equality atoms :  461 (7858 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f49,plain,
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
   => ( k7_mcart_1(sK9,sK10,sK11,sK13) != sK12
      & k1_xboole_0 != sK11
      & k1_xboole_0 != sK10
      & k1_xboole_0 != sK9
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK12 = X7
                  | k3_mcart_1(X5,X6,X7) != sK13
                  | ~ m1_subset_1(X7,sK11) )
              | ~ m1_subset_1(X6,sK10) )
          | ~ m1_subset_1(X5,sK9) )
      & m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11)) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k7_mcart_1(sK9,sK10,sK11,sK13) != sK12
    & k1_xboole_0 != sK11
    & k1_xboole_0 != sK10
    & k1_xboole_0 != sK9
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK12 = X7
                | k3_mcart_1(X5,X6,X7) != sK13
                | ~ m1_subset_1(X7,sK11) )
            | ~ m1_subset_1(X6,sK10) )
        | ~ m1_subset_1(X5,sK9) )
    & m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f32,f49])).

fof(f87,plain,(
    m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11)) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f105,plain,(
    m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
    inference(definition_unfolding,[],[f87,f73])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK7(X0),sK8(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK7(X0),sK8(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f23,f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK7(X0),sK8(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f46])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f16])).

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
    inference(flattening,[],[f47])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f73])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f80,f93])).

fof(f89,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f88,plain,(
    ! [X6,X7,X5] :
      ( sK12 = X7
      | k3_mcart_1(X5,X6,X7) != sK13
      | ~ m1_subset_1(X7,sK11)
      | ~ m1_subset_1(X6,sK10)
      | ~ m1_subset_1(X5,sK9) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f104,plain,(
    ! [X6,X7,X5] :
      ( sK12 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK13
      | ~ m1_subset_1(X7,sK11)
      | ~ m1_subset_1(X6,sK10)
      | ~ m1_subset_1(X5,sK9) ) ),
    inference(definition_unfolding,[],[f88,f72])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f106,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f111,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f75,f73])).

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

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f78,f73])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f81,f93])).

fof(f115,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f102])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f79,f73])).

fof(f92,plain,(
    k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f76,f73])).

fof(f61,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f108,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f107])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_857,plain,
    ( m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_864,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3862,plain,
    ( r2_hidden(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_864])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK7(X0),sK8(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_869,plain,
    ( k4_tarski(sK7(X0),sK8(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3929,plain,
    ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3862,c_869])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_880,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_883,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3113,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_880,c_883])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_867,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_879,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2540,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_867,c_879])).

cnf(c_2556,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_867,c_2540])).

cnf(c_3633,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3113,c_2556])).

cnf(c_23699,plain,
    ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3929,c_3633])).

cnf(c_30,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_23987,plain,
    ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13
    | k2_zfmisc_1(sK9,sK10) = k1_xboole_0
    | sK11 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_23699,c_30])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_955,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,X0),X1),X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1077,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),X0),X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK10
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_1221,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK11
    | k1_xboole_0 = sK10
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_3634,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3113,c_2540])).

cnf(c_24524,plain,
    ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3929,c_3634])).

cnf(c_24875,plain,
    ( k1_xboole_0 = X0
    | k4_tarski(sK7(sK13),sK8(sK13)) = sK13 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23987,c_36,c_35,c_34,c_1221,c_24524])).

cnf(c_24876,plain,
    ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_24875])).

cnf(c_25374,plain,
    ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13 ),
    inference(superposition,[status(thm)],[c_24876,c_36])).

cnf(c_31,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_25489,plain,
    ( k2_mcart_1(sK13) = sK8(sK13) ),
    inference(superposition,[status(thm)],[c_25374,c_31])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK5(X1,X2,X0),sK6(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_872,plain,
    ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5732,plain,
    ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3862,c_872])).

cnf(c_3635,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3113,c_879])).

cnf(c_5998,plain,
    ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5732,c_3635])).

cnf(c_6068,plain,
    ( sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13) = k2_mcart_1(sK13)
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5998,c_31])).

cnf(c_6421,plain,
    ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),k2_mcart_1(sK13)) = sK13
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6068,c_5998])).

cnf(c_37,negated_conjecture,
    ( ~ m1_subset_1(X0,sK11)
    | ~ m1_subset_1(X1,sK10)
    | ~ m1_subset_1(X2,sK9)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK13
    | sK12 = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_858,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK13
    | sK12 = X2
    | m1_subset_1(X2,sK11) != iProver_top
    | m1_subset_1(X1,sK10) != iProver_top
    | m1_subset_1(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6791,plain,
    ( k4_tarski(sK13,X0) != sK13
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | sK12 = X0
    | m1_subset_1(X0,sK11) != iProver_top
    | m1_subset_1(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK9) != iProver_top
    | m1_subset_1(k2_mcart_1(sK13),sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_6421,c_858])).

cnf(c_25612,plain,
    ( k4_tarski(sK13,X0) != sK13
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | sK12 = X0
    | m1_subset_1(X0,sK11) != iProver_top
    | m1_subset_1(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK9) != iProver_top
    | m1_subset_1(sK8(sK13),sK10) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25489,c_6791])).

cnf(c_6,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_102,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2493,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) != k1_xboole_0
    | k1_xboole_0 = sK11
    | k1_xboole_0 = sK10
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4510,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
    | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4511,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) = k1_xboole_0
    | r2_hidden(sK3(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
    | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4510])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8442,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),X0)
    | ~ r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8443,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),X0) != iProver_top
    | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8442])).

cnf(c_8445,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8443])).

cnf(c_23696,plain,
    ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5732,c_3633])).

cnf(c_24283,plain,
    ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | k2_zfmisc_1(sK9,sK10) = k1_xboole_0
    | sK11 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_23696,c_30])).

cnf(c_24521,plain,
    ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5732,c_3634])).

cnf(c_40471,plain,
    ( k1_xboole_0 = X0
    | k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24283,c_36,c_35,c_34,c_1221,c_24521])).

cnf(c_40472,plain,
    ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_40471])).

cnf(c_40694,plain,
    ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13 ),
    inference(superposition,[status(thm)],[c_40472,c_36])).

cnf(c_32,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40781,plain,
    ( sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13) = k1_mcart_1(sK13) ),
    inference(superposition,[status(thm)],[c_40694,c_32])).

cnf(c_25488,plain,
    ( k1_mcart_1(sK13) = sK7(sK13) ),
    inference(superposition,[status(thm)],[c_25374,c_32])).

cnf(c_42013,plain,
    ( sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13) = sK7(sK13) ),
    inference(light_normalisation,[status(thm)],[c_40781,c_25488])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_870,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_42025,plain,
    ( r2_hidden(sK7(sK13),k2_zfmisc_1(sK9,sK10)) = iProver_top
    | r2_hidden(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_42013,c_870])).

cnf(c_46739,plain,
    ( ~ r2_hidden(sK3(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_46740,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46739])).

cnf(c_19,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_865,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3866,plain,
    ( m1_subset_1(sK5(X0,X1,X2),X0) = iProver_top
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_870,c_865])).

cnf(c_6067,plain,
    ( sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13) = k1_mcart_1(sK13)
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5998,c_32])).

cnf(c_6308,plain,
    ( k4_tarski(k1_mcart_1(sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6067,c_5998])).

cnf(c_6307,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK13),k2_zfmisc_1(sK9,sK10)) = iProver_top
    | r2_hidden(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6067,c_870])).

cnf(c_9340,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK13),k2_zfmisc_1(sK9,sK10)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3862,c_6307])).

cnf(c_9350,plain,
    ( k4_tarski(sK5(sK9,sK10,k1_mcart_1(sK13)),sK6(sK9,sK10,k1_mcart_1(sK13))) = k1_mcart_1(sK13)
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9340,c_872])).

cnf(c_9691,plain,
    ( k4_tarski(sK5(sK9,sK10,k1_mcart_1(sK13)),sK6(sK9,sK10,k1_mcart_1(sK13))) = k1_mcart_1(sK13)
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9350,c_3635])).

cnf(c_22504,plain,
    ( k4_tarski(k1_mcart_1(sK13),X0) != sK13
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | sK12 = X0
    | m1_subset_1(X0,sK11) != iProver_top
    | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
    | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9691,c_858])).

cnf(c_22513,plain,
    ( sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13) = sK12
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | m1_subset_1(sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK11) != iProver_top
    | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
    | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6308,c_22504])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_863,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4757,plain,
    ( m1_subset_1(k6_mcart_1(sK9,sK10,sK11,sK13),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_863])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_860,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2010,plain,
    ( k6_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(k1_mcart_1(sK13))
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_857,c_860])).

cnf(c_45,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_46,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_394,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_930,plain,
    ( sK11 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK11 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_931,plain,
    ( sK11 != k1_xboole_0
    | k1_xboole_0 = sK11
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_945,plain,
    ( sK10 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_946,plain,
    ( sK10 != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_968,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_969,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_2482,plain,
    ( k6_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(k1_mcart_1(sK13)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2010,c_36,c_35,c_34,c_45,c_46,c_931,c_946,c_969])).

cnf(c_4772,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK13)),sK10) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4757,c_2482])).

cnf(c_22503,plain,
    ( sK6(sK9,sK10,k1_mcart_1(sK13)) = k2_mcart_1(k1_mcart_1(sK13))
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9691,c_31])).

cnf(c_6617,plain,
    ( k4_tarski(k1_mcart_1(sK13),k2_mcart_1(sK13)) = sK13
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6068,c_6308])).

cnf(c_22514,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | k2_mcart_1(sK13) = sK12
    | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
    | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top
    | m1_subset_1(k2_mcart_1(sK13),sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_6617,c_22504])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_861,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3100,plain,
    ( k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13)
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_857,c_861])).

cnf(c_3385,plain,
    ( k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3100,c_36,c_35,c_34,c_45,c_46,c_931,c_946,c_969])).

cnf(c_33,negated_conjecture,
    ( k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3387,plain,
    ( k2_mcart_1(sK13) != sK12 ),
    inference(demodulation,[status(thm)],[c_3385,c_33])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_862,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3697,plain,
    ( m1_subset_1(k7_mcart_1(sK9,sK10,sK11,sK13),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_862])).

cnf(c_3709,plain,
    ( m1_subset_1(k2_mcart_1(sK13),sK11) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3697,c_3385])).

cnf(c_22664,plain,
    ( m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top
    | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22514,c_3387,c_3709])).

cnf(c_22665,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
    | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_22664])).

cnf(c_22668,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK13)),sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_22503,c_22665])).

cnf(c_22671,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22513,c_4772,c_22668])).

cnf(c_25529,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | m1_subset_1(sK5(sK9,sK10,sK7(sK13)),sK9) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25488,c_22671])).

cnf(c_66134,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | r2_hidden(sK7(sK13),k2_zfmisc_1(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3866,c_25529])).

cnf(c_66491,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25612,c_36,c_35,c_34,c_102,c_2493,c_3862,c_4511,c_8445,c_42025,c_46740,c_66134])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_873,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_25487,plain,
    ( r2_hidden(sK8(sK13),X0) != iProver_top
    | r2_hidden(sK7(sK13),X1) != iProver_top
    | r2_hidden(sK13,k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25374,c_873])).

cnf(c_66555,plain,
    ( r2_hidden(sK8(sK13),sK11) != iProver_top
    | r2_hidden(sK7(sK13),k2_zfmisc_1(sK9,sK10)) != iProver_top
    | r2_hidden(sK13,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_66491,c_25487])).

cnf(c_3932,plain,
    ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_3709,c_864])).

cnf(c_918,plain,
    ( ~ r1_xboole_0(sK11,sK11)
    | k1_xboole_0 = sK11 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_919,plain,
    ( k1_xboole_0 = sK11
    | r1_xboole_0(sK11,sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_991,plain,
    ( r1_xboole_0(sK11,sK11)
    | r2_hidden(sK1(sK11,sK11),sK11) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_992,plain,
    ( r1_xboole_0(sK11,sK11) = iProver_top
    | r2_hidden(sK1(sK11,sK11),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_991])).

cnf(c_3302,plain,
    ( ~ r2_hidden(sK1(sK11,sK11),sK11)
    | ~ v1_xboole_0(sK11) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3303,plain,
    ( r2_hidden(sK1(sK11,sK11),sK11) != iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3302])).

cnf(c_3999,plain,
    ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3932,c_34,c_919,c_992,c_3303])).

cnf(c_25615,plain,
    ( r2_hidden(sK8(sK13),sK11) = iProver_top ),
    inference(demodulation,[status(thm)],[c_25489,c_3999])).

cnf(c_66679,plain,
    ( r2_hidden(sK13,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_66555,c_36,c_35,c_34,c_102,c_2493,c_3862,c_4511,c_8445,c_25615,c_42025,c_46740])).

cnf(c_878,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_882,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8893,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_882])).

cnf(c_66687,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_66679,c_8893])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:03:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.96/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.96/2.48  
% 15.96/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.96/2.48  
% 15.96/2.48  ------  iProver source info
% 15.96/2.48  
% 15.96/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.96/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.96/2.48  git: non_committed_changes: false
% 15.96/2.48  git: last_make_outside_of_git: false
% 15.96/2.48  
% 15.96/2.48  ------ 
% 15.96/2.48  
% 15.96/2.48  ------ Input Options
% 15.96/2.48  
% 15.96/2.48  --out_options                           all
% 15.96/2.48  --tptp_safe_out                         true
% 15.96/2.48  --problem_path                          ""
% 15.96/2.48  --include_path                          ""
% 15.96/2.48  --clausifier                            res/vclausify_rel
% 15.96/2.48  --clausifier_options                    ""
% 15.96/2.48  --stdin                                 false
% 15.96/2.48  --stats_out                             all
% 15.96/2.48  
% 15.96/2.48  ------ General Options
% 15.96/2.48  
% 15.96/2.48  --fof                                   false
% 15.96/2.48  --time_out_real                         305.
% 15.96/2.48  --time_out_virtual                      -1.
% 15.96/2.48  --symbol_type_check                     false
% 15.96/2.48  --clausify_out                          false
% 15.96/2.48  --sig_cnt_out                           false
% 15.96/2.48  --trig_cnt_out                          false
% 15.96/2.48  --trig_cnt_out_tolerance                1.
% 15.96/2.48  --trig_cnt_out_sk_spl                   false
% 15.96/2.48  --abstr_cl_out                          false
% 15.96/2.48  
% 15.96/2.48  ------ Global Options
% 15.96/2.48  
% 15.96/2.48  --schedule                              default
% 15.96/2.48  --add_important_lit                     false
% 15.96/2.48  --prop_solver_per_cl                    1000
% 15.96/2.48  --min_unsat_core                        false
% 15.96/2.48  --soft_assumptions                      false
% 15.96/2.48  --soft_lemma_size                       3
% 15.96/2.48  --prop_impl_unit_size                   0
% 15.96/2.48  --prop_impl_unit                        []
% 15.96/2.48  --share_sel_clauses                     true
% 15.96/2.48  --reset_solvers                         false
% 15.96/2.48  --bc_imp_inh                            [conj_cone]
% 15.96/2.48  --conj_cone_tolerance                   3.
% 15.96/2.48  --extra_neg_conj                        none
% 15.96/2.48  --large_theory_mode                     true
% 15.96/2.48  --prolific_symb_bound                   200
% 15.96/2.48  --lt_threshold                          2000
% 15.96/2.48  --clause_weak_htbl                      true
% 15.96/2.48  --gc_record_bc_elim                     false
% 15.96/2.48  
% 15.96/2.48  ------ Preprocessing Options
% 15.96/2.48  
% 15.96/2.48  --preprocessing_flag                    true
% 15.96/2.48  --time_out_prep_mult                    0.1
% 15.96/2.48  --splitting_mode                        input
% 15.96/2.48  --splitting_grd                         true
% 15.96/2.48  --splitting_cvd                         false
% 15.96/2.48  --splitting_cvd_svl                     false
% 15.96/2.48  --splitting_nvd                         32
% 15.96/2.48  --sub_typing                            true
% 15.96/2.48  --prep_gs_sim                           true
% 15.96/2.48  --prep_unflatten                        true
% 15.96/2.48  --prep_res_sim                          true
% 15.96/2.48  --prep_upred                            true
% 15.96/2.48  --prep_sem_filter                       exhaustive
% 15.96/2.48  --prep_sem_filter_out                   false
% 15.96/2.48  --pred_elim                             true
% 15.96/2.48  --res_sim_input                         true
% 15.96/2.48  --eq_ax_congr_red                       true
% 15.96/2.48  --pure_diseq_elim                       true
% 15.96/2.48  --brand_transform                       false
% 15.96/2.48  --non_eq_to_eq                          false
% 15.96/2.48  --prep_def_merge                        true
% 15.96/2.48  --prep_def_merge_prop_impl              false
% 15.96/2.48  --prep_def_merge_mbd                    true
% 15.96/2.48  --prep_def_merge_tr_red                 false
% 15.96/2.48  --prep_def_merge_tr_cl                  false
% 15.96/2.48  --smt_preprocessing                     true
% 15.96/2.48  --smt_ac_axioms                         fast
% 15.96/2.48  --preprocessed_out                      false
% 15.96/2.48  --preprocessed_stats                    false
% 15.96/2.48  
% 15.96/2.48  ------ Abstraction refinement Options
% 15.96/2.48  
% 15.96/2.48  --abstr_ref                             []
% 15.96/2.48  --abstr_ref_prep                        false
% 15.96/2.48  --abstr_ref_until_sat                   false
% 15.96/2.48  --abstr_ref_sig_restrict                funpre
% 15.96/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.96/2.48  --abstr_ref_under                       []
% 15.96/2.48  
% 15.96/2.48  ------ SAT Options
% 15.96/2.48  
% 15.96/2.48  --sat_mode                              false
% 15.96/2.48  --sat_fm_restart_options                ""
% 15.96/2.48  --sat_gr_def                            false
% 15.96/2.48  --sat_epr_types                         true
% 15.96/2.48  --sat_non_cyclic_types                  false
% 15.96/2.48  --sat_finite_models                     false
% 15.96/2.48  --sat_fm_lemmas                         false
% 15.96/2.48  --sat_fm_prep                           false
% 15.96/2.48  --sat_fm_uc_incr                        true
% 15.96/2.48  --sat_out_model                         small
% 15.96/2.48  --sat_out_clauses                       false
% 15.96/2.48  
% 15.96/2.48  ------ QBF Options
% 15.96/2.48  
% 15.96/2.48  --qbf_mode                              false
% 15.96/2.48  --qbf_elim_univ                         false
% 15.96/2.48  --qbf_dom_inst                          none
% 15.96/2.48  --qbf_dom_pre_inst                      false
% 15.96/2.48  --qbf_sk_in                             false
% 15.96/2.48  --qbf_pred_elim                         true
% 15.96/2.48  --qbf_split                             512
% 15.96/2.48  
% 15.96/2.48  ------ BMC1 Options
% 15.96/2.48  
% 15.96/2.48  --bmc1_incremental                      false
% 15.96/2.48  --bmc1_axioms                           reachable_all
% 15.96/2.48  --bmc1_min_bound                        0
% 15.96/2.48  --bmc1_max_bound                        -1
% 15.96/2.48  --bmc1_max_bound_default                -1
% 15.96/2.48  --bmc1_symbol_reachability              true
% 15.96/2.48  --bmc1_property_lemmas                  false
% 15.96/2.48  --bmc1_k_induction                      false
% 15.96/2.48  --bmc1_non_equiv_states                 false
% 15.96/2.48  --bmc1_deadlock                         false
% 15.96/2.48  --bmc1_ucm                              false
% 15.96/2.48  --bmc1_add_unsat_core                   none
% 15.96/2.48  --bmc1_unsat_core_children              false
% 15.96/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.96/2.48  --bmc1_out_stat                         full
% 15.96/2.48  --bmc1_ground_init                      false
% 15.96/2.48  --bmc1_pre_inst_next_state              false
% 15.96/2.48  --bmc1_pre_inst_state                   false
% 15.96/2.48  --bmc1_pre_inst_reach_state             false
% 15.96/2.48  --bmc1_out_unsat_core                   false
% 15.96/2.48  --bmc1_aig_witness_out                  false
% 15.96/2.48  --bmc1_verbose                          false
% 15.96/2.48  --bmc1_dump_clauses_tptp                false
% 15.96/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.96/2.48  --bmc1_dump_file                        -
% 15.96/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.96/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.96/2.48  --bmc1_ucm_extend_mode                  1
% 15.96/2.48  --bmc1_ucm_init_mode                    2
% 15.96/2.48  --bmc1_ucm_cone_mode                    none
% 15.96/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.96/2.48  --bmc1_ucm_relax_model                  4
% 15.96/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.96/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.96/2.48  --bmc1_ucm_layered_model                none
% 15.96/2.48  --bmc1_ucm_max_lemma_size               10
% 15.96/2.48  
% 15.96/2.48  ------ AIG Options
% 15.96/2.48  
% 15.96/2.48  --aig_mode                              false
% 15.96/2.48  
% 15.96/2.48  ------ Instantiation Options
% 15.96/2.48  
% 15.96/2.48  --instantiation_flag                    true
% 15.96/2.48  --inst_sos_flag                         true
% 15.96/2.48  --inst_sos_phase                        true
% 15.96/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.96/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.96/2.48  --inst_lit_sel_side                     num_symb
% 15.96/2.48  --inst_solver_per_active                1400
% 15.96/2.48  --inst_solver_calls_frac                1.
% 15.96/2.48  --inst_passive_queue_type               priority_queues
% 15.96/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.96/2.48  --inst_passive_queues_freq              [25;2]
% 15.96/2.48  --inst_dismatching                      true
% 15.96/2.48  --inst_eager_unprocessed_to_passive     true
% 15.96/2.48  --inst_prop_sim_given                   true
% 15.96/2.48  --inst_prop_sim_new                     false
% 15.96/2.48  --inst_subs_new                         false
% 15.96/2.48  --inst_eq_res_simp                      false
% 15.96/2.48  --inst_subs_given                       false
% 15.96/2.48  --inst_orphan_elimination               true
% 15.96/2.48  --inst_learning_loop_flag               true
% 15.96/2.48  --inst_learning_start                   3000
% 15.96/2.48  --inst_learning_factor                  2
% 15.96/2.48  --inst_start_prop_sim_after_learn       3
% 15.96/2.48  --inst_sel_renew                        solver
% 15.96/2.48  --inst_lit_activity_flag                true
% 15.96/2.48  --inst_restr_to_given                   false
% 15.96/2.48  --inst_activity_threshold               500
% 15.96/2.48  --inst_out_proof                        true
% 15.96/2.48  
% 15.96/2.48  ------ Resolution Options
% 15.96/2.48  
% 15.96/2.48  --resolution_flag                       true
% 15.96/2.48  --res_lit_sel                           adaptive
% 15.96/2.48  --res_lit_sel_side                      none
% 15.96/2.48  --res_ordering                          kbo
% 15.96/2.48  --res_to_prop_solver                    active
% 15.96/2.48  --res_prop_simpl_new                    false
% 15.96/2.48  --res_prop_simpl_given                  true
% 15.96/2.48  --res_passive_queue_type                priority_queues
% 15.96/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.96/2.48  --res_passive_queues_freq               [15;5]
% 15.96/2.48  --res_forward_subs                      full
% 15.96/2.48  --res_backward_subs                     full
% 15.96/2.48  --res_forward_subs_resolution           true
% 15.96/2.48  --res_backward_subs_resolution          true
% 15.96/2.48  --res_orphan_elimination                true
% 15.96/2.48  --res_time_limit                        2.
% 15.96/2.48  --res_out_proof                         true
% 15.96/2.48  
% 15.96/2.48  ------ Superposition Options
% 15.96/2.48  
% 15.96/2.48  --superposition_flag                    true
% 15.96/2.48  --sup_passive_queue_type                priority_queues
% 15.96/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.96/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.96/2.48  --demod_completeness_check              fast
% 15.96/2.48  --demod_use_ground                      true
% 15.96/2.48  --sup_to_prop_solver                    passive
% 15.96/2.48  --sup_prop_simpl_new                    true
% 15.96/2.48  --sup_prop_simpl_given                  true
% 15.96/2.48  --sup_fun_splitting                     true
% 15.96/2.48  --sup_smt_interval                      50000
% 15.96/2.48  
% 15.96/2.48  ------ Superposition Simplification Setup
% 15.96/2.48  
% 15.96/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.96/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.96/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.96/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.96/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.96/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.96/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.96/2.48  --sup_immed_triv                        [TrivRules]
% 15.96/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.96/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.96/2.48  --sup_immed_bw_main                     []
% 15.96/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.96/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.96/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.96/2.48  --sup_input_bw                          []
% 15.96/2.48  
% 15.96/2.48  ------ Combination Options
% 15.96/2.48  
% 15.96/2.48  --comb_res_mult                         3
% 15.96/2.48  --comb_sup_mult                         2
% 15.96/2.48  --comb_inst_mult                        10
% 15.96/2.48  
% 15.96/2.48  ------ Debug Options
% 15.96/2.48  
% 15.96/2.48  --dbg_backtrace                         false
% 15.96/2.48  --dbg_dump_prop_clauses                 false
% 15.96/2.48  --dbg_dump_prop_clauses_file            -
% 15.96/2.48  --dbg_out_stat                          false
% 15.96/2.48  ------ Parsing...
% 15.96/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.96/2.48  
% 15.96/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.96/2.48  
% 15.96/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.96/2.48  
% 15.96/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.96/2.48  ------ Proving...
% 15.96/2.48  ------ Problem Properties 
% 15.96/2.48  
% 15.96/2.48  
% 15.96/2.48  clauses                                 39
% 15.96/2.48  conjectures                             6
% 15.96/2.48  EPR                                     9
% 15.96/2.48  Horn                                    28
% 15.96/2.48  unary                                   13
% 15.96/2.48  binary                                  14
% 15.96/2.48  lits                                    89
% 15.96/2.48  lits eq                                 38
% 15.96/2.48  fd_pure                                 0
% 15.96/2.48  fd_pseudo                               0
% 15.96/2.48  fd_cond                                 6
% 15.96/2.48  fd_pseudo_cond                          4
% 15.96/2.48  AC symbols                              0
% 15.96/2.48  
% 15.96/2.48  ------ Schedule dynamic 5 is on 
% 15.96/2.48  
% 15.96/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.96/2.48  
% 15.96/2.48  
% 15.96/2.48  ------ 
% 15.96/2.48  Current options:
% 15.96/2.48  ------ 
% 15.96/2.48  
% 15.96/2.48  ------ Input Options
% 15.96/2.48  
% 15.96/2.48  --out_options                           all
% 15.96/2.48  --tptp_safe_out                         true
% 15.96/2.48  --problem_path                          ""
% 15.96/2.48  --include_path                          ""
% 15.96/2.48  --clausifier                            res/vclausify_rel
% 15.96/2.48  --clausifier_options                    ""
% 15.96/2.48  --stdin                                 false
% 15.96/2.48  --stats_out                             all
% 15.96/2.48  
% 15.96/2.48  ------ General Options
% 15.96/2.48  
% 15.96/2.48  --fof                                   false
% 15.96/2.48  --time_out_real                         305.
% 15.96/2.48  --time_out_virtual                      -1.
% 15.96/2.48  --symbol_type_check                     false
% 15.96/2.48  --clausify_out                          false
% 15.96/2.48  --sig_cnt_out                           false
% 15.96/2.48  --trig_cnt_out                          false
% 15.96/2.48  --trig_cnt_out_tolerance                1.
% 15.96/2.48  --trig_cnt_out_sk_spl                   false
% 15.96/2.48  --abstr_cl_out                          false
% 15.96/2.48  
% 15.96/2.48  ------ Global Options
% 15.96/2.48  
% 15.96/2.48  --schedule                              default
% 15.96/2.48  --add_important_lit                     false
% 15.96/2.48  --prop_solver_per_cl                    1000
% 15.96/2.48  --min_unsat_core                        false
% 15.96/2.48  --soft_assumptions                      false
% 15.96/2.48  --soft_lemma_size                       3
% 15.96/2.48  --prop_impl_unit_size                   0
% 15.96/2.48  --prop_impl_unit                        []
% 15.96/2.48  --share_sel_clauses                     true
% 15.96/2.48  --reset_solvers                         false
% 15.96/2.48  --bc_imp_inh                            [conj_cone]
% 15.96/2.48  --conj_cone_tolerance                   3.
% 15.96/2.48  --extra_neg_conj                        none
% 15.96/2.48  --large_theory_mode                     true
% 15.96/2.48  --prolific_symb_bound                   200
% 15.96/2.48  --lt_threshold                          2000
% 15.96/2.48  --clause_weak_htbl                      true
% 15.96/2.48  --gc_record_bc_elim                     false
% 15.96/2.48  
% 15.96/2.48  ------ Preprocessing Options
% 15.96/2.48  
% 15.96/2.48  --preprocessing_flag                    true
% 15.96/2.48  --time_out_prep_mult                    0.1
% 15.96/2.48  --splitting_mode                        input
% 15.96/2.48  --splitting_grd                         true
% 15.96/2.48  --splitting_cvd                         false
% 15.96/2.48  --splitting_cvd_svl                     false
% 15.96/2.48  --splitting_nvd                         32
% 15.96/2.48  --sub_typing                            true
% 15.96/2.48  --prep_gs_sim                           true
% 15.96/2.48  --prep_unflatten                        true
% 15.96/2.48  --prep_res_sim                          true
% 15.96/2.48  --prep_upred                            true
% 15.96/2.48  --prep_sem_filter                       exhaustive
% 15.96/2.48  --prep_sem_filter_out                   false
% 15.96/2.48  --pred_elim                             true
% 15.96/2.48  --res_sim_input                         true
% 15.96/2.48  --eq_ax_congr_red                       true
% 15.96/2.48  --pure_diseq_elim                       true
% 15.96/2.48  --brand_transform                       false
% 15.96/2.48  --non_eq_to_eq                          false
% 15.96/2.48  --prep_def_merge                        true
% 15.96/2.48  --prep_def_merge_prop_impl              false
% 15.96/2.48  --prep_def_merge_mbd                    true
% 15.96/2.48  --prep_def_merge_tr_red                 false
% 15.96/2.48  --prep_def_merge_tr_cl                  false
% 15.96/2.48  --smt_preprocessing                     true
% 15.96/2.48  --smt_ac_axioms                         fast
% 15.96/2.48  --preprocessed_out                      false
% 15.96/2.48  --preprocessed_stats                    false
% 15.96/2.48  
% 15.96/2.48  ------ Abstraction refinement Options
% 15.96/2.48  
% 15.96/2.48  --abstr_ref                             []
% 15.96/2.48  --abstr_ref_prep                        false
% 15.96/2.48  --abstr_ref_until_sat                   false
% 15.96/2.48  --abstr_ref_sig_restrict                funpre
% 15.96/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.96/2.48  --abstr_ref_under                       []
% 15.96/2.48  
% 15.96/2.48  ------ SAT Options
% 15.96/2.48  
% 15.96/2.48  --sat_mode                              false
% 15.96/2.48  --sat_fm_restart_options                ""
% 15.96/2.48  --sat_gr_def                            false
% 15.96/2.48  --sat_epr_types                         true
% 15.96/2.48  --sat_non_cyclic_types                  false
% 15.96/2.48  --sat_finite_models                     false
% 15.96/2.48  --sat_fm_lemmas                         false
% 15.96/2.48  --sat_fm_prep                           false
% 15.96/2.48  --sat_fm_uc_incr                        true
% 15.96/2.48  --sat_out_model                         small
% 15.96/2.48  --sat_out_clauses                       false
% 15.96/2.48  
% 15.96/2.48  ------ QBF Options
% 15.96/2.48  
% 15.96/2.48  --qbf_mode                              false
% 15.96/2.48  --qbf_elim_univ                         false
% 15.96/2.48  --qbf_dom_inst                          none
% 15.96/2.48  --qbf_dom_pre_inst                      false
% 15.96/2.48  --qbf_sk_in                             false
% 15.96/2.48  --qbf_pred_elim                         true
% 15.96/2.48  --qbf_split                             512
% 15.96/2.48  
% 15.96/2.48  ------ BMC1 Options
% 15.96/2.48  
% 15.96/2.48  --bmc1_incremental                      false
% 15.96/2.48  --bmc1_axioms                           reachable_all
% 15.96/2.48  --bmc1_min_bound                        0
% 15.96/2.48  --bmc1_max_bound                        -1
% 15.96/2.48  --bmc1_max_bound_default                -1
% 15.96/2.48  --bmc1_symbol_reachability              true
% 15.96/2.48  --bmc1_property_lemmas                  false
% 15.96/2.48  --bmc1_k_induction                      false
% 15.96/2.48  --bmc1_non_equiv_states                 false
% 15.96/2.48  --bmc1_deadlock                         false
% 15.96/2.48  --bmc1_ucm                              false
% 15.96/2.48  --bmc1_add_unsat_core                   none
% 15.96/2.48  --bmc1_unsat_core_children              false
% 15.96/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.96/2.48  --bmc1_out_stat                         full
% 15.96/2.48  --bmc1_ground_init                      false
% 15.96/2.48  --bmc1_pre_inst_next_state              false
% 15.96/2.48  --bmc1_pre_inst_state                   false
% 15.96/2.48  --bmc1_pre_inst_reach_state             false
% 15.96/2.48  --bmc1_out_unsat_core                   false
% 15.96/2.48  --bmc1_aig_witness_out                  false
% 15.96/2.48  --bmc1_verbose                          false
% 15.96/2.48  --bmc1_dump_clauses_tptp                false
% 15.96/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.96/2.48  --bmc1_dump_file                        -
% 15.96/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.96/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.96/2.48  --bmc1_ucm_extend_mode                  1
% 15.96/2.48  --bmc1_ucm_init_mode                    2
% 15.96/2.48  --bmc1_ucm_cone_mode                    none
% 15.96/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.96/2.48  --bmc1_ucm_relax_model                  4
% 15.96/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.96/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.96/2.48  --bmc1_ucm_layered_model                none
% 15.96/2.48  --bmc1_ucm_max_lemma_size               10
% 15.96/2.48  
% 15.96/2.48  ------ AIG Options
% 15.96/2.48  
% 15.96/2.48  --aig_mode                              false
% 15.96/2.48  
% 15.96/2.48  ------ Instantiation Options
% 15.96/2.48  
% 15.96/2.48  --instantiation_flag                    true
% 15.96/2.48  --inst_sos_flag                         true
% 15.96/2.48  --inst_sos_phase                        true
% 15.96/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.96/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.96/2.48  --inst_lit_sel_side                     none
% 15.96/2.48  --inst_solver_per_active                1400
% 15.96/2.48  --inst_solver_calls_frac                1.
% 15.96/2.48  --inst_passive_queue_type               priority_queues
% 15.96/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.96/2.48  --inst_passive_queues_freq              [25;2]
% 15.96/2.48  --inst_dismatching                      true
% 15.96/2.48  --inst_eager_unprocessed_to_passive     true
% 15.96/2.48  --inst_prop_sim_given                   true
% 15.96/2.48  --inst_prop_sim_new                     false
% 15.96/2.48  --inst_subs_new                         false
% 15.96/2.48  --inst_eq_res_simp                      false
% 15.96/2.48  --inst_subs_given                       false
% 15.96/2.48  --inst_orphan_elimination               true
% 15.96/2.48  --inst_learning_loop_flag               true
% 15.96/2.48  --inst_learning_start                   3000
% 15.96/2.48  --inst_learning_factor                  2
% 15.96/2.48  --inst_start_prop_sim_after_learn       3
% 15.96/2.48  --inst_sel_renew                        solver
% 15.96/2.48  --inst_lit_activity_flag                true
% 15.96/2.48  --inst_restr_to_given                   false
% 15.96/2.48  --inst_activity_threshold               500
% 15.96/2.48  --inst_out_proof                        true
% 15.96/2.48  
% 15.96/2.48  ------ Resolution Options
% 15.96/2.48  
% 15.96/2.48  --resolution_flag                       false
% 15.96/2.48  --res_lit_sel                           adaptive
% 15.96/2.48  --res_lit_sel_side                      none
% 15.96/2.48  --res_ordering                          kbo
% 15.96/2.48  --res_to_prop_solver                    active
% 15.96/2.48  --res_prop_simpl_new                    false
% 15.96/2.48  --res_prop_simpl_given                  true
% 15.96/2.48  --res_passive_queue_type                priority_queues
% 15.96/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.96/2.48  --res_passive_queues_freq               [15;5]
% 15.96/2.48  --res_forward_subs                      full
% 15.96/2.48  --res_backward_subs                     full
% 15.96/2.48  --res_forward_subs_resolution           true
% 15.96/2.48  --res_backward_subs_resolution          true
% 15.96/2.48  --res_orphan_elimination                true
% 15.96/2.48  --res_time_limit                        2.
% 15.96/2.48  --res_out_proof                         true
% 15.96/2.48  
% 15.96/2.48  ------ Superposition Options
% 15.96/2.48  
% 15.96/2.48  --superposition_flag                    true
% 15.96/2.48  --sup_passive_queue_type                priority_queues
% 15.96/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.96/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.96/2.48  --demod_completeness_check              fast
% 15.96/2.48  --demod_use_ground                      true
% 15.96/2.48  --sup_to_prop_solver                    passive
% 15.96/2.48  --sup_prop_simpl_new                    true
% 15.96/2.48  --sup_prop_simpl_given                  true
% 15.96/2.48  --sup_fun_splitting                     true
% 15.96/2.48  --sup_smt_interval                      50000
% 15.96/2.48  
% 15.96/2.48  ------ Superposition Simplification Setup
% 15.96/2.48  
% 15.96/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.96/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.96/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.96/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.96/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.96/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.96/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.96/2.48  --sup_immed_triv                        [TrivRules]
% 15.96/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.96/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.96/2.48  --sup_immed_bw_main                     []
% 15.96/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.96/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.96/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.96/2.48  --sup_input_bw                          []
% 15.96/2.48  
% 15.96/2.48  ------ Combination Options
% 15.96/2.48  
% 15.96/2.48  --comb_res_mult                         3
% 15.96/2.48  --comb_sup_mult                         2
% 15.96/2.48  --comb_inst_mult                        10
% 15.96/2.48  
% 15.96/2.48  ------ Debug Options
% 15.96/2.48  
% 15.96/2.48  --dbg_backtrace                         false
% 15.96/2.48  --dbg_dump_prop_clauses                 false
% 15.96/2.48  --dbg_dump_prop_clauses_file            -
% 15.96/2.48  --dbg_out_stat                          false
% 15.96/2.48  
% 15.96/2.48  
% 15.96/2.48  
% 15.96/2.48  
% 15.96/2.48  ------ Proving...
% 15.96/2.48  
% 15.96/2.48  
% 15.96/2.48  % SZS status Theorem for theBenchmark.p
% 15.96/2.48  
% 15.96/2.48   Resolution empty clause
% 15.96/2.48  
% 15.96/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.96/2.48  
% 15.96/2.48  fof(f18,conjecture,(
% 15.96/2.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f19,negated_conjecture,(
% 15.96/2.48    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 15.96/2.48    inference(negated_conjecture,[],[f18])).
% 15.96/2.48  
% 15.96/2.48  fof(f31,plain,(
% 15.96/2.48    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 15.96/2.48    inference(ennf_transformation,[],[f19])).
% 15.96/2.48  
% 15.96/2.48  fof(f32,plain,(
% 15.96/2.48    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 15.96/2.48    inference(flattening,[],[f31])).
% 15.96/2.48  
% 15.96/2.48  fof(f49,plain,(
% 15.96/2.48    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 & k1_xboole_0 != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & ! [X5] : (! [X6] : (! [X7] : (sK12 = X7 | k3_mcart_1(X5,X6,X7) != sK13 | ~m1_subset_1(X7,sK11)) | ~m1_subset_1(X6,sK10)) | ~m1_subset_1(X5,sK9)) & m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11)))),
% 15.96/2.48    introduced(choice_axiom,[])).
% 15.96/2.48  
% 15.96/2.48  fof(f50,plain,(
% 15.96/2.48    k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 & k1_xboole_0 != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & ! [X5] : (! [X6] : (! [X7] : (sK12 = X7 | k3_mcart_1(X5,X6,X7) != sK13 | ~m1_subset_1(X7,sK11)) | ~m1_subset_1(X6,sK10)) | ~m1_subset_1(X5,sK9)) & m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11))),
% 15.96/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f32,f49])).
% 15.96/2.48  
% 15.96/2.48  fof(f87,plain,(
% 15.96/2.48    m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11))),
% 15.96/2.48    inference(cnf_transformation,[],[f50])).
% 15.96/2.48  
% 15.96/2.48  fof(f11,axiom,(
% 15.96/2.48    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f73,plain,(
% 15.96/2.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f11])).
% 15.96/2.48  
% 15.96/2.48  fof(f105,plain,(
% 15.96/2.48    m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))),
% 15.96/2.48    inference(definition_unfolding,[],[f87,f73])).
% 15.96/2.48  
% 15.96/2.48  fof(f9,axiom,(
% 15.96/2.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f26,plain,(
% 15.96/2.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 15.96/2.48    inference(ennf_transformation,[],[f9])).
% 15.96/2.48  
% 15.96/2.48  fof(f27,plain,(
% 15.96/2.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 15.96/2.48    inference(flattening,[],[f26])).
% 15.96/2.48  
% 15.96/2.48  fof(f71,plain,(
% 15.96/2.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f27])).
% 15.96/2.48  
% 15.96/2.48  fof(f5,axiom,(
% 15.96/2.48    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f23,plain,(
% 15.96/2.48    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 15.96/2.48    inference(ennf_transformation,[],[f5])).
% 15.96/2.48  
% 15.96/2.48  fof(f45,plain,(
% 15.96/2.48    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK7(X0),sK8(X0)) = X0)),
% 15.96/2.48    introduced(choice_axiom,[])).
% 15.96/2.48  
% 15.96/2.48  fof(f46,plain,(
% 15.96/2.48    ! [X0,X1,X2] : (k4_tarski(sK7(X0),sK8(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 15.96/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f23,f45])).
% 15.96/2.48  
% 15.96/2.48  fof(f66,plain,(
% 15.96/2.48    ( ! [X2,X0,X1] : (k4_tarski(sK7(X0),sK8(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 15.96/2.48    inference(cnf_transformation,[],[f46])).
% 15.96/2.48  
% 15.96/2.48  fof(f2,axiom,(
% 15.96/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f20,plain,(
% 15.96/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.96/2.48    inference(rectify,[],[f2])).
% 15.96/2.48  
% 15.96/2.48  fof(f21,plain,(
% 15.96/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 15.96/2.48    inference(ennf_transformation,[],[f20])).
% 15.96/2.48  
% 15.96/2.48  fof(f37,plain,(
% 15.96/2.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 15.96/2.48    introduced(choice_axiom,[])).
% 15.96/2.48  
% 15.96/2.48  fof(f38,plain,(
% 15.96/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 15.96/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f37])).
% 15.96/2.48  
% 15.96/2.48  fof(f53,plain,(
% 15.96/2.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f38])).
% 15.96/2.48  
% 15.96/2.48  fof(f1,axiom,(
% 15.96/2.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f33,plain,(
% 15.96/2.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 15.96/2.48    inference(nnf_transformation,[],[f1])).
% 15.96/2.48  
% 15.96/2.48  fof(f34,plain,(
% 15.96/2.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.96/2.48    inference(rectify,[],[f33])).
% 15.96/2.48  
% 15.96/2.48  fof(f35,plain,(
% 15.96/2.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 15.96/2.48    introduced(choice_axiom,[])).
% 15.96/2.48  
% 15.96/2.48  fof(f36,plain,(
% 15.96/2.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.96/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 15.96/2.48  
% 15.96/2.48  fof(f51,plain,(
% 15.96/2.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f36])).
% 15.96/2.48  
% 15.96/2.48  fof(f6,axiom,(
% 15.96/2.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f24,plain,(
% 15.96/2.48    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 15.96/2.48    inference(ennf_transformation,[],[f6])).
% 15.96/2.48  
% 15.96/2.48  fof(f67,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f24])).
% 15.96/2.48  
% 15.96/2.48  fof(f3,axiom,(
% 15.96/2.48    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f22,plain,(
% 15.96/2.48    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 15.96/2.48    inference(ennf_transformation,[],[f3])).
% 15.96/2.48  
% 15.96/2.48  fof(f57,plain,(
% 15.96/2.48    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 15.96/2.48    inference(cnf_transformation,[],[f22])).
% 15.96/2.48  
% 15.96/2.48  fof(f16,axiom,(
% 15.96/2.48    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f47,plain,(
% 15.96/2.48    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 15.96/2.48    inference(nnf_transformation,[],[f16])).
% 15.96/2.48  
% 15.96/2.48  fof(f48,plain,(
% 15.96/2.48    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.96/2.48    inference(flattening,[],[f47])).
% 15.96/2.48  
% 15.96/2.48  fof(f80,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.96/2.48    inference(cnf_transformation,[],[f48])).
% 15.96/2.48  
% 15.96/2.48  fof(f12,axiom,(
% 15.96/2.48    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f74,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f12])).
% 15.96/2.48  
% 15.96/2.48  fof(f93,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 15.96/2.48    inference(definition_unfolding,[],[f74,f73])).
% 15.96/2.48  
% 15.96/2.48  fof(f103,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.96/2.48    inference(definition_unfolding,[],[f80,f93])).
% 15.96/2.48  
% 15.96/2.48  fof(f89,plain,(
% 15.96/2.48    k1_xboole_0 != sK9),
% 15.96/2.48    inference(cnf_transformation,[],[f50])).
% 15.96/2.48  
% 15.96/2.48  fof(f90,plain,(
% 15.96/2.48    k1_xboole_0 != sK10),
% 15.96/2.48    inference(cnf_transformation,[],[f50])).
% 15.96/2.48  
% 15.96/2.48  fof(f91,plain,(
% 15.96/2.48    k1_xboole_0 != sK11),
% 15.96/2.48    inference(cnf_transformation,[],[f50])).
% 15.96/2.48  
% 15.96/2.48  fof(f17,axiom,(
% 15.96/2.48    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f86,plain,(
% 15.96/2.48    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 15.96/2.48    inference(cnf_transformation,[],[f17])).
% 15.96/2.48  
% 15.96/2.48  fof(f4,axiom,(
% 15.96/2.48    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f39,plain,(
% 15.96/2.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 15.96/2.48    inference(nnf_transformation,[],[f4])).
% 15.96/2.48  
% 15.96/2.48  fof(f40,plain,(
% 15.96/2.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 15.96/2.48    inference(rectify,[],[f39])).
% 15.96/2.48  
% 15.96/2.48  fof(f43,plain,(
% 15.96/2.48    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 15.96/2.48    introduced(choice_axiom,[])).
% 15.96/2.48  
% 15.96/2.48  fof(f42,plain,(
% 15.96/2.48    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 15.96/2.48    introduced(choice_axiom,[])).
% 15.96/2.48  
% 15.96/2.48  fof(f41,plain,(
% 15.96/2.48    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 15.96/2.48    introduced(choice_axiom,[])).
% 15.96/2.48  
% 15.96/2.48  fof(f44,plain,(
% 15.96/2.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 15.96/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f40,f43,f42,f41])).
% 15.96/2.48  
% 15.96/2.48  fof(f60,plain,(
% 15.96/2.48    ( ! [X2,X0,X8,X1] : (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 15.96/2.48    inference(cnf_transformation,[],[f44])).
% 15.96/2.48  
% 15.96/2.48  fof(f109,plain,(
% 15.96/2.48    ( ! [X0,X8,X1] : (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 15.96/2.48    inference(equality_resolution,[],[f60])).
% 15.96/2.48  
% 15.96/2.48  fof(f88,plain,(
% 15.96/2.48    ( ! [X6,X7,X5] : (sK12 = X7 | k3_mcart_1(X5,X6,X7) != sK13 | ~m1_subset_1(X7,sK11) | ~m1_subset_1(X6,sK10) | ~m1_subset_1(X5,sK9)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f50])).
% 15.96/2.48  
% 15.96/2.48  fof(f10,axiom,(
% 15.96/2.48    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f72,plain,(
% 15.96/2.48    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f10])).
% 15.96/2.48  
% 15.96/2.48  fof(f104,plain,(
% 15.96/2.48    ( ! [X6,X7,X5] : (sK12 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK13 | ~m1_subset_1(X7,sK11) | ~m1_subset_1(X6,sK10) | ~m1_subset_1(X5,sK9)) )),
% 15.96/2.48    inference(definition_unfolding,[],[f88,f72])).
% 15.96/2.48  
% 15.96/2.48  fof(f56,plain,(
% 15.96/2.48    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f22])).
% 15.96/2.48  
% 15.96/2.48  fof(f106,plain,(
% 15.96/2.48    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 15.96/2.48    inference(equality_resolution,[],[f56])).
% 15.96/2.48  
% 15.96/2.48  fof(f62,plain,(
% 15.96/2.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f44])).
% 15.96/2.48  
% 15.96/2.48  fof(f55,plain,(
% 15.96/2.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f38])).
% 15.96/2.48  
% 15.96/2.48  fof(f85,plain,(
% 15.96/2.48    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 15.96/2.48    inference(cnf_transformation,[],[f17])).
% 15.96/2.48  
% 15.96/2.48  fof(f58,plain,(
% 15.96/2.48    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 15.96/2.48    inference(cnf_transformation,[],[f44])).
% 15.96/2.48  
% 15.96/2.48  fof(f111,plain,(
% 15.96/2.48    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 15.96/2.48    inference(equality_resolution,[],[f58])).
% 15.96/2.48  
% 15.96/2.48  fof(f8,axiom,(
% 15.96/2.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f25,plain,(
% 15.96/2.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 15.96/2.48    inference(ennf_transformation,[],[f8])).
% 15.96/2.48  
% 15.96/2.48  fof(f70,plain,(
% 15.96/2.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f25])).
% 15.96/2.48  
% 15.96/2.48  fof(f13,axiom,(
% 15.96/2.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f28,plain,(
% 15.96/2.48    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 15.96/2.48    inference(ennf_transformation,[],[f13])).
% 15.96/2.48  
% 15.96/2.48  fof(f75,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 15.96/2.48    inference(cnf_transformation,[],[f28])).
% 15.96/2.48  
% 15.96/2.48  fof(f94,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 15.96/2.48    inference(definition_unfolding,[],[f75,f73])).
% 15.96/2.48  
% 15.96/2.48  fof(f15,axiom,(
% 15.96/2.48    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f30,plain,(
% 15.96/2.48    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 15.96/2.48    inference(ennf_transformation,[],[f15])).
% 15.96/2.48  
% 15.96/2.48  fof(f78,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.96/2.48    inference(cnf_transformation,[],[f30])).
% 15.96/2.48  
% 15.96/2.48  fof(f97,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.96/2.48    inference(definition_unfolding,[],[f78,f73])).
% 15.96/2.48  
% 15.96/2.48  fof(f81,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 15.96/2.48    inference(cnf_transformation,[],[f48])).
% 15.96/2.48  
% 15.96/2.48  fof(f102,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 15.96/2.48    inference(definition_unfolding,[],[f81,f93])).
% 15.96/2.48  
% 15.96/2.48  fof(f115,plain,(
% 15.96/2.48    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 15.96/2.48    inference(equality_resolution,[],[f102])).
% 15.96/2.48  
% 15.96/2.48  fof(f79,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.96/2.48    inference(cnf_transformation,[],[f30])).
% 15.96/2.48  
% 15.96/2.48  fof(f96,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 15.96/2.48    inference(definition_unfolding,[],[f79,f73])).
% 15.96/2.48  
% 15.96/2.48  fof(f92,plain,(
% 15.96/2.48    k7_mcart_1(sK9,sK10,sK11,sK13) != sK12),
% 15.96/2.48    inference(cnf_transformation,[],[f50])).
% 15.96/2.48  
% 15.96/2.48  fof(f14,axiom,(
% 15.96/2.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 15.96/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.48  
% 15.96/2.48  fof(f29,plain,(
% 15.96/2.48    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 15.96/2.48    inference(ennf_transformation,[],[f14])).
% 15.96/2.48  
% 15.96/2.48  fof(f76,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 15.96/2.48    inference(cnf_transformation,[],[f29])).
% 15.96/2.48  
% 15.96/2.48  fof(f95,plain,(
% 15.96/2.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 15.96/2.48    inference(definition_unfolding,[],[f76,f73])).
% 15.96/2.48  
% 15.96/2.48  fof(f61,plain,(
% 15.96/2.48    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 15.96/2.48    inference(cnf_transformation,[],[f44])).
% 15.96/2.48  
% 15.96/2.48  fof(f107,plain,(
% 15.96/2.48    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 15.96/2.48    inference(equality_resolution,[],[f61])).
% 15.96/2.48  
% 15.96/2.48  fof(f108,plain,(
% 15.96/2.48    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 15.96/2.48    inference(equality_resolution,[],[f107])).
% 15.96/2.48  
% 15.96/2.48  cnf(c_38,negated_conjecture,
% 15.96/2.48      ( m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
% 15.96/2.48      inference(cnf_transformation,[],[f105]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_857,plain,
% 15.96/2.48      ( m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_20,plain,
% 15.96/2.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.96/2.48      inference(cnf_transformation,[],[f71]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_864,plain,
% 15.96/2.48      ( m1_subset_1(X0,X1) != iProver_top
% 15.96/2.48      | r2_hidden(X0,X1) = iProver_top
% 15.96/2.48      | v1_xboole_0(X1) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3862,plain,
% 15.96/2.48      ( r2_hidden(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
% 15.96/2.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_857,c_864]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_15,plain,
% 15.96/2.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK7(X0),sK8(X0)) = X0 ),
% 15.96/2.48      inference(cnf_transformation,[],[f66]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_869,plain,
% 15.96/2.48      ( k4_tarski(sK7(X0),sK8(X0)) = X0
% 15.96/2.48      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3929,plain,
% 15.96/2.48      ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13
% 15.96/2.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3862,c_869]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_4,plain,
% 15.96/2.48      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 15.96/2.48      inference(cnf_transformation,[],[f53]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_880,plain,
% 15.96/2.48      ( r1_xboole_0(X0,X1) = iProver_top
% 15.96/2.48      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_1,plain,
% 15.96/2.48      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 15.96/2.48      inference(cnf_transformation,[],[f51]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_883,plain,
% 15.96/2.48      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3113,plain,
% 15.96/2.48      ( r1_xboole_0(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_880,c_883]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_17,plain,
% 15.96/2.48      ( ~ r1_xboole_0(X0,X1)
% 15.96/2.48      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 15.96/2.48      inference(cnf_transformation,[],[f67]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_867,plain,
% 15.96/2.48      ( r1_xboole_0(X0,X1) != iProver_top
% 15.96/2.48      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_5,plain,
% 15.96/2.48      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 15.96/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_879,plain,
% 15.96/2.48      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_2540,plain,
% 15.96/2.48      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X0) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_867,c_879]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_2556,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 15.96/2.48      | r1_xboole_0(X0,X0) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_867,c_2540]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3633,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 15.96/2.48      | v1_xboole_0(X0) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3113,c_2556]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_23699,plain,
% 15.96/2.48      ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0),X1) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3929,c_3633]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_30,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 15.96/2.48      | k1_xboole_0 = X0
% 15.96/2.48      | k1_xboole_0 = X2
% 15.96/2.48      | k1_xboole_0 = X1
% 15.96/2.48      | k1_xboole_0 = X3 ),
% 15.96/2.48      inference(cnf_transformation,[],[f103]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_23987,plain,
% 15.96/2.48      ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(sK9,sK10) = k1_xboole_0
% 15.96/2.48      | sK11 = k1_xboole_0
% 15.96/2.48      | k1_xboole_0 = X0
% 15.96/2.48      | k1_xboole_0 = X1 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_23699,c_30]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_36,negated_conjecture,
% 15.96/2.48      ( k1_xboole_0 != sK9 ),
% 15.96/2.48      inference(cnf_transformation,[],[f89]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_35,negated_conjecture,
% 15.96/2.48      ( k1_xboole_0 != sK10 ),
% 15.96/2.48      inference(cnf_transformation,[],[f90]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_34,negated_conjecture,
% 15.96/2.48      ( k1_xboole_0 != sK11 ),
% 15.96/2.48      inference(cnf_transformation,[],[f91]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_955,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,X0),X1),X2) != k1_xboole_0
% 15.96/2.48      | k1_xboole_0 = X0
% 15.96/2.48      | k1_xboole_0 = X1
% 15.96/2.48      | k1_xboole_0 = X2
% 15.96/2.48      | k1_xboole_0 = sK9 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_30]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_1077,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),X0),X1) != k1_xboole_0
% 15.96/2.48      | k1_xboole_0 = X0
% 15.96/2.48      | k1_xboole_0 = X1
% 15.96/2.48      | k1_xboole_0 = sK10
% 15.96/2.48      | k1_xboole_0 = sK9 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_955]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_1221,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0) != k1_xboole_0
% 15.96/2.48      | k1_xboole_0 = X0
% 15.96/2.48      | k1_xboole_0 = sK11
% 15.96/2.48      | k1_xboole_0 = sK10
% 15.96/2.48      | k1_xboole_0 = sK9 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_1077]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3634,plain,
% 15.96/2.48      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3113,c_2540]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_24524,plain,
% 15.96/2.48      ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3929,c_3634]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_24875,plain,
% 15.96/2.48      ( k1_xboole_0 = X0 | k4_tarski(sK7(sK13),sK8(sK13)) = sK13 ),
% 15.96/2.48      inference(global_propositional_subsumption,
% 15.96/2.48                [status(thm)],
% 15.96/2.48                [c_23987,c_36,c_35,c_34,c_1221,c_24524]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_24876,plain,
% 15.96/2.48      ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13 | k1_xboole_0 = X0 ),
% 15.96/2.48      inference(renaming,[status(thm)],[c_24875]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_25374,plain,
% 15.96/2.48      ( k4_tarski(sK7(sK13),sK8(sK13)) = sK13 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_24876,c_36]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_31,plain,
% 15.96/2.48      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 15.96/2.48      inference(cnf_transformation,[],[f86]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_25489,plain,
% 15.96/2.48      ( k2_mcart_1(sK13) = sK8(sK13) ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_25374,c_31]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_12,plain,
% 15.96/2.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 15.96/2.48      | k4_tarski(sK5(X1,X2,X0),sK6(X1,X2,X0)) = X0 ),
% 15.96/2.48      inference(cnf_transformation,[],[f109]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_872,plain,
% 15.96/2.48      ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2
% 15.96/2.48      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_5732,plain,
% 15.96/2.48      ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 15.96/2.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3862,c_872]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3635,plain,
% 15.96/2.48      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3113,c_879]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_5998,plain,
% 15.96/2.48      ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_5732,c_3635]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_6068,plain,
% 15.96/2.48      ( sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13) = k2_mcart_1(sK13)
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_5998,c_31]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_6421,plain,
% 15.96/2.48      ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),k2_mcart_1(sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_6068,c_5998]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_37,negated_conjecture,
% 15.96/2.48      ( ~ m1_subset_1(X0,sK11)
% 15.96/2.48      | ~ m1_subset_1(X1,sK10)
% 15.96/2.48      | ~ m1_subset_1(X2,sK9)
% 15.96/2.48      | k4_tarski(k4_tarski(X2,X1),X0) != sK13
% 15.96/2.48      | sK12 = X0 ),
% 15.96/2.48      inference(cnf_transformation,[],[f104]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_858,plain,
% 15.96/2.48      ( k4_tarski(k4_tarski(X0,X1),X2) != sK13
% 15.96/2.48      | sK12 = X2
% 15.96/2.48      | m1_subset_1(X2,sK11) != iProver_top
% 15.96/2.48      | m1_subset_1(X1,sK10) != iProver_top
% 15.96/2.48      | m1_subset_1(X0,sK9) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_6791,plain,
% 15.96/2.48      ( k4_tarski(sK13,X0) != sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | sK12 = X0
% 15.96/2.48      | m1_subset_1(X0,sK11) != iProver_top
% 15.96/2.48      | m1_subset_1(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK9) != iProver_top
% 15.96/2.48      | m1_subset_1(k2_mcart_1(sK13),sK10) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_6421,c_858]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_25612,plain,
% 15.96/2.48      ( k4_tarski(sK13,X0) != sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | sK12 = X0
% 15.96/2.48      | m1_subset_1(X0,sK11) != iProver_top
% 15.96/2.48      | m1_subset_1(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK9) != iProver_top
% 15.96/2.48      | m1_subset_1(sK8(sK13),sK10) != iProver_top ),
% 15.96/2.48      inference(demodulation,[status(thm)],[c_25489,c_6791]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_6,plain,
% 15.96/2.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 15.96/2.48      inference(cnf_transformation,[],[f106]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_102,plain,
% 15.96/2.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_2493,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) != k1_xboole_0
% 15.96/2.48      | k1_xboole_0 = sK11
% 15.96/2.48      | k1_xboole_0 = sK10
% 15.96/2.48      | k1_xboole_0 = sK9 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_1221]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_10,plain,
% 15.96/2.48      ( r2_hidden(sK3(X0,X1,X2),X0)
% 15.96/2.48      | r2_hidden(sK2(X0,X1,X2),X2)
% 15.96/2.48      | k2_zfmisc_1(X0,X1) = X2 ),
% 15.96/2.48      inference(cnf_transformation,[],[f62]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_4510,plain,
% 15.96/2.48      ( r2_hidden(sK3(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
% 15.96/2.48      | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0)
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_10]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_4511,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) = k1_xboole_0
% 15.96/2.48      | r2_hidden(sK3(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
% 15.96/2.48      | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_4510]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_2,plain,
% 15.96/2.48      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 15.96/2.48      inference(cnf_transformation,[],[f55]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_8442,plain,
% 15.96/2.48      ( ~ r1_xboole_0(k1_xboole_0,X0)
% 15.96/2.48      | ~ r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),X0)
% 15.96/2.48      | ~ r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_2]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_8443,plain,
% 15.96/2.48      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 15.96/2.48      | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),X0) != iProver_top
% 15.96/2.48      | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_8442]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_8445,plain,
% 15.96/2.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 15.96/2.48      | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_8443]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_23696,plain,
% 15.96/2.48      ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0),X1) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_5732,c_3633]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_24283,plain,
% 15.96/2.48      ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(sK9,sK10) = k1_xboole_0
% 15.96/2.48      | sK11 = k1_xboole_0
% 15.96/2.48      | k1_xboole_0 = X0
% 15.96/2.48      | k1_xboole_0 = X1 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_23696,c_30]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_24521,plain,
% 15.96/2.48      ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),X0) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_5732,c_3634]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_40471,plain,
% 15.96/2.48      ( k1_xboole_0 = X0
% 15.96/2.48      | k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13 ),
% 15.96/2.48      inference(global_propositional_subsumption,
% 15.96/2.48                [status(thm)],
% 15.96/2.48                [c_24283,c_36,c_35,c_34,c_1221,c_24521]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_40472,plain,
% 15.96/2.48      ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 15.96/2.48      | k1_xboole_0 = X0 ),
% 15.96/2.48      inference(renaming,[status(thm)],[c_40471]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_40694,plain,
% 15.96/2.48      ( k4_tarski(sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_40472,c_36]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_32,plain,
% 15.96/2.48      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 15.96/2.48      inference(cnf_transformation,[],[f85]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_40781,plain,
% 15.96/2.48      ( sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13) = k1_mcart_1(sK13) ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_40694,c_32]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_25488,plain,
% 15.96/2.48      ( k1_mcart_1(sK13) = sK7(sK13) ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_25374,c_32]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_42013,plain,
% 15.96/2.48      ( sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13) = sK7(sK13) ),
% 15.96/2.48      inference(light_normalisation,[status(thm)],[c_40781,c_25488]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_14,plain,
% 15.96/2.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X1) ),
% 15.96/2.48      inference(cnf_transformation,[],[f111]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_870,plain,
% 15.96/2.48      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.96/2.48      | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_42025,plain,
% 15.96/2.48      ( r2_hidden(sK7(sK13),k2_zfmisc_1(sK9,sK10)) = iProver_top
% 15.96/2.48      | r2_hidden(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_42013,c_870]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_46739,plain,
% 15.96/2.48      ( ~ r2_hidden(sK3(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
% 15.96/2.48      | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_1]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_46740,plain,
% 15.96/2.48      ( r2_hidden(sK3(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top
% 15.96/2.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_46739]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_19,plain,
% 15.96/2.48      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 15.96/2.48      inference(cnf_transformation,[],[f70]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_865,plain,
% 15.96/2.48      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3866,plain,
% 15.96/2.48      ( m1_subset_1(sK5(X0,X1,X2),X0) = iProver_top
% 15.96/2.48      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_870,c_865]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_6067,plain,
% 15.96/2.48      ( sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13) = k1_mcart_1(sK13)
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_5998,c_32]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_6308,plain,
% 15.96/2.48      ( k4_tarski(k1_mcart_1(sK13),sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_6067,c_5998]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_6307,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | r2_hidden(k1_mcart_1(sK13),k2_zfmisc_1(sK9,sK10)) = iProver_top
% 15.96/2.48      | r2_hidden(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_6067,c_870]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_9340,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | r2_hidden(k1_mcart_1(sK13),k2_zfmisc_1(sK9,sK10)) = iProver_top
% 15.96/2.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3862,c_6307]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_9350,plain,
% 15.96/2.48      ( k4_tarski(sK5(sK9,sK10,k1_mcart_1(sK13)),sK6(sK9,sK10,k1_mcart_1(sK13))) = k1_mcart_1(sK13)
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_9340,c_872]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_9691,plain,
% 15.96/2.48      ( k4_tarski(sK5(sK9,sK10,k1_mcart_1(sK13)),sK6(sK9,sK10,k1_mcart_1(sK13))) = k1_mcart_1(sK13)
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_9350,c_3635]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_22504,plain,
% 15.96/2.48      ( k4_tarski(k1_mcart_1(sK13),X0) != sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | sK12 = X0
% 15.96/2.48      | m1_subset_1(X0,sK11) != iProver_top
% 15.96/2.48      | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
% 15.96/2.48      | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_9691,c_858]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_22513,plain,
% 15.96/2.48      ( sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13) = sK12
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | m1_subset_1(sK6(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK11) != iProver_top
% 15.96/2.48      | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
% 15.96/2.48      | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_6308,c_22504]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_21,plain,
% 15.96/2.48      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 15.96/2.48      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
% 15.96/2.48      inference(cnf_transformation,[],[f94]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_863,plain,
% 15.96/2.48      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 15.96/2.48      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_4757,plain,
% 15.96/2.48      ( m1_subset_1(k6_mcart_1(sK9,sK10,sK11,sK13),sK10) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_857,c_863]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_24,plain,
% 15.96/2.48      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 15.96/2.48      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 15.96/2.48      | k1_xboole_0 = X1
% 15.96/2.48      | k1_xboole_0 = X3
% 15.96/2.48      | k1_xboole_0 = X2 ),
% 15.96/2.48      inference(cnf_transformation,[],[f97]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_860,plain,
% 15.96/2.48      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 15.96/2.48      | k1_xboole_0 = X0
% 15.96/2.48      | k1_xboole_0 = X1
% 15.96/2.48      | k1_xboole_0 = X2
% 15.96/2.48      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_2010,plain,
% 15.96/2.48      ( k6_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(k1_mcart_1(sK13))
% 15.96/2.48      | sK11 = k1_xboole_0
% 15.96/2.48      | sK10 = k1_xboole_0
% 15.96/2.48      | sK9 = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_857,c_860]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_45,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 15.96/2.48      | k1_xboole_0 = k1_xboole_0 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_30]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_29,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 15.96/2.48      inference(cnf_transformation,[],[f115]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_46,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_29]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_394,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_930,plain,
% 15.96/2.48      ( sK11 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK11 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_394]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_931,plain,
% 15.96/2.48      ( sK11 != k1_xboole_0 | k1_xboole_0 = sK11 | k1_xboole_0 != k1_xboole_0 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_930]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_945,plain,
% 15.96/2.48      ( sK10 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK10 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_394]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_946,plain,
% 15.96/2.48      ( sK10 != k1_xboole_0 | k1_xboole_0 = sK10 | k1_xboole_0 != k1_xboole_0 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_945]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_968,plain,
% 15.96/2.48      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_394]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_969,plain,
% 15.96/2.48      ( sK9 != k1_xboole_0 | k1_xboole_0 = sK9 | k1_xboole_0 != k1_xboole_0 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_968]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_2482,plain,
% 15.96/2.48      ( k6_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(k1_mcart_1(sK13)) ),
% 15.96/2.48      inference(global_propositional_subsumption,
% 15.96/2.48                [status(thm)],
% 15.96/2.48                [c_2010,c_36,c_35,c_34,c_45,c_46,c_931,c_946,c_969]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_4772,plain,
% 15.96/2.48      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK13)),sK10) = iProver_top ),
% 15.96/2.48      inference(light_normalisation,[status(thm)],[c_4757,c_2482]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_22503,plain,
% 15.96/2.48      ( sK6(sK9,sK10,k1_mcart_1(sK13)) = k2_mcart_1(k1_mcart_1(sK13))
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_9691,c_31]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_6617,plain,
% 15.96/2.48      ( k4_tarski(k1_mcart_1(sK13),k2_mcart_1(sK13)) = sK13
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_6068,c_6308]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_22514,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | k2_mcart_1(sK13) = sK12
% 15.96/2.48      | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
% 15.96/2.48      | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top
% 15.96/2.48      | m1_subset_1(k2_mcart_1(sK13),sK11) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_6617,c_22504]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_23,plain,
% 15.96/2.48      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 15.96/2.48      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 15.96/2.48      | k1_xboole_0 = X1
% 15.96/2.48      | k1_xboole_0 = X3
% 15.96/2.48      | k1_xboole_0 = X2 ),
% 15.96/2.48      inference(cnf_transformation,[],[f96]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_861,plain,
% 15.96/2.48      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 15.96/2.48      | k1_xboole_0 = X0
% 15.96/2.48      | k1_xboole_0 = X1
% 15.96/2.48      | k1_xboole_0 = X2
% 15.96/2.48      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3100,plain,
% 15.96/2.48      ( k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13)
% 15.96/2.48      | sK11 = k1_xboole_0
% 15.96/2.48      | sK10 = k1_xboole_0
% 15.96/2.48      | sK9 = k1_xboole_0 ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_857,c_861]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3385,plain,
% 15.96/2.48      ( k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13) ),
% 15.96/2.48      inference(global_propositional_subsumption,
% 15.96/2.48                [status(thm)],
% 15.96/2.48                [c_3100,c_36,c_35,c_34,c_45,c_46,c_931,c_946,c_969]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_33,negated_conjecture,
% 15.96/2.48      ( k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 ),
% 15.96/2.48      inference(cnf_transformation,[],[f92]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3387,plain,
% 15.96/2.48      ( k2_mcart_1(sK13) != sK12 ),
% 15.96/2.48      inference(demodulation,[status(thm)],[c_3385,c_33]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_22,plain,
% 15.96/2.48      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 15.96/2.48      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 15.96/2.48      inference(cnf_transformation,[],[f95]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_862,plain,
% 15.96/2.48      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 15.96/2.48      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3697,plain,
% 15.96/2.48      ( m1_subset_1(k7_mcart_1(sK9,sK10,sK11,sK13),sK11) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_857,c_862]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3709,plain,
% 15.96/2.48      ( m1_subset_1(k2_mcart_1(sK13),sK11) = iProver_top ),
% 15.96/2.48      inference(light_normalisation,[status(thm)],[c_3697,c_3385]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_22664,plain,
% 15.96/2.48      ( m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top
% 15.96/2.48      | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
% 15.96/2.48      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(global_propositional_subsumption,
% 15.96/2.48                [status(thm)],
% 15.96/2.48                [c_22514,c_3387,c_3709]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_22665,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | m1_subset_1(sK6(sK9,sK10,k1_mcart_1(sK13)),sK10) != iProver_top
% 15.96/2.48      | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top ),
% 15.96/2.48      inference(renaming,[status(thm)],[c_22664]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_22668,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top
% 15.96/2.48      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK13)),sK10) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_22503,c_22665]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_22671,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | m1_subset_1(sK5(sK9,sK10,k1_mcart_1(sK13)),sK9) != iProver_top ),
% 15.96/2.48      inference(global_propositional_subsumption,
% 15.96/2.48                [status(thm)],
% 15.96/2.48                [c_22513,c_4772,c_22668]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_25529,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | m1_subset_1(sK5(sK9,sK10,sK7(sK13)),sK9) != iProver_top ),
% 15.96/2.48      inference(demodulation,[status(thm)],[c_25488,c_22671]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_66134,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 15.96/2.48      | r2_hidden(sK7(sK13),k2_zfmisc_1(sK9,sK10)) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3866,c_25529]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_66491,plain,
% 15.96/2.48      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 15.96/2.48      inference(global_propositional_subsumption,
% 15.96/2.48                [status(thm)],
% 15.96/2.48                [c_25612,c_36,c_35,c_34,c_102,c_2493,c_3862,c_4511,c_8445,
% 15.96/2.48                 c_42025,c_46740,c_66134]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_11,plain,
% 15.96/2.48      ( ~ r2_hidden(X0,X1)
% 15.96/2.48      | ~ r2_hidden(X2,X3)
% 15.96/2.48      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 15.96/2.48      inference(cnf_transformation,[],[f108]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_873,plain,
% 15.96/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.96/2.48      | r2_hidden(X2,X3) != iProver_top
% 15.96/2.48      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_25487,plain,
% 15.96/2.48      ( r2_hidden(sK8(sK13),X0) != iProver_top
% 15.96/2.48      | r2_hidden(sK7(sK13),X1) != iProver_top
% 15.96/2.48      | r2_hidden(sK13,k2_zfmisc_1(X1,X0)) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_25374,c_873]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_66555,plain,
% 15.96/2.48      ( r2_hidden(sK8(sK13),sK11) != iProver_top
% 15.96/2.48      | r2_hidden(sK7(sK13),k2_zfmisc_1(sK9,sK10)) != iProver_top
% 15.96/2.48      | r2_hidden(sK13,k1_xboole_0) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_66491,c_25487]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3932,plain,
% 15.96/2.48      ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top
% 15.96/2.48      | v1_xboole_0(sK11) = iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_3709,c_864]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_918,plain,
% 15.96/2.48      ( ~ r1_xboole_0(sK11,sK11) | k1_xboole_0 = sK11 ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_5]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_919,plain,
% 15.96/2.48      ( k1_xboole_0 = sK11 | r1_xboole_0(sK11,sK11) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_991,plain,
% 15.96/2.48      ( r1_xboole_0(sK11,sK11) | r2_hidden(sK1(sK11,sK11),sK11) ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_4]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_992,plain,
% 15.96/2.48      ( r1_xboole_0(sK11,sK11) = iProver_top
% 15.96/2.48      | r2_hidden(sK1(sK11,sK11),sK11) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_991]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3302,plain,
% 15.96/2.48      ( ~ r2_hidden(sK1(sK11,sK11),sK11) | ~ v1_xboole_0(sK11) ),
% 15.96/2.48      inference(instantiation,[status(thm)],[c_1]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3303,plain,
% 15.96/2.48      ( r2_hidden(sK1(sK11,sK11),sK11) != iProver_top
% 15.96/2.48      | v1_xboole_0(sK11) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_3302]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_3999,plain,
% 15.96/2.48      ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top ),
% 15.96/2.48      inference(global_propositional_subsumption,
% 15.96/2.48                [status(thm)],
% 15.96/2.48                [c_3932,c_34,c_919,c_992,c_3303]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_25615,plain,
% 15.96/2.48      ( r2_hidden(sK8(sK13),sK11) = iProver_top ),
% 15.96/2.48      inference(demodulation,[status(thm)],[c_25489,c_3999]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_66679,plain,
% 15.96/2.48      ( r2_hidden(sK13,k1_xboole_0) = iProver_top ),
% 15.96/2.48      inference(global_propositional_subsumption,
% 15.96/2.48                [status(thm)],
% 15.96/2.48                [c_66555,c_36,c_35,c_34,c_102,c_2493,c_3862,c_4511,c_8445,
% 15.96/2.48                 c_25615,c_42025,c_46740]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_878,plain,
% 15.96/2.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_882,plain,
% 15.96/2.48      ( r1_xboole_0(X0,X1) != iProver_top
% 15.96/2.48      | r2_hidden(X2,X0) != iProver_top
% 15.96/2.48      | r2_hidden(X2,X1) != iProver_top ),
% 15.96/2.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_8893,plain,
% 15.96/2.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_878,c_882]) ).
% 15.96/2.48  
% 15.96/2.48  cnf(c_66687,plain,
% 15.96/2.48      ( $false ),
% 15.96/2.48      inference(superposition,[status(thm)],[c_66679,c_8893]) ).
% 15.96/2.48  
% 15.96/2.48  
% 15.96/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.96/2.48  
% 15.96/2.48  ------                               Statistics
% 15.96/2.48  
% 15.96/2.48  ------ General
% 15.96/2.48  
% 15.96/2.48  abstr_ref_over_cycles:                  0
% 15.96/2.48  abstr_ref_under_cycles:                 0
% 15.96/2.48  gc_basic_clause_elim:                   0
% 15.96/2.48  forced_gc_time:                         0
% 15.96/2.48  parsing_time:                           0.012
% 15.96/2.48  unif_index_cands_time:                  0.
% 15.96/2.48  unif_index_add_time:                    0.
% 15.96/2.48  orderings_time:                         0.
% 15.96/2.48  out_proof_time:                         0.024
% 15.96/2.48  total_time:                             1.974
% 15.96/2.48  num_of_symbols:                         58
% 15.96/2.48  num_of_terms:                           98308
% 15.96/2.48  
% 15.96/2.48  ------ Preprocessing
% 15.96/2.48  
% 15.96/2.48  num_of_splits:                          0
% 15.96/2.48  num_of_split_atoms:                     0
% 15.96/2.48  num_of_reused_defs:                     0
% 15.96/2.48  num_eq_ax_congr_red:                    58
% 15.96/2.48  num_of_sem_filtered_clauses:            1
% 15.96/2.48  num_of_subtypes:                        0
% 15.96/2.48  monotx_restored_types:                  0
% 15.96/2.48  sat_num_of_epr_types:                   0
% 15.96/2.48  sat_num_of_non_cyclic_types:            0
% 15.96/2.48  sat_guarded_non_collapsed_types:        0
% 15.96/2.48  num_pure_diseq_elim:                    0
% 15.96/2.48  simp_replaced_by:                       0
% 15.96/2.48  res_preprocessed:                       140
% 15.96/2.48  prep_upred:                             0
% 15.96/2.48  prep_unflattend:                        3
% 15.96/2.48  smt_new_axioms:                         0
% 15.96/2.48  pred_elim_cands:                        4
% 15.96/2.48  pred_elim:                              0
% 15.96/2.48  pred_elim_cl:                           0
% 15.96/2.48  pred_elim_cycles:                       1
% 15.96/2.48  merged_defs:                            0
% 15.96/2.48  merged_defs_ncl:                        0
% 15.96/2.48  bin_hyper_res:                          0
% 15.96/2.48  prep_cycles:                            3
% 15.96/2.48  pred_elim_time:                         0.001
% 15.96/2.48  splitting_time:                         0.
% 15.96/2.48  sem_filter_time:                        0.
% 15.96/2.48  monotx_time:                            0.001
% 15.96/2.48  subtype_inf_time:                       0.
% 15.96/2.48  
% 15.96/2.48  ------ Problem properties
% 15.96/2.48  
% 15.96/2.48  clauses:                                39
% 15.96/2.48  conjectures:                            6
% 15.96/2.48  epr:                                    9
% 15.96/2.48  horn:                                   28
% 15.96/2.48  ground:                                 6
% 15.96/2.48  unary:                                  13
% 15.96/2.48  binary:                                 14
% 15.96/2.48  lits:                                   89
% 15.96/2.48  lits_eq:                                38
% 15.96/2.48  fd_pure:                                0
% 15.96/2.48  fd_pseudo:                              0
% 15.96/2.48  fd_cond:                                6
% 15.96/2.48  fd_pseudo_cond:                         4
% 15.96/2.48  ac_symbols:                             0
% 15.96/2.48  
% 15.96/2.48  ------ Propositional Solver
% 15.96/2.48  
% 15.96/2.48  prop_solver_calls:                      38
% 15.96/2.48  prop_fast_solver_calls:                 2039
% 15.96/2.48  smt_solver_calls:                       0
% 15.96/2.48  smt_fast_solver_calls:                  0
% 15.96/2.48  prop_num_of_clauses:                    37041
% 15.96/2.48  prop_preprocess_simplified:             77266
% 15.96/2.48  prop_fo_subsumed:                       142
% 15.96/2.48  prop_solver_time:                       0.
% 15.96/2.48  smt_solver_time:                        0.
% 15.96/2.48  smt_fast_solver_time:                   0.
% 15.96/2.48  prop_fast_solver_time:                  0.
% 15.96/2.48  prop_unsat_core_time:                   0.
% 15.96/2.48  
% 15.96/2.48  ------ QBF
% 15.96/2.48  
% 15.96/2.48  qbf_q_res:                              0
% 15.96/2.48  qbf_num_tautologies:                    0
% 15.96/2.48  qbf_prep_cycles:                        0
% 15.96/2.48  
% 15.96/2.48  ------ BMC1
% 15.96/2.48  
% 15.96/2.48  bmc1_current_bound:                     -1
% 15.96/2.48  bmc1_last_solved_bound:                 -1
% 15.96/2.48  bmc1_unsat_core_size:                   -1
% 15.96/2.48  bmc1_unsat_core_parents_size:           -1
% 15.96/2.48  bmc1_merge_next_fun:                    0
% 15.96/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.96/2.48  
% 15.96/2.48  ------ Instantiation
% 15.96/2.48  
% 15.96/2.48  inst_num_of_clauses:                    13951
% 15.96/2.48  inst_num_in_passive:                    10584
% 15.96/2.48  inst_num_in_active:                     1364
% 15.96/2.48  inst_num_in_unprocessed:                2003
% 15.96/2.48  inst_num_of_loops:                      1640
% 15.96/2.48  inst_num_of_learning_restarts:          0
% 15.96/2.48  inst_num_moves_active_passive:          276
% 15.96/2.48  inst_lit_activity:                      0
% 15.96/2.48  inst_lit_activity_moves:                0
% 15.96/2.48  inst_num_tautologies:                   0
% 15.96/2.48  inst_num_prop_implied:                  0
% 15.96/2.48  inst_num_existing_simplified:           0
% 15.96/2.48  inst_num_eq_res_simplified:             0
% 15.96/2.48  inst_num_child_elim:                    0
% 15.96/2.48  inst_num_of_dismatching_blockings:      4848
% 15.96/2.48  inst_num_of_non_proper_insts:           8185
% 15.96/2.48  inst_num_of_duplicates:                 0
% 15.96/2.48  inst_inst_num_from_inst_to_res:         0
% 15.96/2.48  inst_dismatching_checking_time:         0.
% 15.96/2.48  
% 15.96/2.48  ------ Resolution
% 15.96/2.48  
% 15.96/2.48  res_num_of_clauses:                     0
% 15.96/2.48  res_num_in_passive:                     0
% 15.96/2.48  res_num_in_active:                      0
% 15.96/2.48  res_num_of_loops:                       143
% 15.96/2.48  res_forward_subset_subsumed:            12
% 15.96/2.48  res_backward_subset_subsumed:           0
% 15.96/2.48  res_forward_subsumed:                   0
% 15.96/2.48  res_backward_subsumed:                  0
% 15.96/2.48  res_forward_subsumption_resolution:     0
% 15.96/2.48  res_backward_subsumption_resolution:    0
% 15.96/2.48  res_clause_to_clause_subsumption:       4769
% 15.96/2.48  res_orphan_elimination:                 0
% 15.96/2.48  res_tautology_del:                      0
% 15.96/2.48  res_num_eq_res_simplified:              0
% 15.96/2.48  res_num_sel_changes:                    0
% 15.96/2.48  res_moves_from_active_to_pass:          0
% 15.96/2.48  
% 15.96/2.48  ------ Superposition
% 15.96/2.48  
% 15.96/2.48  sup_time_total:                         0.
% 15.96/2.48  sup_time_generating:                    0.
% 15.96/2.48  sup_time_sim_full:                      0.
% 15.96/2.48  sup_time_sim_immed:                     0.
% 15.96/2.48  
% 15.96/2.48  sup_num_of_clauses:                     758
% 15.96/2.48  sup_num_in_active:                      144
% 15.96/2.48  sup_num_in_passive:                     614
% 15.96/2.48  sup_num_of_loops:                       327
% 15.96/2.48  sup_fw_superposition:                   1475
% 15.96/2.48  sup_bw_superposition:                   4590
% 15.96/2.48  sup_immediate_simplified:               2906
% 15.96/2.48  sup_given_eliminated:                   5
% 15.96/2.48  comparisons_done:                       0
% 15.96/2.48  comparisons_avoided:                    366
% 15.96/2.48  
% 15.96/2.48  ------ Simplifications
% 15.96/2.48  
% 15.96/2.48  
% 15.96/2.48  sim_fw_subset_subsumed:                 1498
% 15.96/2.48  sim_bw_subset_subsumed:                 217
% 15.96/2.48  sim_fw_subsumed:                        870
% 15.96/2.48  sim_bw_subsumed:                        133
% 15.96/2.48  sim_fw_subsumption_res:                 0
% 15.96/2.48  sim_bw_subsumption_res:                 0
% 15.96/2.48  sim_tautology_del:                      31
% 15.96/2.48  sim_eq_tautology_del:                   300
% 15.96/2.48  sim_eq_res_simp:                        37
% 15.96/2.48  sim_fw_demodulated:                     423
% 15.96/2.48  sim_bw_demodulated:                     96
% 15.96/2.48  sim_light_normalised:                   246
% 15.96/2.48  sim_joinable_taut:                      0
% 15.96/2.48  sim_joinable_simp:                      0
% 15.96/2.48  sim_ac_normalised:                      0
% 15.96/2.48  sim_smt_subsumption:                    0
% 15.96/2.48  
%------------------------------------------------------------------------------
