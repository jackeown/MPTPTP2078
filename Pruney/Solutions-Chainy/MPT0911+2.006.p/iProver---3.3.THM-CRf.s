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
% DateTime   : Thu Dec  3 11:59:01 EST 2020

% Result     : Theorem 27.55s
% Output     : CNFRefutation 27.55s
% Verified   : 
% Statistics : Number of formulae       :  289 (206903 expanded)
%              Number of clauses        :  199 (66046 expanded)
%              Number of leaves         :   22 (44532 expanded)
%              Depth                    :   40
%              Number of atoms          :  876 (965239 expanded)
%              Number of equality atoms :  616 (463315 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f43,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f25,f43])).

fof(f81,plain,(
    m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11)) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f97,plain,(
    m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
    inference(definition_unfolding,[],[f81,f61])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK6(X0),sK7(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK6(X0),sK7(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f36])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK6(X0),sK7(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK8(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK8(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK8(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f39])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f73,f61])).

fof(f83,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X6,X7,X5] :
      ( sK12 = X7
      | k3_mcart_1(X5,X6,X7) != sK13
      | ~ m1_subset_1(X7,sK11)
      | ~ m1_subset_1(X6,sK10)
      | ~ m1_subset_1(X5,sK9) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f96,plain,(
    ! [X6,X7,X5] :
      ( sK12 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK13
      | ~ m1_subset_1(X7,sK11)
      | ~ m1_subset_1(X6,sK10)
      | ~ m1_subset_1(X5,sK9) ) ),
    inference(definition_unfolding,[],[f82,f60])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f41])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f61])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f87])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f31,f34,f33,f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f77,f87])).

fof(f106,plain,(
    ! [X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f92])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f75,f87])).

fof(f108,plain,(
    ! [X2,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f94])).

fof(f50,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f50])).

fof(f99,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f78,f87])).

fof(f105,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f91])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f49,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f48,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_729,plain,
    ( m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_740,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2833,plain,
    ( r2_hidden(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_740])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_738,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2841,plain,
    ( r2_hidden(k1_mcart_1(sK13),k2_zfmisc_1(sK9,sK10)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_738])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK6(X0),sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_743,plain,
    ( k4_tarski(sK6(X0),sK7(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3027,plain,
    ( k4_tarski(sK6(k1_mcart_1(sK13)),sK7(k1_mcart_1(sK13))) = k1_mcart_1(sK13)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_743])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_741,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3473,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_741])).

cnf(c_14716,plain,
    ( k4_tarski(sK6(k1_mcart_1(sK13)),sK7(k1_mcart_1(sK13))) = k1_mcart_1(sK13)
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_3027,c_3473])).

cnf(c_22,plain,
    ( r2_hidden(sK8(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_734,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK8(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_752,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2265,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_752])).

cnf(c_14943,plain,
    ( k4_tarski(sK6(k1_mcart_1(sK13)),sK7(k1_mcart_1(sK13))) = k1_mcart_1(sK13)
    | sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14716,c_2265])).

cnf(c_32,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_14953,plain,
    ( k1_mcart_1(k1_mcart_1(sK13)) = sK6(k1_mcart_1(sK13))
    | sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14943,c_32])).

cnf(c_3029,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK13)),sK9) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_738])).

cnf(c_7893,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK13)),sK9) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_3029,c_3473])).

cnf(c_16610,plain,
    ( sK13 = k1_xboole_0
    | r2_hidden(sK6(k1_mcart_1(sK13)),sK9) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_14953,c_7893])).

cnf(c_2839,plain,
    ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_743])).

cnf(c_4002,plain,
    ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_2839,c_3473])).

cnf(c_4300,plain,
    ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
    | sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4002,c_2265])).

cnf(c_31,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5106,plain,
    ( k2_mcart_1(sK13) = sK7(sK13)
    | sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4300,c_31])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_739,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2840,plain,
    ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_739])).

cnf(c_4003,plain,
    ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_2840,c_3473])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_182,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_1])).

cnf(c_183,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_728,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_4295,plain,
    ( m1_subset_1(k2_mcart_1(sK13),sK11) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_4003,c_728])).

cnf(c_5829,plain,
    ( sK13 = k1_xboole_0
    | m1_subset_1(sK7(sK13),sK11) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_5106,c_4295])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_733,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3245,plain,
    ( k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13)
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_729,c_733])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK10),X2))
    | k7_mcart_1(X1,sK10,X2,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1268,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK10),sK11))
    | k7_mcart_1(X1,sK10,sK11,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK11
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1859,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
    | k7_mcart_1(sK9,sK10,sK11,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = sK11
    | k1_xboole_0 = sK10
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_2806,plain,
    ( ~ m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
    | k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13)
    | k1_xboole_0 = sK11
    | k1_xboole_0 = sK10
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_1859])).

cnf(c_4007,plain,
    ( k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3245,c_38,c_36,c_35,c_34,c_2806])).

cnf(c_33,negated_conjecture,
    ( k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4009,plain,
    ( k2_mcart_1(sK13) != sK12 ),
    inference(demodulation,[status(thm)],[c_4007,c_33])).

cnf(c_5831,plain,
    ( sK7(sK13) != sK12
    | sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5106,c_4009])).

cnf(c_7900,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK13)),sK9) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_7893,c_728])).

cnf(c_16609,plain,
    ( sK13 = k1_xboole_0
    | m1_subset_1(sK6(k1_mcart_1(sK13)),sK9) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_14953,c_7900])).

cnf(c_14954,plain,
    ( k2_mcart_1(k1_mcart_1(sK13)) = sK7(k1_mcart_1(sK13))
    | sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14943,c_31])).

cnf(c_3028,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK13)),sK10) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_739])).

cnf(c_5373,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK13)),sK10) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_3028,c_3473])).

cnf(c_5379,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK13)),sK10) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_5373,c_728])).

cnf(c_16910,plain,
    ( sK13 = k1_xboole_0
    | m1_subset_1(sK7(k1_mcart_1(sK13)),sK10) = iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_14954,c_5379])).

cnf(c_5105,plain,
    ( k1_mcart_1(sK13) = sK6(sK13)
    | sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4300,c_32])).

cnf(c_37,negated_conjecture,
    ( ~ m1_subset_1(X0,sK11)
    | ~ m1_subset_1(X1,sK10)
    | ~ m1_subset_1(X2,sK9)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK13
    | sK12 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_730,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK13
    | sK12 = X2
    | m1_subset_1(X2,sK11) != iProver_top
    | m1_subset_1(X1,sK10) != iProver_top
    | m1_subset_1(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_14955,plain,
    ( k4_tarski(k1_mcart_1(sK13),X0) != sK13
    | sK12 = X0
    | sK13 = k1_xboole_0
    | m1_subset_1(X0,sK11) != iProver_top
    | m1_subset_1(sK7(k1_mcart_1(sK13)),sK10) != iProver_top
    | m1_subset_1(sK6(k1_mcart_1(sK13)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_14943,c_730])).

cnf(c_17172,plain,
    ( k4_tarski(sK6(sK13),X0) != sK13
    | sK12 = X0
    | sK13 = k1_xboole_0
    | m1_subset_1(X0,sK11) != iProver_top
    | m1_subset_1(sK7(k1_mcart_1(sK13)),sK10) != iProver_top
    | m1_subset_1(sK6(k1_mcart_1(sK13)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5105,c_14955])).

cnf(c_18803,plain,
    ( sK7(sK13) = sK12
    | sK13 = k1_xboole_0
    | m1_subset_1(sK7(k1_mcart_1(sK13)),sK10) != iProver_top
    | m1_subset_1(sK7(sK13),sK11) != iProver_top
    | m1_subset_1(sK6(k1_mcart_1(sK13)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4300,c_17172])).

cnf(c_18807,plain,
    ( sK13 = k1_xboole_0
    | v1_xboole_0(sK13) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16610,c_5829,c_5831,c_16609,c_16910,c_18803])).

cnf(c_18814,plain,
    ( sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18807,c_2265])).

cnf(c_72925,plain,
    ( r2_hidden(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18814,c_2833])).

cnf(c_30,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_835,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK10),X1),X2) != k1_xboole_0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1190,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK10),X1),sK11) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK11
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_1544,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),X0),sK11) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK11
    | k1_xboole_0 = sK10
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_2289,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) != k1_xboole_0
    | k1_xboole_0 = sK11
    | k1_xboole_0 = sK10
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4496,plain,
    ( r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4497,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) = k1_xboole_0
    | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4496])).

cnf(c_7487,plain,
    ( ~ r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7488,plain,
    ( r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7487])).

cnf(c_24836,plain,
    ( ~ r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_24837,plain,
    ( r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24836])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_753,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2521,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_739])).

cnf(c_2533,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_752])).

cnf(c_2579,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_2533])).

cnf(c_2974,plain,
    ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2840,c_2579])).

cnf(c_3073,plain,
    ( m1_subset_1(k2_mcart_1(sK13),sK11) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2974,c_728])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_737,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5597,plain,
    ( k4_tarski(k1_mcart_1(sK13),k2_mcart_1(sK13)) = sK13
    | k2_zfmisc_1(sK9,sK10) = k1_xboole_0
    | sK11 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_729,c_737])).

cnf(c_45,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_46,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_327,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_811,plain,
    ( sK11 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK11 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_812,plain,
    ( sK11 != k1_xboole_0
    | k1_xboole_0 = sK11
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_6939,plain,
    ( k2_zfmisc_1(sK9,sK10) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK13),k2_mcart_1(sK13)) = sK13 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5597,c_34,c_45,c_46,c_812])).

cnf(c_6940,plain,
    ( k4_tarski(k1_mcart_1(sK13),k2_mcart_1(sK13)) = sK13
    | k2_zfmisc_1(sK9,sK10) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6939])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_747,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7017,plain,
    ( k2_zfmisc_1(sK9,sK10) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK13),X0) != iProver_top
    | r2_hidden(k2_mcart_1(sK13),X1) != iProver_top
    | r2_hidden(sK13,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6940,c_747])).

cnf(c_7777,plain,
    ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
    | k2_zfmisc_1(sK9,sK10) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK13),X0) != iProver_top
    | r2_hidden(k2_mcart_1(sK13),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7017,c_743])).

cnf(c_3021,plain,
    ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2839,c_2579])).

cnf(c_29541,plain,
    ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7777,c_36,c_35,c_34,c_2289,c_2839,c_3021,c_4497,c_7488,c_24837])).

cnf(c_29543,plain,
    ( k4_tarski(sK6(k1_xboole_0),sK7(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_29541,c_18814])).

cnf(c_29555,plain,
    ( k2_mcart_1(k1_xboole_0) = sK7(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_29543,c_31])).

cnf(c_37550,plain,
    ( m1_subset_1(sK7(k1_xboole_0),sK11) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3073,c_18814,c_29555])).

cnf(c_748,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7019,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k2_zfmisc_1(k2_zfmisc_1(X3,X4),k1_xboole_0)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_747])).

cnf(c_7266,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = X3
    | r2_hidden(X4,X5) != iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),X3) = iProver_top
    | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),X4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_7019])).

cnf(c_7286,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X3,X4),k1_xboole_0),X5,X0),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X3,X4),k1_xboole_0),X5,X0),X1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7266,c_27])).

cnf(c_10961,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),k1_mcart_1(sK13)),k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_7286])).

cnf(c_29554,plain,
    ( k1_mcart_1(k1_xboole_0) = sK6(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_29543,c_32])).

cnf(c_41093,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK6(k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10961,c_18814,c_29554])).

cnf(c_10957,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK13),k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_7286])).

cnf(c_26,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_7018,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | r2_hidden(X4,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(X0,X4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_747])).

cnf(c_7197,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(sK13,X0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_7018])).

cnf(c_1527,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27,c_27])).

cnf(c_1915,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_738])).

cnf(c_2064,plain,
    ( r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_1915])).

cnf(c_7683,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK13,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7197,c_2064])).

cnf(c_20157,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7683,c_18814])).

cnf(c_20180,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10957,c_20157])).

cnf(c_74,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_76,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_2066,plain,
    ( m1_subset_1(k1_mcart_1(X0),k1_xboole_0) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_728])).

cnf(c_2446,plain,
    ( m1_subset_1(X0,k1_xboole_0) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_2066])).

cnf(c_7682,plain,
    ( m1_subset_1(sK13,k1_xboole_0) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7197,c_2446])).

cnf(c_19762,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7682,c_18814])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_81,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_83,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_7675,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(sK13,X0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7197,c_2579])).

cnf(c_19156,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7675,c_18814])).

cnf(c_19171,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19156,c_2446])).

cnf(c_19764,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19762,c_83,c_19171])).

cnf(c_19765,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19764])).

cnf(c_19768,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_19765])).

cnf(c_21358,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19768,c_83])).

cnf(c_30666,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20180,c_36,c_35,c_34,c_76,c_83,c_2289,c_4497,c_7488,c_19768,c_24837])).

cnf(c_30667,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_30666])).

cnf(c_29551,plain,
    ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29543,c_2064])).

cnf(c_36970,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK6(k1_xboole_0)),k1_xboole_0) = iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29551,c_7286])).

cnf(c_41095,plain,
    ( r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK6(k1_xboole_0)),k1_xboole_0) = iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41093,c_30667,c_36970])).

cnf(c_41096,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK6(k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_41095])).

cnf(c_2773,plain,
    ( k4_tarski(sK6(k2_mcart_1(X0)),sK7(k2_mcart_1(X0))) = k2_mcart_1(X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_743])).

cnf(c_41127,plain,
    ( k4_tarski(sK6(k2_mcart_1(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),sK6(k1_xboole_0)))),sK7(k2_mcart_1(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),sK6(k1_xboole_0))))) = k2_mcart_1(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),sK6(k1_xboole_0)))
    | k1_xboole_0 = X3
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_41096,c_2773])).

cnf(c_41180,plain,
    ( k4_tarski(sK6(sK6(k1_xboole_0)),sK7(sK6(k1_xboole_0))) = sK6(k1_xboole_0)
    | k1_xboole_0 = X0
    | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_41127,c_31])).

cnf(c_2775,plain,
    ( k4_tarski(sK6(X0),sK7(X0)) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_743])).

cnf(c_36981,plain,
    ( k4_tarski(sK6(sK6(k1_xboole_0)),sK7(sK6(k1_xboole_0))) = sK6(k1_xboole_0)
    | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29551,c_2775])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_744,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3546,plain,
    ( k4_tarski(sK6(sK4(k2_zfmisc_1(X0,X1),X2,X3)),sK7(sK4(k2_zfmisc_1(X0,X1),X2,X3))) = sK4(k2_zfmisc_1(X0,X1),X2,X3)
    | r2_hidden(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_743])).

cnf(c_41629,plain,
    ( k4_tarski(sK6(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13)),sK7(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13))) = sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_3546])).

cnf(c_3022,plain,
    ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
    | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2839,c_2265])).

cnf(c_5276,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
    | k1_mcart_1(sK13) = sK6(sK13) ),
    inference(superposition,[status(thm)],[c_3022,c_32])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_746,plain,
    ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4928,plain,
    ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_746])).

cnf(c_6040,plain,
    ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | k1_mcart_1(sK13) = sK6(sK13)
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5276,c_4928])).

cnf(c_4960,plain,
    ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4928,c_2579])).

cnf(c_26083,plain,
    ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6040,c_36,c_35,c_34,c_2289,c_4497,c_4928,c_4960,c_7488,c_24837])).

cnf(c_26085,plain,
    ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0),sK5(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_26083,c_18814])).

cnf(c_26095,plain,
    ( sK4(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0) = k1_mcart_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26085,c_32])).

cnf(c_29603,plain,
    ( sK4(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0) = sK6(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_29554,c_26095])).

cnf(c_41691,plain,
    ( k4_tarski(sK6(sK6(k1_xboole_0)),sK7(sK6(k1_xboole_0))) = sK6(k1_xboole_0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41629,c_18814,c_29603])).

cnf(c_42071,plain,
    ( k4_tarski(sK6(sK6(k1_xboole_0)),sK7(sK6(k1_xboole_0))) = sK6(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41180,c_36,c_35,c_34,c_76,c_83,c_2289,c_4497,c_7488,c_19768,c_24837,c_36981,c_41691])).

cnf(c_42085,plain,
    ( k4_tarski(sK6(k1_xboole_0),X0) != sK13
    | sK12 = X0
    | m1_subset_1(X0,sK11) != iProver_top
    | m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) != iProver_top
    | m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_42071,c_730])).

cnf(c_42087,plain,
    ( k4_tarski(sK6(k1_xboole_0),X0) != k1_xboole_0
    | sK12 = X0
    | m1_subset_1(X0,sK11) != iProver_top
    | m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) != iProver_top
    | m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42085,c_18814])).

cnf(c_42364,plain,
    ( sK7(k1_xboole_0) = sK12
    | m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) != iProver_top
    | m1_subset_1(sK7(k1_xboole_0),sK11) != iProver_top
    | m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_29543,c_42087])).

cnf(c_72916,plain,
    ( k2_mcart_1(k1_xboole_0) != sK12 ),
    inference(demodulation,[status(thm)],[c_18814,c_4009])).

cnf(c_72935,plain,
    ( sK7(k1_xboole_0) != sK12 ),
    inference(light_normalisation,[status(thm)],[c_72916,c_29555])).

cnf(c_72884,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_xboole_0)),sK10) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18814,c_5379])).

cnf(c_42084,plain,
    ( k2_mcart_1(sK6(k1_xboole_0)) = sK7(sK6(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_42071,c_31])).

cnf(c_72945,plain,
    ( m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72884,c_29554,c_42084])).

cnf(c_72871,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_xboole_0)),sK9) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18814,c_7900])).

cnf(c_42083,plain,
    ( k1_mcart_1(sK6(k1_xboole_0)) = sK6(sK6(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_42071,c_32])).

cnf(c_72952,plain,
    ( m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72871,c_29554,c_42083])).

cnf(c_73593,plain,
    ( r2_hidden(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72925,c_36,c_35,c_34,c_2289,c_4497,c_7488,c_24837,c_37550,c_42364,c_72935,c_72945,c_72952])).

cnf(c_73612,plain,
    ( r2_hidden(k1_mcart_1(k1_xboole_0),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_73593,c_738])).

cnf(c_73619,plain,
    ( r2_hidden(sK6(k1_xboole_0),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_73612,c_29554])).

cnf(c_75189,plain,
    ( r2_hidden(k2_mcart_1(sK6(k1_xboole_0)),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_73619,c_739])).

cnf(c_75193,plain,
    ( r2_hidden(sK7(sK6(k1_xboole_0)),sK10) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_75189,c_42084])).

cnf(c_75328,plain,
    ( m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_75193,c_728])).

cnf(c_75190,plain,
    ( r2_hidden(k1_mcart_1(sK6(k1_xboole_0)),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_73619,c_738])).

cnf(c_75192,plain,
    ( r2_hidden(sK6(sK6(k1_xboole_0)),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_75190,c_42083])).

cnf(c_75324,plain,
    ( m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_75192,c_728])).

cnf(c_26096,plain,
    ( sK5(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0) = k2_mcart_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26085,c_31])).

cnf(c_29807,plain,
    ( sK5(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0) = sK7(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_29555,c_26096])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_745,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3573,plain,
    ( m1_subset_1(sK5(X0,X1,X2),X1) = iProver_top
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_745,c_728])).

cnf(c_47996,plain,
    ( m1_subset_1(sK7(k1_xboole_0),sK11) = iProver_top
    | r2_hidden(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29807,c_3573])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75328,c_75324,c_73593,c_72935,c_47996,c_42364])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.55/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.55/4.00  
% 27.55/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.55/4.00  
% 27.55/4.00  ------  iProver source info
% 27.55/4.00  
% 27.55/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.55/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.55/4.00  git: non_committed_changes: false
% 27.55/4.00  git: last_make_outside_of_git: false
% 27.55/4.00  
% 27.55/4.00  ------ 
% 27.55/4.00  
% 27.55/4.00  ------ Input Options
% 27.55/4.00  
% 27.55/4.00  --out_options                           all
% 27.55/4.00  --tptp_safe_out                         true
% 27.55/4.00  --problem_path                          ""
% 27.55/4.00  --include_path                          ""
% 27.55/4.00  --clausifier                            res/vclausify_rel
% 27.55/4.00  --clausifier_options                    ""
% 27.55/4.00  --stdin                                 false
% 27.55/4.00  --stats_out                             all
% 27.55/4.00  
% 27.55/4.00  ------ General Options
% 27.55/4.00  
% 27.55/4.00  --fof                                   false
% 27.55/4.00  --time_out_real                         305.
% 27.55/4.00  --time_out_virtual                      -1.
% 27.55/4.00  --symbol_type_check                     false
% 27.55/4.00  --clausify_out                          false
% 27.55/4.00  --sig_cnt_out                           false
% 27.55/4.00  --trig_cnt_out                          false
% 27.55/4.00  --trig_cnt_out_tolerance                1.
% 27.55/4.00  --trig_cnt_out_sk_spl                   false
% 27.55/4.00  --abstr_cl_out                          false
% 27.55/4.00  
% 27.55/4.00  ------ Global Options
% 27.55/4.00  
% 27.55/4.00  --schedule                              default
% 27.55/4.00  --add_important_lit                     false
% 27.55/4.00  --prop_solver_per_cl                    1000
% 27.55/4.00  --min_unsat_core                        false
% 27.55/4.00  --soft_assumptions                      false
% 27.55/4.00  --soft_lemma_size                       3
% 27.55/4.00  --prop_impl_unit_size                   0
% 27.55/4.00  --prop_impl_unit                        []
% 27.55/4.00  --share_sel_clauses                     true
% 27.55/4.00  --reset_solvers                         false
% 27.55/4.00  --bc_imp_inh                            [conj_cone]
% 27.55/4.00  --conj_cone_tolerance                   3.
% 27.55/4.00  --extra_neg_conj                        none
% 27.55/4.00  --large_theory_mode                     true
% 27.55/4.00  --prolific_symb_bound                   200
% 27.55/4.00  --lt_threshold                          2000
% 27.55/4.00  --clause_weak_htbl                      true
% 27.55/4.00  --gc_record_bc_elim                     false
% 27.55/4.00  
% 27.55/4.00  ------ Preprocessing Options
% 27.55/4.00  
% 27.55/4.00  --preprocessing_flag                    true
% 27.55/4.00  --time_out_prep_mult                    0.1
% 27.55/4.00  --splitting_mode                        input
% 27.55/4.00  --splitting_grd                         true
% 27.55/4.00  --splitting_cvd                         false
% 27.55/4.00  --splitting_cvd_svl                     false
% 27.55/4.00  --splitting_nvd                         32
% 27.55/4.00  --sub_typing                            true
% 27.55/4.00  --prep_gs_sim                           true
% 27.55/4.00  --prep_unflatten                        true
% 27.55/4.00  --prep_res_sim                          true
% 27.55/4.00  --prep_upred                            true
% 27.55/4.00  --prep_sem_filter                       exhaustive
% 27.55/4.00  --prep_sem_filter_out                   false
% 27.55/4.00  --pred_elim                             true
% 27.55/4.00  --res_sim_input                         true
% 27.55/4.00  --eq_ax_congr_red                       true
% 27.55/4.00  --pure_diseq_elim                       true
% 27.55/4.00  --brand_transform                       false
% 27.55/4.00  --non_eq_to_eq                          false
% 27.55/4.00  --prep_def_merge                        true
% 27.55/4.00  --prep_def_merge_prop_impl              false
% 27.55/4.00  --prep_def_merge_mbd                    true
% 27.55/4.00  --prep_def_merge_tr_red                 false
% 27.55/4.00  --prep_def_merge_tr_cl                  false
% 27.55/4.00  --smt_preprocessing                     true
% 27.55/4.00  --smt_ac_axioms                         fast
% 27.55/4.00  --preprocessed_out                      false
% 27.55/4.00  --preprocessed_stats                    false
% 27.55/4.00  
% 27.55/4.00  ------ Abstraction refinement Options
% 27.55/4.00  
% 27.55/4.00  --abstr_ref                             []
% 27.55/4.00  --abstr_ref_prep                        false
% 27.55/4.00  --abstr_ref_until_sat                   false
% 27.55/4.00  --abstr_ref_sig_restrict                funpre
% 27.55/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.55/4.00  --abstr_ref_under                       []
% 27.55/4.00  
% 27.55/4.00  ------ SAT Options
% 27.55/4.00  
% 27.55/4.00  --sat_mode                              false
% 27.55/4.00  --sat_fm_restart_options                ""
% 27.55/4.00  --sat_gr_def                            false
% 27.55/4.00  --sat_epr_types                         true
% 27.55/4.00  --sat_non_cyclic_types                  false
% 27.55/4.00  --sat_finite_models                     false
% 27.55/4.00  --sat_fm_lemmas                         false
% 27.55/4.00  --sat_fm_prep                           false
% 27.55/4.00  --sat_fm_uc_incr                        true
% 27.55/4.00  --sat_out_model                         small
% 27.55/4.00  --sat_out_clauses                       false
% 27.55/4.00  
% 27.55/4.00  ------ QBF Options
% 27.55/4.00  
% 27.55/4.00  --qbf_mode                              false
% 27.55/4.00  --qbf_elim_univ                         false
% 27.55/4.00  --qbf_dom_inst                          none
% 27.55/4.00  --qbf_dom_pre_inst                      false
% 27.55/4.00  --qbf_sk_in                             false
% 27.55/4.00  --qbf_pred_elim                         true
% 27.55/4.00  --qbf_split                             512
% 27.55/4.00  
% 27.55/4.00  ------ BMC1 Options
% 27.55/4.00  
% 27.55/4.00  --bmc1_incremental                      false
% 27.55/4.00  --bmc1_axioms                           reachable_all
% 27.55/4.00  --bmc1_min_bound                        0
% 27.55/4.00  --bmc1_max_bound                        -1
% 27.55/4.00  --bmc1_max_bound_default                -1
% 27.55/4.00  --bmc1_symbol_reachability              true
% 27.55/4.00  --bmc1_property_lemmas                  false
% 27.55/4.00  --bmc1_k_induction                      false
% 27.55/4.00  --bmc1_non_equiv_states                 false
% 27.55/4.00  --bmc1_deadlock                         false
% 27.55/4.00  --bmc1_ucm                              false
% 27.55/4.00  --bmc1_add_unsat_core                   none
% 27.55/4.00  --bmc1_unsat_core_children              false
% 27.55/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.55/4.00  --bmc1_out_stat                         full
% 27.55/4.00  --bmc1_ground_init                      false
% 27.55/4.00  --bmc1_pre_inst_next_state              false
% 27.55/4.00  --bmc1_pre_inst_state                   false
% 27.55/4.00  --bmc1_pre_inst_reach_state             false
% 27.55/4.00  --bmc1_out_unsat_core                   false
% 27.55/4.00  --bmc1_aig_witness_out                  false
% 27.55/4.00  --bmc1_verbose                          false
% 27.55/4.00  --bmc1_dump_clauses_tptp                false
% 27.55/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.55/4.00  --bmc1_dump_file                        -
% 27.55/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.55/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.55/4.00  --bmc1_ucm_extend_mode                  1
% 27.55/4.00  --bmc1_ucm_init_mode                    2
% 27.55/4.00  --bmc1_ucm_cone_mode                    none
% 27.55/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.55/4.00  --bmc1_ucm_relax_model                  4
% 27.55/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.55/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.55/4.00  --bmc1_ucm_layered_model                none
% 27.55/4.00  --bmc1_ucm_max_lemma_size               10
% 27.55/4.00  
% 27.55/4.00  ------ AIG Options
% 27.55/4.00  
% 27.55/4.00  --aig_mode                              false
% 27.55/4.00  
% 27.55/4.00  ------ Instantiation Options
% 27.55/4.00  
% 27.55/4.00  --instantiation_flag                    true
% 27.55/4.00  --inst_sos_flag                         true
% 27.55/4.00  --inst_sos_phase                        true
% 27.55/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.55/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.55/4.00  --inst_lit_sel_side                     num_symb
% 27.55/4.00  --inst_solver_per_active                1400
% 27.55/4.00  --inst_solver_calls_frac                1.
% 27.55/4.00  --inst_passive_queue_type               priority_queues
% 27.55/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.55/4.00  --inst_passive_queues_freq              [25;2]
% 27.55/4.00  --inst_dismatching                      true
% 27.55/4.00  --inst_eager_unprocessed_to_passive     true
% 27.55/4.00  --inst_prop_sim_given                   true
% 27.55/4.00  --inst_prop_sim_new                     false
% 27.55/4.00  --inst_subs_new                         false
% 27.55/4.00  --inst_eq_res_simp                      false
% 27.55/4.00  --inst_subs_given                       false
% 27.55/4.00  --inst_orphan_elimination               true
% 27.55/4.00  --inst_learning_loop_flag               true
% 27.55/4.00  --inst_learning_start                   3000
% 27.55/4.00  --inst_learning_factor                  2
% 27.55/4.00  --inst_start_prop_sim_after_learn       3
% 27.55/4.00  --inst_sel_renew                        solver
% 27.55/4.00  --inst_lit_activity_flag                true
% 27.55/4.00  --inst_restr_to_given                   false
% 27.55/4.00  --inst_activity_threshold               500
% 27.55/4.00  --inst_out_proof                        true
% 27.55/4.00  
% 27.55/4.00  ------ Resolution Options
% 27.55/4.00  
% 27.55/4.00  --resolution_flag                       true
% 27.55/4.00  --res_lit_sel                           adaptive
% 27.55/4.00  --res_lit_sel_side                      none
% 27.55/4.00  --res_ordering                          kbo
% 27.55/4.00  --res_to_prop_solver                    active
% 27.55/4.00  --res_prop_simpl_new                    false
% 27.55/4.00  --res_prop_simpl_given                  true
% 27.55/4.00  --res_passive_queue_type                priority_queues
% 27.55/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.55/4.00  --res_passive_queues_freq               [15;5]
% 27.55/4.00  --res_forward_subs                      full
% 27.55/4.00  --res_backward_subs                     full
% 27.55/4.00  --res_forward_subs_resolution           true
% 27.55/4.00  --res_backward_subs_resolution          true
% 27.55/4.00  --res_orphan_elimination                true
% 27.55/4.00  --res_time_limit                        2.
% 27.55/4.00  --res_out_proof                         true
% 27.55/4.00  
% 27.55/4.00  ------ Superposition Options
% 27.55/4.00  
% 27.55/4.00  --superposition_flag                    true
% 27.55/4.00  --sup_passive_queue_type                priority_queues
% 27.55/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.55/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.55/4.00  --demod_completeness_check              fast
% 27.55/4.00  --demod_use_ground                      true
% 27.55/4.00  --sup_to_prop_solver                    passive
% 27.55/4.00  --sup_prop_simpl_new                    true
% 27.55/4.00  --sup_prop_simpl_given                  true
% 27.55/4.00  --sup_fun_splitting                     true
% 27.55/4.00  --sup_smt_interval                      50000
% 27.55/4.00  
% 27.55/4.00  ------ Superposition Simplification Setup
% 27.55/4.00  
% 27.55/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.55/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.55/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.55/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.55/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.55/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.55/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.55/4.00  --sup_immed_triv                        [TrivRules]
% 27.55/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.55/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.55/4.00  --sup_immed_bw_main                     []
% 27.55/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.55/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.55/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.55/4.00  --sup_input_bw                          []
% 27.55/4.00  
% 27.55/4.00  ------ Combination Options
% 27.55/4.00  
% 27.55/4.00  --comb_res_mult                         3
% 27.55/4.00  --comb_sup_mult                         2
% 27.55/4.00  --comb_inst_mult                        10
% 27.55/4.00  
% 27.55/4.00  ------ Debug Options
% 27.55/4.00  
% 27.55/4.00  --dbg_backtrace                         false
% 27.55/4.00  --dbg_dump_prop_clauses                 false
% 27.55/4.00  --dbg_dump_prop_clauses_file            -
% 27.55/4.00  --dbg_out_stat                          false
% 27.55/4.00  ------ Parsing...
% 27.55/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.55/4.00  
% 27.55/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.55/4.00  
% 27.55/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.55/4.00  
% 27.55/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.55/4.00  ------ Proving...
% 27.55/4.00  ------ Problem Properties 
% 27.55/4.00  
% 27.55/4.00  
% 27.55/4.00  clauses                                 39
% 27.55/4.00  conjectures                             6
% 27.55/4.00  EPR                                     8
% 27.55/4.00  Horn                                    28
% 27.55/4.00  unary                                   13
% 27.55/4.00  binary                                  10
% 27.55/4.00  lits                                    94
% 27.55/4.00  lits eq                                 47
% 27.55/4.00  fd_pure                                 0
% 27.55/4.00  fd_pseudo                               0
% 27.55/4.00  fd_cond                                 8
% 27.55/4.00  fd_pseudo_cond                          4
% 27.55/4.00  AC symbols                              0
% 27.55/4.00  
% 27.55/4.00  ------ Schedule dynamic 5 is on 
% 27.55/4.00  
% 27.55/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.55/4.00  
% 27.55/4.00  
% 27.55/4.00  ------ 
% 27.55/4.00  Current options:
% 27.55/4.00  ------ 
% 27.55/4.00  
% 27.55/4.00  ------ Input Options
% 27.55/4.00  
% 27.55/4.00  --out_options                           all
% 27.55/4.00  --tptp_safe_out                         true
% 27.55/4.00  --problem_path                          ""
% 27.55/4.00  --include_path                          ""
% 27.55/4.00  --clausifier                            res/vclausify_rel
% 27.55/4.00  --clausifier_options                    ""
% 27.55/4.00  --stdin                                 false
% 27.55/4.00  --stats_out                             all
% 27.55/4.00  
% 27.55/4.00  ------ General Options
% 27.55/4.00  
% 27.55/4.00  --fof                                   false
% 27.55/4.00  --time_out_real                         305.
% 27.55/4.00  --time_out_virtual                      -1.
% 27.55/4.00  --symbol_type_check                     false
% 27.55/4.00  --clausify_out                          false
% 27.55/4.00  --sig_cnt_out                           false
% 27.55/4.00  --trig_cnt_out                          false
% 27.55/4.00  --trig_cnt_out_tolerance                1.
% 27.55/4.00  --trig_cnt_out_sk_spl                   false
% 27.55/4.00  --abstr_cl_out                          false
% 27.55/4.00  
% 27.55/4.00  ------ Global Options
% 27.55/4.00  
% 27.55/4.00  --schedule                              default
% 27.55/4.00  --add_important_lit                     false
% 27.55/4.00  --prop_solver_per_cl                    1000
% 27.55/4.00  --min_unsat_core                        false
% 27.55/4.00  --soft_assumptions                      false
% 27.55/4.00  --soft_lemma_size                       3
% 27.55/4.00  --prop_impl_unit_size                   0
% 27.55/4.00  --prop_impl_unit                        []
% 27.55/4.00  --share_sel_clauses                     true
% 27.55/4.00  --reset_solvers                         false
% 27.55/4.00  --bc_imp_inh                            [conj_cone]
% 27.55/4.00  --conj_cone_tolerance                   3.
% 27.55/4.00  --extra_neg_conj                        none
% 27.55/4.00  --large_theory_mode                     true
% 27.55/4.00  --prolific_symb_bound                   200
% 27.55/4.00  --lt_threshold                          2000
% 27.55/4.00  --clause_weak_htbl                      true
% 27.55/4.00  --gc_record_bc_elim                     false
% 27.55/4.00  
% 27.55/4.00  ------ Preprocessing Options
% 27.55/4.00  
% 27.55/4.00  --preprocessing_flag                    true
% 27.55/4.00  --time_out_prep_mult                    0.1
% 27.55/4.00  --splitting_mode                        input
% 27.55/4.00  --splitting_grd                         true
% 27.55/4.00  --splitting_cvd                         false
% 27.55/4.00  --splitting_cvd_svl                     false
% 27.55/4.00  --splitting_nvd                         32
% 27.55/4.00  --sub_typing                            true
% 27.55/4.00  --prep_gs_sim                           true
% 27.55/4.00  --prep_unflatten                        true
% 27.55/4.00  --prep_res_sim                          true
% 27.55/4.00  --prep_upred                            true
% 27.55/4.00  --prep_sem_filter                       exhaustive
% 27.55/4.00  --prep_sem_filter_out                   false
% 27.55/4.00  --pred_elim                             true
% 27.55/4.00  --res_sim_input                         true
% 27.55/4.00  --eq_ax_congr_red                       true
% 27.55/4.00  --pure_diseq_elim                       true
% 27.55/4.00  --brand_transform                       false
% 27.55/4.00  --non_eq_to_eq                          false
% 27.55/4.00  --prep_def_merge                        true
% 27.55/4.00  --prep_def_merge_prop_impl              false
% 27.55/4.00  --prep_def_merge_mbd                    true
% 27.55/4.00  --prep_def_merge_tr_red                 false
% 27.55/4.00  --prep_def_merge_tr_cl                  false
% 27.55/4.00  --smt_preprocessing                     true
% 27.55/4.00  --smt_ac_axioms                         fast
% 27.55/4.00  --preprocessed_out                      false
% 27.55/4.00  --preprocessed_stats                    false
% 27.55/4.00  
% 27.55/4.00  ------ Abstraction refinement Options
% 27.55/4.00  
% 27.55/4.00  --abstr_ref                             []
% 27.55/4.00  --abstr_ref_prep                        false
% 27.55/4.00  --abstr_ref_until_sat                   false
% 27.55/4.00  --abstr_ref_sig_restrict                funpre
% 27.55/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.55/4.00  --abstr_ref_under                       []
% 27.55/4.00  
% 27.55/4.00  ------ SAT Options
% 27.55/4.00  
% 27.55/4.00  --sat_mode                              false
% 27.55/4.00  --sat_fm_restart_options                ""
% 27.55/4.00  --sat_gr_def                            false
% 27.55/4.00  --sat_epr_types                         true
% 27.55/4.00  --sat_non_cyclic_types                  false
% 27.55/4.00  --sat_finite_models                     false
% 27.55/4.00  --sat_fm_lemmas                         false
% 27.55/4.00  --sat_fm_prep                           false
% 27.55/4.00  --sat_fm_uc_incr                        true
% 27.55/4.00  --sat_out_model                         small
% 27.55/4.00  --sat_out_clauses                       false
% 27.55/4.00  
% 27.55/4.00  ------ QBF Options
% 27.55/4.00  
% 27.55/4.00  --qbf_mode                              false
% 27.55/4.00  --qbf_elim_univ                         false
% 27.55/4.00  --qbf_dom_inst                          none
% 27.55/4.00  --qbf_dom_pre_inst                      false
% 27.55/4.00  --qbf_sk_in                             false
% 27.55/4.00  --qbf_pred_elim                         true
% 27.55/4.00  --qbf_split                             512
% 27.55/4.00  
% 27.55/4.00  ------ BMC1 Options
% 27.55/4.00  
% 27.55/4.00  --bmc1_incremental                      false
% 27.55/4.00  --bmc1_axioms                           reachable_all
% 27.55/4.00  --bmc1_min_bound                        0
% 27.55/4.00  --bmc1_max_bound                        -1
% 27.55/4.00  --bmc1_max_bound_default                -1
% 27.55/4.00  --bmc1_symbol_reachability              true
% 27.55/4.00  --bmc1_property_lemmas                  false
% 27.55/4.00  --bmc1_k_induction                      false
% 27.55/4.00  --bmc1_non_equiv_states                 false
% 27.55/4.00  --bmc1_deadlock                         false
% 27.55/4.00  --bmc1_ucm                              false
% 27.55/4.00  --bmc1_add_unsat_core                   none
% 27.55/4.00  --bmc1_unsat_core_children              false
% 27.55/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.55/4.00  --bmc1_out_stat                         full
% 27.55/4.00  --bmc1_ground_init                      false
% 27.55/4.00  --bmc1_pre_inst_next_state              false
% 27.55/4.00  --bmc1_pre_inst_state                   false
% 27.55/4.00  --bmc1_pre_inst_reach_state             false
% 27.55/4.00  --bmc1_out_unsat_core                   false
% 27.55/4.00  --bmc1_aig_witness_out                  false
% 27.55/4.00  --bmc1_verbose                          false
% 27.55/4.00  --bmc1_dump_clauses_tptp                false
% 27.55/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.55/4.00  --bmc1_dump_file                        -
% 27.55/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.55/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.55/4.00  --bmc1_ucm_extend_mode                  1
% 27.55/4.00  --bmc1_ucm_init_mode                    2
% 27.55/4.00  --bmc1_ucm_cone_mode                    none
% 27.55/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.55/4.00  --bmc1_ucm_relax_model                  4
% 27.55/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.55/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.55/4.00  --bmc1_ucm_layered_model                none
% 27.55/4.00  --bmc1_ucm_max_lemma_size               10
% 27.55/4.00  
% 27.55/4.00  ------ AIG Options
% 27.55/4.00  
% 27.55/4.00  --aig_mode                              false
% 27.55/4.00  
% 27.55/4.00  ------ Instantiation Options
% 27.55/4.00  
% 27.55/4.00  --instantiation_flag                    true
% 27.55/4.00  --inst_sos_flag                         true
% 27.55/4.00  --inst_sos_phase                        true
% 27.55/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.55/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.55/4.00  --inst_lit_sel_side                     none
% 27.55/4.00  --inst_solver_per_active                1400
% 27.55/4.00  --inst_solver_calls_frac                1.
% 27.55/4.00  --inst_passive_queue_type               priority_queues
% 27.55/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.55/4.00  --inst_passive_queues_freq              [25;2]
% 27.55/4.00  --inst_dismatching                      true
% 27.55/4.00  --inst_eager_unprocessed_to_passive     true
% 27.55/4.00  --inst_prop_sim_given                   true
% 27.55/4.00  --inst_prop_sim_new                     false
% 27.55/4.00  --inst_subs_new                         false
% 27.55/4.00  --inst_eq_res_simp                      false
% 27.55/4.00  --inst_subs_given                       false
% 27.55/4.00  --inst_orphan_elimination               true
% 27.55/4.00  --inst_learning_loop_flag               true
% 27.55/4.00  --inst_learning_start                   3000
% 27.55/4.00  --inst_learning_factor                  2
% 27.55/4.00  --inst_start_prop_sim_after_learn       3
% 27.55/4.00  --inst_sel_renew                        solver
% 27.55/4.00  --inst_lit_activity_flag                true
% 27.55/4.00  --inst_restr_to_given                   false
% 27.55/4.00  --inst_activity_threshold               500
% 27.55/4.00  --inst_out_proof                        true
% 27.55/4.00  
% 27.55/4.00  ------ Resolution Options
% 27.55/4.00  
% 27.55/4.00  --resolution_flag                       false
% 27.55/4.00  --res_lit_sel                           adaptive
% 27.55/4.00  --res_lit_sel_side                      none
% 27.55/4.00  --res_ordering                          kbo
% 27.55/4.00  --res_to_prop_solver                    active
% 27.55/4.00  --res_prop_simpl_new                    false
% 27.55/4.00  --res_prop_simpl_given                  true
% 27.55/4.00  --res_passive_queue_type                priority_queues
% 27.55/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.55/4.00  --res_passive_queues_freq               [15;5]
% 27.55/4.00  --res_forward_subs                      full
% 27.55/4.00  --res_backward_subs                     full
% 27.55/4.00  --res_forward_subs_resolution           true
% 27.55/4.00  --res_backward_subs_resolution          true
% 27.55/4.00  --res_orphan_elimination                true
% 27.55/4.00  --res_time_limit                        2.
% 27.55/4.00  --res_out_proof                         true
% 27.55/4.00  
% 27.55/4.00  ------ Superposition Options
% 27.55/4.00  
% 27.55/4.00  --superposition_flag                    true
% 27.55/4.00  --sup_passive_queue_type                priority_queues
% 27.55/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.55/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.55/4.00  --demod_completeness_check              fast
% 27.55/4.00  --demod_use_ground                      true
% 27.55/4.00  --sup_to_prop_solver                    passive
% 27.55/4.00  --sup_prop_simpl_new                    true
% 27.55/4.00  --sup_prop_simpl_given                  true
% 27.55/4.00  --sup_fun_splitting                     true
% 27.55/4.00  --sup_smt_interval                      50000
% 27.55/4.00  
% 27.55/4.00  ------ Superposition Simplification Setup
% 27.55/4.00  
% 27.55/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.55/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.55/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.55/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.55/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.55/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.55/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.55/4.00  --sup_immed_triv                        [TrivRules]
% 27.55/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.55/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.55/4.00  --sup_immed_bw_main                     []
% 27.55/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.55/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.55/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.55/4.00  --sup_input_bw                          []
% 27.55/4.00  
% 27.55/4.00  ------ Combination Options
% 27.55/4.00  
% 27.55/4.00  --comb_res_mult                         3
% 27.55/4.00  --comb_sup_mult                         2
% 27.55/4.00  --comb_inst_mult                        10
% 27.55/4.00  
% 27.55/4.00  ------ Debug Options
% 27.55/4.00  
% 27.55/4.00  --dbg_backtrace                         false
% 27.55/4.00  --dbg_dump_prop_clauses                 false
% 27.55/4.00  --dbg_dump_prop_clauses_file            -
% 27.55/4.00  --dbg_out_stat                          false
% 27.55/4.00  
% 27.55/4.00  
% 27.55/4.00  
% 27.55/4.00  
% 27.55/4.00  ------ Proving...
% 27.55/4.00  
% 27.55/4.00  
% 27.55/4.00  % SZS status Theorem for theBenchmark.p
% 27.55/4.00  
% 27.55/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.55/4.00  
% 27.55/4.00  fof(f15,conjecture,(
% 27.55/4.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f16,negated_conjecture,(
% 27.55/4.00    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 27.55/4.00    inference(negated_conjecture,[],[f15])).
% 27.55/4.00  
% 27.55/4.00  fof(f24,plain,(
% 27.55/4.00    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 27.55/4.00    inference(ennf_transformation,[],[f16])).
% 27.55/4.00  
% 27.55/4.00  fof(f25,plain,(
% 27.55/4.00    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 27.55/4.00    inference(flattening,[],[f24])).
% 27.55/4.00  
% 27.55/4.00  fof(f43,plain,(
% 27.55/4.00    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 & k1_xboole_0 != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & ! [X5] : (! [X6] : (! [X7] : (sK12 = X7 | k3_mcart_1(X5,X6,X7) != sK13 | ~m1_subset_1(X7,sK11)) | ~m1_subset_1(X6,sK10)) | ~m1_subset_1(X5,sK9)) & m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11)))),
% 27.55/4.00    introduced(choice_axiom,[])).
% 27.55/4.00  
% 27.55/4.00  fof(f44,plain,(
% 27.55/4.00    k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 & k1_xboole_0 != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & ! [X5] : (! [X6] : (! [X7] : (sK12 = X7 | k3_mcart_1(X5,X6,X7) != sK13 | ~m1_subset_1(X7,sK11)) | ~m1_subset_1(X6,sK10)) | ~m1_subset_1(X5,sK9)) & m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11))),
% 27.55/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f25,f43])).
% 27.55/4.00  
% 27.55/4.00  fof(f81,plain,(
% 27.55/4.00    m1_subset_1(sK13,k3_zfmisc_1(sK9,sK10,sK11))),
% 27.55/4.00    inference(cnf_transformation,[],[f44])).
% 27.55/4.00  
% 27.55/4.00  fof(f6,axiom,(
% 27.55/4.00    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f61,plain,(
% 27.55/4.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f6])).
% 27.55/4.00  
% 27.55/4.00  fof(f97,plain,(
% 27.55/4.00    m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))),
% 27.55/4.00    inference(definition_unfolding,[],[f81,f61])).
% 27.55/4.00  
% 27.55/4.00  fof(f4,axiom,(
% 27.55/4.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f18,plain,(
% 27.55/4.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 27.55/4.00    inference(ennf_transformation,[],[f4])).
% 27.55/4.00  
% 27.55/4.00  fof(f38,plain,(
% 27.55/4.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 27.55/4.00    inference(nnf_transformation,[],[f18])).
% 27.55/4.00  
% 27.55/4.00  fof(f56,plain,(
% 27.55/4.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f38])).
% 27.55/4.00  
% 27.55/4.00  fof(f8,axiom,(
% 27.55/4.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f19,plain,(
% 27.55/4.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 27.55/4.00    inference(ennf_transformation,[],[f8])).
% 27.55/4.00  
% 27.55/4.00  fof(f63,plain,(
% 27.55/4.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 27.55/4.00    inference(cnf_transformation,[],[f19])).
% 27.55/4.00  
% 27.55/4.00  fof(f3,axiom,(
% 27.55/4.00    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f17,plain,(
% 27.55/4.00    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 27.55/4.00    inference(ennf_transformation,[],[f3])).
% 27.55/4.00  
% 27.55/4.00  fof(f36,plain,(
% 27.55/4.00    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK6(X0),sK7(X0)) = X0)),
% 27.55/4.00    introduced(choice_axiom,[])).
% 27.55/4.00  
% 27.55/4.00  fof(f37,plain,(
% 27.55/4.00    ! [X0,X1,X2] : (k4_tarski(sK6(X0),sK7(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 27.55/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f36])).
% 27.55/4.00  
% 27.55/4.00  fof(f55,plain,(
% 27.55/4.00    ( ! [X2,X0,X1] : (k4_tarski(sK6(X0),sK7(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 27.55/4.00    inference(cnf_transformation,[],[f37])).
% 27.55/4.00  
% 27.55/4.00  fof(f58,plain,(
% 27.55/4.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f38])).
% 27.55/4.00  
% 27.55/4.00  fof(f11,axiom,(
% 27.55/4.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f22,plain,(
% 27.55/4.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 27.55/4.00    inference(ennf_transformation,[],[f11])).
% 27.55/4.00  
% 27.55/4.00  fof(f39,plain,(
% 27.55/4.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK8(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK8(X0),X0)))),
% 27.55/4.00    introduced(choice_axiom,[])).
% 27.55/4.00  
% 27.55/4.00  fof(f40,plain,(
% 27.55/4.00    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK8(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK8(X0),X0)) | k1_xboole_0 = X0)),
% 27.55/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f39])).
% 27.55/4.00  
% 27.55/4.00  fof(f68,plain,(
% 27.55/4.00    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 27.55/4.00    inference(cnf_transformation,[],[f40])).
% 27.55/4.00  
% 27.55/4.00  fof(f1,axiom,(
% 27.55/4.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f26,plain,(
% 27.55/4.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 27.55/4.00    inference(nnf_transformation,[],[f1])).
% 27.55/4.00  
% 27.55/4.00  fof(f27,plain,(
% 27.55/4.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 27.55/4.00    inference(rectify,[],[f26])).
% 27.55/4.00  
% 27.55/4.00  fof(f28,plain,(
% 27.55/4.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 27.55/4.00    introduced(choice_axiom,[])).
% 27.55/4.00  
% 27.55/4.00  fof(f29,plain,(
% 27.55/4.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 27.55/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 27.55/4.00  
% 27.55/4.00  fof(f45,plain,(
% 27.55/4.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f29])).
% 27.55/4.00  
% 27.55/4.00  fof(f14,axiom,(
% 27.55/4.00    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f79,plain,(
% 27.55/4.00    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 27.55/4.00    inference(cnf_transformation,[],[f14])).
% 27.55/4.00  
% 27.55/4.00  fof(f80,plain,(
% 27.55/4.00    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 27.55/4.00    inference(cnf_transformation,[],[f14])).
% 27.55/4.00  
% 27.55/4.00  fof(f64,plain,(
% 27.55/4.00    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 27.55/4.00    inference(cnf_transformation,[],[f19])).
% 27.55/4.00  
% 27.55/4.00  fof(f57,plain,(
% 27.55/4.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f38])).
% 27.55/4.00  
% 27.55/4.00  fof(f12,axiom,(
% 27.55/4.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f23,plain,(
% 27.55/4.00    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 27.55/4.00    inference(ennf_transformation,[],[f12])).
% 27.55/4.00  
% 27.55/4.00  fof(f73,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.55/4.00    inference(cnf_transformation,[],[f23])).
% 27.55/4.00  
% 27.55/4.00  fof(f88,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.55/4.00    inference(definition_unfolding,[],[f73,f61])).
% 27.55/4.00  
% 27.55/4.00  fof(f83,plain,(
% 27.55/4.00    k1_xboole_0 != sK9),
% 27.55/4.00    inference(cnf_transformation,[],[f44])).
% 27.55/4.00  
% 27.55/4.00  fof(f84,plain,(
% 27.55/4.00    k1_xboole_0 != sK10),
% 27.55/4.00    inference(cnf_transformation,[],[f44])).
% 27.55/4.00  
% 27.55/4.00  fof(f85,plain,(
% 27.55/4.00    k1_xboole_0 != sK11),
% 27.55/4.00    inference(cnf_transformation,[],[f44])).
% 27.55/4.00  
% 27.55/4.00  fof(f86,plain,(
% 27.55/4.00    k7_mcart_1(sK9,sK10,sK11,sK13) != sK12),
% 27.55/4.00    inference(cnf_transformation,[],[f44])).
% 27.55/4.00  
% 27.55/4.00  fof(f82,plain,(
% 27.55/4.00    ( ! [X6,X7,X5] : (sK12 = X7 | k3_mcart_1(X5,X6,X7) != sK13 | ~m1_subset_1(X7,sK11) | ~m1_subset_1(X6,sK10) | ~m1_subset_1(X5,sK9)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f44])).
% 27.55/4.00  
% 27.55/4.00  fof(f5,axiom,(
% 27.55/4.00    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f60,plain,(
% 27.55/4.00    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f5])).
% 27.55/4.00  
% 27.55/4.00  fof(f96,plain,(
% 27.55/4.00    ( ! [X6,X7,X5] : (sK12 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK13 | ~m1_subset_1(X7,sK11) | ~m1_subset_1(X6,sK10) | ~m1_subset_1(X5,sK9)) )),
% 27.55/4.00    inference(definition_unfolding,[],[f82,f60])).
% 27.55/4.00  
% 27.55/4.00  fof(f13,axiom,(
% 27.55/4.00    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f41,plain,(
% 27.55/4.00    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 27.55/4.00    inference(nnf_transformation,[],[f13])).
% 27.55/4.00  
% 27.55/4.00  fof(f42,plain,(
% 27.55/4.00    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 27.55/4.00    inference(flattening,[],[f41])).
% 27.55/4.00  
% 27.55/4.00  fof(f74,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.55/4.00    inference(cnf_transformation,[],[f42])).
% 27.55/4.00  
% 27.55/4.00  fof(f7,axiom,(
% 27.55/4.00    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f62,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f7])).
% 27.55/4.00  
% 27.55/4.00  fof(f87,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 27.55/4.00    inference(definition_unfolding,[],[f62,f61])).
% 27.55/4.00  
% 27.55/4.00  fof(f95,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.55/4.00    inference(definition_unfolding,[],[f74,f87])).
% 27.55/4.00  
% 27.55/4.00  fof(f2,axiom,(
% 27.55/4.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f30,plain,(
% 27.55/4.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 27.55/4.00    inference(nnf_transformation,[],[f2])).
% 27.55/4.00  
% 27.55/4.00  fof(f31,plain,(
% 27.55/4.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 27.55/4.00    inference(rectify,[],[f30])).
% 27.55/4.00  
% 27.55/4.00  fof(f34,plain,(
% 27.55/4.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 27.55/4.00    introduced(choice_axiom,[])).
% 27.55/4.00  
% 27.55/4.00  fof(f33,plain,(
% 27.55/4.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 27.55/4.00    introduced(choice_axiom,[])).
% 27.55/4.00  
% 27.55/4.00  fof(f32,plain,(
% 27.55/4.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 27.55/4.00    introduced(choice_axiom,[])).
% 27.55/4.00  
% 27.55/4.00  fof(f35,plain,(
% 27.55/4.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 27.55/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f31,f34,f33,f32])).
% 27.55/4.00  
% 27.55/4.00  fof(f51,plain,(
% 27.55/4.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f35])).
% 27.55/4.00  
% 27.55/4.00  fof(f46,plain,(
% 27.55/4.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f29])).
% 27.55/4.00  
% 27.55/4.00  fof(f77,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 27.55/4.00    inference(cnf_transformation,[],[f42])).
% 27.55/4.00  
% 27.55/4.00  fof(f92,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 27.55/4.00    inference(definition_unfolding,[],[f77,f87])).
% 27.55/4.00  
% 27.55/4.00  fof(f106,plain,(
% 27.55/4.00    ( ! [X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) = k1_xboole_0) )),
% 27.55/4.00    inference(equality_resolution,[],[f92])).
% 27.55/4.00  
% 27.55/4.00  fof(f10,axiom,(
% 27.55/4.00    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 27.55/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.55/4.00  
% 27.55/4.00  fof(f21,plain,(
% 27.55/4.00    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 27.55/4.00    inference(ennf_transformation,[],[f10])).
% 27.55/4.00  
% 27.55/4.00  fof(f67,plain,(
% 27.55/4.00    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 27.55/4.00    inference(cnf_transformation,[],[f21])).
% 27.55/4.00  
% 27.55/4.00  fof(f75,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 27.55/4.00    inference(cnf_transformation,[],[f42])).
% 27.55/4.00  
% 27.55/4.00  fof(f94,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 27.55/4.00    inference(definition_unfolding,[],[f75,f87])).
% 27.55/4.00  
% 27.55/4.00  fof(f108,plain,(
% 27.55/4.00    ( ! [X2,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0) )),
% 27.55/4.00    inference(equality_resolution,[],[f94])).
% 27.55/4.00  
% 27.55/4.00  fof(f50,plain,(
% 27.55/4.00    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 27.55/4.00    inference(cnf_transformation,[],[f35])).
% 27.55/4.00  
% 27.55/4.00  fof(f98,plain,(
% 27.55/4.00    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 27.55/4.00    inference(equality_resolution,[],[f50])).
% 27.55/4.00  
% 27.55/4.00  fof(f99,plain,(
% 27.55/4.00    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 27.55/4.00    inference(equality_resolution,[],[f98])).
% 27.55/4.00  
% 27.55/4.00  fof(f78,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 27.55/4.00    inference(cnf_transformation,[],[f42])).
% 27.55/4.00  
% 27.55/4.00  fof(f91,plain,(
% 27.55/4.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 27.55/4.00    inference(definition_unfolding,[],[f78,f87])).
% 27.55/4.00  
% 27.55/4.00  fof(f105,plain,(
% 27.55/4.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) = k1_xboole_0) )),
% 27.55/4.00    inference(equality_resolution,[],[f91])).
% 27.55/4.00  
% 27.55/4.00  fof(f59,plain,(
% 27.55/4.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 27.55/4.00    inference(cnf_transformation,[],[f38])).
% 27.55/4.00  
% 27.55/4.00  fof(f47,plain,(
% 27.55/4.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 27.55/4.00    inference(cnf_transformation,[],[f35])).
% 27.55/4.00  
% 27.55/4.00  fof(f102,plain,(
% 27.55/4.00    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 27.55/4.00    inference(equality_resolution,[],[f47])).
% 27.55/4.00  
% 27.55/4.00  fof(f49,plain,(
% 27.55/4.00    ( ! [X2,X0,X8,X1] : (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 27.55/4.00    inference(cnf_transformation,[],[f35])).
% 27.55/4.00  
% 27.55/4.00  fof(f100,plain,(
% 27.55/4.00    ( ! [X0,X8,X1] : (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 27.55/4.00    inference(equality_resolution,[],[f49])).
% 27.55/4.00  
% 27.55/4.00  fof(f48,plain,(
% 27.55/4.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 27.55/4.00    inference(cnf_transformation,[],[f35])).
% 27.55/4.00  
% 27.55/4.00  fof(f101,plain,(
% 27.55/4.00    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 27.55/4.00    inference(equality_resolution,[],[f48])).
% 27.55/4.00  
% 27.55/4.00  cnf(c_38,negated_conjecture,
% 27.55/4.00      ( m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
% 27.55/4.00      inference(cnf_transformation,[],[f97]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_729,plain,
% 27.55/4.00      ( m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_14,plain,
% 27.55/4.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 27.55/4.00      inference(cnf_transformation,[],[f56]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_740,plain,
% 27.55/4.00      ( m1_subset_1(X0,X1) != iProver_top
% 27.55/4.00      | r2_hidden(X0,X1) = iProver_top
% 27.55/4.00      | v1_xboole_0(X1) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2833,plain,
% 27.55/4.00      ( r2_hidden(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_729,c_740]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_16,plain,
% 27.55/4.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 27.55/4.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 27.55/4.00      inference(cnf_transformation,[],[f63]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_738,plain,
% 27.55/4.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.55/4.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2841,plain,
% 27.55/4.00      ( r2_hidden(k1_mcart_1(sK13),k2_zfmisc_1(sK9,sK10)) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2833,c_738]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_10,plain,
% 27.55/4.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 27.55/4.00      | k4_tarski(sK6(X0),sK7(X0)) = X0 ),
% 27.55/4.00      inference(cnf_transformation,[],[f55]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_743,plain,
% 27.55/4.00      ( k4_tarski(sK6(X0),sK7(X0)) = X0
% 27.55/4.00      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3027,plain,
% 27.55/4.00      ( k4_tarski(sK6(k1_mcart_1(sK13)),sK7(k1_mcart_1(sK13))) = k1_mcart_1(sK13)
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2841,c_743]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_12,plain,
% 27.55/4.00      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 27.55/4.00      inference(cnf_transformation,[],[f58]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_741,plain,
% 27.55/4.00      ( m1_subset_1(X0,X1) != iProver_top
% 27.55/4.00      | v1_xboole_0(X1) != iProver_top
% 27.55/4.00      | v1_xboole_0(X0) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3473,plain,
% 27.55/4.00      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_729,c_741]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_14716,plain,
% 27.55/4.00      ( k4_tarski(sK6(k1_mcart_1(sK13)),sK7(k1_mcart_1(sK13))) = k1_mcart_1(sK13)
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_3027,c_3473]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_22,plain,
% 27.55/4.00      ( r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0 ),
% 27.55/4.00      inference(cnf_transformation,[],[f68]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_734,plain,
% 27.55/4.00      ( k1_xboole_0 = X0 | r2_hidden(sK8(X0),X0) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_1,plain,
% 27.55/4.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 27.55/4.00      inference(cnf_transformation,[],[f45]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_752,plain,
% 27.55/4.00      ( r2_hidden(X0,X1) != iProver_top
% 27.55/4.00      | v1_xboole_0(X1) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2265,plain,
% 27.55/4.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_734,c_752]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_14943,plain,
% 27.55/4.00      ( k4_tarski(sK6(k1_mcart_1(sK13)),sK7(k1_mcart_1(sK13))) = k1_mcart_1(sK13)
% 27.55/4.00      | sK13 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_14716,c_2265]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_32,plain,
% 27.55/4.00      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 27.55/4.00      inference(cnf_transformation,[],[f79]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_14953,plain,
% 27.55/4.00      ( k1_mcart_1(k1_mcart_1(sK13)) = sK6(k1_mcart_1(sK13))
% 27.55/4.00      | sK13 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_14943,c_32]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3029,plain,
% 27.55/4.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK13)),sK9) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2841,c_738]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7893,plain,
% 27.55/4.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK13)),sK9) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_3029,c_3473]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_16610,plain,
% 27.55/4.00      ( sK13 = k1_xboole_0
% 27.55/4.00      | r2_hidden(sK6(k1_mcart_1(sK13)),sK9) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_14953,c_7893]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2839,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2833,c_743]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4002,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2839,c_3473]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4300,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13 | sK13 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_4002,c_2265]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_31,plain,
% 27.55/4.00      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 27.55/4.00      inference(cnf_transformation,[],[f80]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_5106,plain,
% 27.55/4.00      ( k2_mcart_1(sK13) = sK7(sK13) | sK13 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_4300,c_31]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_15,plain,
% 27.55/4.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 27.55/4.00      | r2_hidden(k2_mcart_1(X0),X2) ),
% 27.55/4.00      inference(cnf_transformation,[],[f64]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_739,plain,
% 27.55/4.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.55/4.00      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2840,plain,
% 27.55/4.00      ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2833,c_739]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4003,plain,
% 27.55/4.00      ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2840,c_3473]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_13,plain,
% 27.55/4.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 27.55/4.00      inference(cnf_transformation,[],[f57]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_182,plain,
% 27.55/4.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_13,c_1]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_183,plain,
% 27.55/4.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 27.55/4.00      inference(renaming,[status(thm)],[c_182]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_728,plain,
% 27.55/4.00      ( m1_subset_1(X0,X1) = iProver_top
% 27.55/4.00      | r2_hidden(X0,X1) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4295,plain,
% 27.55/4.00      ( m1_subset_1(k2_mcart_1(sK13),sK11) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_4003,c_728]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_5829,plain,
% 27.55/4.00      ( sK13 = k1_xboole_0
% 27.55/4.00      | m1_subset_1(sK7(sK13),sK11) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_5106,c_4295]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_23,plain,
% 27.55/4.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 27.55/4.00      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 27.55/4.00      | k1_xboole_0 = X2
% 27.55/4.00      | k1_xboole_0 = X1
% 27.55/4.00      | k1_xboole_0 = X3 ),
% 27.55/4.00      inference(cnf_transformation,[],[f88]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_733,plain,
% 27.55/4.00      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 27.55/4.00      | k1_xboole_0 = X1
% 27.55/4.00      | k1_xboole_0 = X0
% 27.55/4.00      | k1_xboole_0 = X2
% 27.55/4.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3245,plain,
% 27.55/4.00      ( k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13)
% 27.55/4.00      | sK11 = k1_xboole_0
% 27.55/4.00      | sK10 = k1_xboole_0
% 27.55/4.00      | sK9 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_729,c_733]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_36,negated_conjecture,
% 27.55/4.00      ( k1_xboole_0 != sK9 ),
% 27.55/4.00      inference(cnf_transformation,[],[f83]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_35,negated_conjecture,
% 27.55/4.00      ( k1_xboole_0 != sK10 ),
% 27.55/4.00      inference(cnf_transformation,[],[f84]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_34,negated_conjecture,
% 27.55/4.00      ( k1_xboole_0 != sK11 ),
% 27.55/4.00      inference(cnf_transformation,[],[f85]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_822,plain,
% 27.55/4.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK10),X2))
% 27.55/4.00      | k7_mcart_1(X1,sK10,X2,X0) = k2_mcart_1(X0)
% 27.55/4.00      | k1_xboole_0 = X2
% 27.55/4.00      | k1_xboole_0 = X1
% 27.55/4.00      | k1_xboole_0 = sK10 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_23]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_1268,plain,
% 27.55/4.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK10),sK11))
% 27.55/4.00      | k7_mcart_1(X1,sK10,sK11,X0) = k2_mcart_1(X0)
% 27.55/4.00      | k1_xboole_0 = X1
% 27.55/4.00      | k1_xboole_0 = sK11
% 27.55/4.00      | k1_xboole_0 = sK10 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_822]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_1859,plain,
% 27.55/4.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
% 27.55/4.00      | k7_mcart_1(sK9,sK10,sK11,X0) = k2_mcart_1(X0)
% 27.55/4.00      | k1_xboole_0 = sK11
% 27.55/4.00      | k1_xboole_0 = sK10
% 27.55/4.00      | k1_xboole_0 = sK9 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_1268]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2806,plain,
% 27.55/4.00      ( ~ m1_subset_1(sK13,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
% 27.55/4.00      | k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13)
% 27.55/4.00      | k1_xboole_0 = sK11
% 27.55/4.00      | k1_xboole_0 = sK10
% 27.55/4.00      | k1_xboole_0 = sK9 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_1859]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4007,plain,
% 27.55/4.00      ( k7_mcart_1(sK9,sK10,sK11,sK13) = k2_mcart_1(sK13) ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_3245,c_38,c_36,c_35,c_34,c_2806]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_33,negated_conjecture,
% 27.55/4.00      ( k7_mcart_1(sK9,sK10,sK11,sK13) != sK12 ),
% 27.55/4.00      inference(cnf_transformation,[],[f86]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4009,plain,
% 27.55/4.00      ( k2_mcart_1(sK13) != sK12 ),
% 27.55/4.00      inference(demodulation,[status(thm)],[c_4007,c_33]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_5831,plain,
% 27.55/4.00      ( sK7(sK13) != sK12 | sK13 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_5106,c_4009]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7900,plain,
% 27.55/4.00      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK13)),sK9) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_7893,c_728]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_16609,plain,
% 27.55/4.00      ( sK13 = k1_xboole_0
% 27.55/4.00      | m1_subset_1(sK6(k1_mcart_1(sK13)),sK9) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_14953,c_7900]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_14954,plain,
% 27.55/4.00      ( k2_mcart_1(k1_mcart_1(sK13)) = sK7(k1_mcart_1(sK13))
% 27.55/4.00      | sK13 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_14943,c_31]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3028,plain,
% 27.55/4.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK13)),sK10) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2841,c_739]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_5373,plain,
% 27.55/4.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK13)),sK10) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_3028,c_3473]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_5379,plain,
% 27.55/4.00      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK13)),sK10) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_5373,c_728]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_16910,plain,
% 27.55/4.00      ( sK13 = k1_xboole_0
% 27.55/4.00      | m1_subset_1(sK7(k1_mcart_1(sK13)),sK10) = iProver_top
% 27.55/4.00      | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_14954,c_5379]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_5105,plain,
% 27.55/4.00      ( k1_mcart_1(sK13) = sK6(sK13) | sK13 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_4300,c_32]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_37,negated_conjecture,
% 27.55/4.00      ( ~ m1_subset_1(X0,sK11)
% 27.55/4.00      | ~ m1_subset_1(X1,sK10)
% 27.55/4.00      | ~ m1_subset_1(X2,sK9)
% 27.55/4.00      | k4_tarski(k4_tarski(X2,X1),X0) != sK13
% 27.55/4.00      | sK12 = X0 ),
% 27.55/4.00      inference(cnf_transformation,[],[f96]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_730,plain,
% 27.55/4.00      ( k4_tarski(k4_tarski(X0,X1),X2) != sK13
% 27.55/4.00      | sK12 = X2
% 27.55/4.00      | m1_subset_1(X2,sK11) != iProver_top
% 27.55/4.00      | m1_subset_1(X1,sK10) != iProver_top
% 27.55/4.00      | m1_subset_1(X0,sK9) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_14955,plain,
% 27.55/4.00      ( k4_tarski(k1_mcart_1(sK13),X0) != sK13
% 27.55/4.00      | sK12 = X0
% 27.55/4.00      | sK13 = k1_xboole_0
% 27.55/4.00      | m1_subset_1(X0,sK11) != iProver_top
% 27.55/4.00      | m1_subset_1(sK7(k1_mcart_1(sK13)),sK10) != iProver_top
% 27.55/4.00      | m1_subset_1(sK6(k1_mcart_1(sK13)),sK9) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_14943,c_730]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_17172,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK13),X0) != sK13
% 27.55/4.00      | sK12 = X0
% 27.55/4.00      | sK13 = k1_xboole_0
% 27.55/4.00      | m1_subset_1(X0,sK11) != iProver_top
% 27.55/4.00      | m1_subset_1(sK7(k1_mcart_1(sK13)),sK10) != iProver_top
% 27.55/4.00      | m1_subset_1(sK6(k1_mcart_1(sK13)),sK9) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_5105,c_14955]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_18803,plain,
% 27.55/4.00      ( sK7(sK13) = sK12
% 27.55/4.00      | sK13 = k1_xboole_0
% 27.55/4.00      | m1_subset_1(sK7(k1_mcart_1(sK13)),sK10) != iProver_top
% 27.55/4.00      | m1_subset_1(sK7(sK13),sK11) != iProver_top
% 27.55/4.00      | m1_subset_1(sK6(k1_mcart_1(sK13)),sK9) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_4300,c_17172]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_18807,plain,
% 27.55/4.00      ( sK13 = k1_xboole_0 | v1_xboole_0(sK13) = iProver_top ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_16610,c_5829,c_5831,c_16609,c_16910,c_18803]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_18814,plain,
% 27.55/4.00      ( sK13 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_18807,c_2265]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_72925,plain,
% 27.55/4.00      ( r2_hidden(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(demodulation,[status(thm)],[c_18814,c_2833]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_30,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 27.55/4.00      | k1_xboole_0 = X1
% 27.55/4.00      | k1_xboole_0 = X0
% 27.55/4.00      | k1_xboole_0 = X2
% 27.55/4.00      | k1_xboole_0 = X3 ),
% 27.55/4.00      inference(cnf_transformation,[],[f95]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_835,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK10),X1),X2) != k1_xboole_0
% 27.55/4.00      | k1_xboole_0 = X2
% 27.55/4.00      | k1_xboole_0 = X0
% 27.55/4.00      | k1_xboole_0 = X1
% 27.55/4.00      | k1_xboole_0 = sK10 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_30]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_1190,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK10),X1),sK11) != k1_xboole_0
% 27.55/4.00      | k1_xboole_0 = X0
% 27.55/4.00      | k1_xboole_0 = X1
% 27.55/4.00      | k1_xboole_0 = sK11
% 27.55/4.00      | k1_xboole_0 = sK10 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_835]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_1544,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),X0),sK11) != k1_xboole_0
% 27.55/4.00      | k1_xboole_0 = X0
% 27.55/4.00      | k1_xboole_0 = sK11
% 27.55/4.00      | k1_xboole_0 = sK10
% 27.55/4.00      | k1_xboole_0 = sK9 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_1190]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2289,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) != k1_xboole_0
% 27.55/4.00      | k1_xboole_0 = sK11
% 27.55/4.00      | k1_xboole_0 = sK10
% 27.55/4.00      | k1_xboole_0 = sK9 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_1544]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_5,plain,
% 27.55/4.00      ( r2_hidden(sK2(X0,X1,X2),X0)
% 27.55/4.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 27.55/4.00      | k2_zfmisc_1(X0,X1) = X2 ),
% 27.55/4.00      inference(cnf_transformation,[],[f51]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4496,plain,
% 27.55/4.00      ( r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0)
% 27.55/4.00      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) = k1_xboole_0 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_5]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4497,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11) = k1_xboole_0
% 27.55/4.00      | r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_4496]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7487,plain,
% 27.55/4.00      ( ~ r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0)
% 27.55/4.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7488,plain,
% 27.55/4.00      ( r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k1_xboole_0) != iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_7487]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_24836,plain,
% 27.55/4.00      ( ~ r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11))
% 27.55/4.00      | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_24837,plain,
% 27.55/4.00      ( r2_hidden(sK2(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11),sK11,k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_24836]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_0,plain,
% 27.55/4.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 27.55/4.00      inference(cnf_transformation,[],[f46]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_753,plain,
% 27.55/4.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 27.55/4.00      | v1_xboole_0(X0) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_27,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 27.55/4.00      inference(cnf_transformation,[],[f106]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2521,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | r2_hidden(k2_mcart_1(X0),X1) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_27,c_739]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2533,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | v1_xboole_0(X1) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2521,c_752]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2579,plain,
% 27.55/4.00      ( v1_xboole_0(X0) != iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_753,c_2533]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2974,plain,
% 27.55/4.00      ( r2_hidden(k2_mcart_1(sK13),sK11) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2840,c_2579]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3073,plain,
% 27.55/4.00      ( m1_subset_1(k2_mcart_1(sK13),sK11) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2974,c_728]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_19,plain,
% 27.55/4.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
% 27.55/4.00      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 27.55/4.00      | k1_xboole_0 = X2
% 27.55/4.00      | k1_xboole_0 = X1 ),
% 27.55/4.00      inference(cnf_transformation,[],[f67]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_737,plain,
% 27.55/4.00      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 27.55/4.00      | k1_xboole_0 = X1
% 27.55/4.00      | k1_xboole_0 = X2
% 27.55/4.00      | m1_subset_1(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_5597,plain,
% 27.55/4.00      ( k4_tarski(k1_mcart_1(sK13),k2_mcart_1(sK13)) = sK13
% 27.55/4.00      | k2_zfmisc_1(sK9,sK10) = k1_xboole_0
% 27.55/4.00      | sK11 = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_729,c_737]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_45,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 27.55/4.00      | k1_xboole_0 = k1_xboole_0 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_30]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_29,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 27.55/4.00      inference(cnf_transformation,[],[f108]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_46,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_29]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_327,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_811,plain,
% 27.55/4.00      ( sK11 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK11 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_327]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_812,plain,
% 27.55/4.00      ( sK11 != k1_xboole_0
% 27.55/4.00      | k1_xboole_0 = sK11
% 27.55/4.00      | k1_xboole_0 != k1_xboole_0 ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_811]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_6939,plain,
% 27.55/4.00      ( k2_zfmisc_1(sK9,sK10) = k1_xboole_0
% 27.55/4.00      | k4_tarski(k1_mcart_1(sK13),k2_mcart_1(sK13)) = sK13 ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_5597,c_34,c_45,c_46,c_812]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_6940,plain,
% 27.55/4.00      ( k4_tarski(k1_mcart_1(sK13),k2_mcart_1(sK13)) = sK13
% 27.55/4.00      | k2_zfmisc_1(sK9,sK10) = k1_xboole_0 ),
% 27.55/4.00      inference(renaming,[status(thm)],[c_6939]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_6,plain,
% 27.55/4.00      ( ~ r2_hidden(X0,X1)
% 27.55/4.00      | ~ r2_hidden(X2,X3)
% 27.55/4.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 27.55/4.00      inference(cnf_transformation,[],[f99]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_747,plain,
% 27.55/4.00      ( r2_hidden(X0,X1) != iProver_top
% 27.55/4.00      | r2_hidden(X2,X3) != iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7017,plain,
% 27.55/4.00      ( k2_zfmisc_1(sK9,sK10) = k1_xboole_0
% 27.55/4.00      | r2_hidden(k1_mcart_1(sK13),X0) != iProver_top
% 27.55/4.00      | r2_hidden(k2_mcart_1(sK13),X1) != iProver_top
% 27.55/4.00      | r2_hidden(sK13,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_6940,c_747]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7777,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
% 27.55/4.00      | k2_zfmisc_1(sK9,sK10) = k1_xboole_0
% 27.55/4.00      | r2_hidden(k1_mcart_1(sK13),X0) != iProver_top
% 27.55/4.00      | r2_hidden(k2_mcart_1(sK13),X1) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_7017,c_743]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3021,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2839,c_2579]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_29541,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13 ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_7777,c_36,c_35,c_34,c_2289,c_2839,c_3021,c_4497,
% 27.55/4.00                 c_7488,c_24837]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_29543,plain,
% 27.55/4.00      ( k4_tarski(sK6(k1_xboole_0),sK7(k1_xboole_0)) = k1_xboole_0 ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_29541,c_18814]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_29555,plain,
% 27.55/4.00      ( k2_mcart_1(k1_xboole_0) = sK7(k1_xboole_0) ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_29543,c_31]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_37550,plain,
% 27.55/4.00      ( m1_subset_1(sK7(k1_xboole_0),sK11) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_3073,c_18814,c_29555]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_748,plain,
% 27.55/4.00      ( k2_zfmisc_1(X0,X1) = X2
% 27.55/4.00      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 27.55/4.00      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7019,plain,
% 27.55/4.00      ( r2_hidden(X0,X1) != iProver_top
% 27.55/4.00      | r2_hidden(X2,k2_zfmisc_1(k2_zfmisc_1(X3,X4),k1_xboole_0)) != iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_27,c_747]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7266,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = X3
% 27.55/4.00      | r2_hidden(X4,X5) != iProver_top
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),X3) = iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),X4),k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_748,c_7019]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7286,plain,
% 27.55/4.00      ( k1_xboole_0 = X0
% 27.55/4.00      | r2_hidden(X1,X2) != iProver_top
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X3,X4),k1_xboole_0),X5,X0),X0) = iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X3,X4),k1_xboole_0),X5,X0),X1),k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(demodulation,[status(thm)],[c_7266,c_27]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_10961,plain,
% 27.55/4.00      ( k1_xboole_0 = X0
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),k1_mcart_1(sK13)),k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2841,c_7286]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_29554,plain,
% 27.55/4.00      ( k1_mcart_1(k1_xboole_0) = sK6(k1_xboole_0) ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_29543,c_32]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_41093,plain,
% 27.55/4.00      ( k1_xboole_0 = X0
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK6(k1_xboole_0)),k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_10961,c_18814,c_29554]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_10957,plain,
% 27.55/4.00      ( k1_xboole_0 = X0
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK13),k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2833,c_7286]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_26,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) = k1_xboole_0 ),
% 27.55/4.00      inference(cnf_transformation,[],[f105]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7018,plain,
% 27.55/4.00      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 27.55/4.00      | r2_hidden(X4,k1_xboole_0) != iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(X0,X4),k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_26,c_747]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7197,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(sK13,X0),k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2833,c_7018]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_1527,plain,
% 27.55/4.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_27,c_27]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_1915,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | r2_hidden(k1_mcart_1(X0),k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_1527,c_738]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2064,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_32,c_1915]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7683,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | r2_hidden(sK13,k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_7197,c_2064]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_20157,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_7683,c_18814]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_20180,plain,
% 27.55/4.00      ( k1_xboole_0 = X0
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
% 27.55/4.00      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_10957,c_20157]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_74,plain,
% 27.55/4.00      ( m1_subset_1(X0,X1) != iProver_top
% 27.55/4.00      | r2_hidden(X0,X1) = iProver_top
% 27.55/4.00      | v1_xboole_0(X1) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_76,plain,
% 27.55/4.00      ( m1_subset_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 27.55/4.00      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_74]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2066,plain,
% 27.55/4.00      ( m1_subset_1(k1_mcart_1(X0),k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_1915,c_728]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2446,plain,
% 27.55/4.00      ( m1_subset_1(X0,k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_32,c_2066]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7682,plain,
% 27.55/4.00      ( m1_subset_1(sK13,k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_7197,c_2446]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_19762,plain,
% 27.55/4.00      ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_7682,c_18814]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_11,plain,
% 27.55/4.00      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 27.55/4.00      inference(cnf_transformation,[],[f59]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_81,plain,
% 27.55/4.00      ( m1_subset_1(X0,X1) = iProver_top
% 27.55/4.00      | v1_xboole_0(X1) != iProver_top
% 27.55/4.00      | v1_xboole_0(X0) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_83,plain,
% 27.55/4.00      ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(instantiation,[status(thm)],[c_81]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7675,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(sK13,X0),k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_7197,c_2579]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_19156,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_7675,c_18814]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_19171,plain,
% 27.55/4.00      ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_19156,c_2446]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_19764,plain,
% 27.55/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.55/4.00      | m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_19762,c_83,c_19171]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_19765,plain,
% 27.55/4.00      ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(renaming,[status(thm)],[c_19764]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_19768,plain,
% 27.55/4.00      ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_753,c_19765]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_21358,plain,
% 27.55/4.00      ( m1_subset_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_19768,c_83]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_30666,plain,
% 27.55/4.00      ( r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
% 27.55/4.00      | k1_xboole_0 = X0 ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_20180,c_36,c_35,c_34,c_76,c_83,c_2289,c_4497,c_7488,
% 27.55/4.00                 c_19768,c_24837]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_30667,plain,
% 27.55/4.00      ( k1_xboole_0 = X0
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
% 27.55/4.00      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(renaming,[status(thm)],[c_30666]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_29551,plain,
% 27.55/4.00      ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_29543,c_2064]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_36970,plain,
% 27.55/4.00      ( k1_xboole_0 = X0
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK6(k1_xboole_0)),k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_29551,c_7286]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_41095,plain,
% 27.55/4.00      ( r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK6(k1_xboole_0)),k1_xboole_0) = iProver_top
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
% 27.55/4.00      | k1_xboole_0 = X0 ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_41093,c_30667,c_36970]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_41096,plain,
% 27.55/4.00      ( k1_xboole_0 = X0
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top
% 27.55/4.00      | r2_hidden(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),sK6(k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(renaming,[status(thm)],[c_41095]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2773,plain,
% 27.55/4.00      ( k4_tarski(sK6(k2_mcart_1(X0)),sK7(k2_mcart_1(X0))) = k2_mcart_1(X0)
% 27.55/4.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2521,c_743]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_41127,plain,
% 27.55/4.00      ( k4_tarski(sK6(k2_mcart_1(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),sK6(k1_xboole_0)))),sK7(k2_mcart_1(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),sK6(k1_xboole_0))))) = k2_mcart_1(k4_tarski(sK2(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),sK6(k1_xboole_0)))
% 27.55/4.00      | k1_xboole_0 = X3
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2,X3),X3) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_41096,c_2773]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_41180,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK6(k1_xboole_0)),sK7(sK6(k1_xboole_0))) = sK6(k1_xboole_0)
% 27.55/4.00      | k1_xboole_0 = X0
% 27.55/4.00      | r2_hidden(sK1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3,X0),X0) = iProver_top ),
% 27.55/4.00      inference(demodulation,[status(thm)],[c_41127,c_31]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_2775,plain,
% 27.55/4.00      ( k4_tarski(sK6(X0),sK7(X0)) = X0
% 27.55/4.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_26,c_743]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_36981,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK6(k1_xboole_0)),sK7(sK6(k1_xboole_0))) = sK6(k1_xboole_0)
% 27.55/4.00      | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_29551,c_2775]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_9,plain,
% 27.55/4.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 27.55/4.00      | r2_hidden(sK4(X1,X2,X0),X1) ),
% 27.55/4.00      inference(cnf_transformation,[],[f102]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_744,plain,
% 27.55/4.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.55/4.00      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3546,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK4(k2_zfmisc_1(X0,X1),X2,X3)),sK7(sK4(k2_zfmisc_1(X0,X1),X2,X3))) = sK4(k2_zfmisc_1(X0,X1),X2,X3)
% 27.55/4.00      | r2_hidden(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_744,c_743]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_41629,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13)),sK7(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13))) = sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13)
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2833,c_3546]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3022,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK13),sK7(sK13)) = sK13
% 27.55/4.00      | k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0 ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2839,c_2265]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_5276,plain,
% 27.55/4.00      ( k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11) = k1_xboole_0
% 27.55/4.00      | k1_mcart_1(sK13) = sK6(sK13) ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_3022,c_32]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_7,plain,
% 27.55/4.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 27.55/4.00      | k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
% 27.55/4.00      inference(cnf_transformation,[],[f100]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_746,plain,
% 27.55/4.00      ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
% 27.55/4.00      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4928,plain,
% 27.55/4.00      ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_2833,c_746]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_6040,plain,
% 27.55/4.00      ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 27.55/4.00      | k1_mcart_1(sK13) = sK6(sK13)
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_5276,c_4928]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_4960,plain,
% 27.55/4.00      ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_4928,c_2579]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_26083,plain,
% 27.55/4.00      ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,sK13),sK5(k2_zfmisc_1(sK9,sK10),sK11,sK13)) = sK13 ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_6040,c_36,c_35,c_34,c_2289,c_4497,c_4928,c_4960,
% 27.55/4.00                 c_7488,c_24837]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_26085,plain,
% 27.55/4.00      ( k4_tarski(sK4(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0),sK5(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0)) = k1_xboole_0 ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_26083,c_18814]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_26095,plain,
% 27.55/4.00      ( sK4(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0) = k1_mcart_1(k1_xboole_0) ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_26085,c_32]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_29603,plain,
% 27.55/4.00      ( sK4(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0) = sK6(k1_xboole_0) ),
% 27.55/4.00      inference(demodulation,[status(thm)],[c_29554,c_26095]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_41691,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK6(k1_xboole_0)),sK7(sK6(k1_xboole_0))) = sK6(k1_xboole_0)
% 27.55/4.00      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_41629,c_18814,c_29603]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_42071,plain,
% 27.55/4.00      ( k4_tarski(sK6(sK6(k1_xboole_0)),sK7(sK6(k1_xboole_0))) = sK6(k1_xboole_0) ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_41180,c_36,c_35,c_34,c_76,c_83,c_2289,c_4497,c_7488,
% 27.55/4.00                 c_19768,c_24837,c_36981,c_41691]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_42085,plain,
% 27.55/4.00      ( k4_tarski(sK6(k1_xboole_0),X0) != sK13
% 27.55/4.00      | sK12 = X0
% 27.55/4.00      | m1_subset_1(X0,sK11) != iProver_top
% 27.55/4.00      | m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) != iProver_top
% 27.55/4.00      | m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_42071,c_730]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_42087,plain,
% 27.55/4.00      ( k4_tarski(sK6(k1_xboole_0),X0) != k1_xboole_0
% 27.55/4.00      | sK12 = X0
% 27.55/4.00      | m1_subset_1(X0,sK11) != iProver_top
% 27.55/4.00      | m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) != iProver_top
% 27.55/4.00      | m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) != iProver_top ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_42085,c_18814]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_42364,plain,
% 27.55/4.00      ( sK7(k1_xboole_0) = sK12
% 27.55/4.00      | m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) != iProver_top
% 27.55/4.00      | m1_subset_1(sK7(k1_xboole_0),sK11) != iProver_top
% 27.55/4.00      | m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_29543,c_42087]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_72916,plain,
% 27.55/4.00      ( k2_mcart_1(k1_xboole_0) != sK12 ),
% 27.55/4.00      inference(demodulation,[status(thm)],[c_18814,c_4009]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_72935,plain,
% 27.55/4.00      ( sK7(k1_xboole_0) != sK12 ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_72916,c_29555]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_72884,plain,
% 27.55/4.00      ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_xboole_0)),sK10) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(demodulation,[status(thm)],[c_18814,c_5379]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_42084,plain,
% 27.55/4.00      ( k2_mcart_1(sK6(k1_xboole_0)) = sK7(sK6(k1_xboole_0)) ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_42071,c_31]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_72945,plain,
% 27.55/4.00      ( m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_72884,c_29554,c_42084]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_72871,plain,
% 27.55/4.00      ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_xboole_0)),sK9) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(demodulation,[status(thm)],[c_18814,c_7900]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_42083,plain,
% 27.55/4.00      ( k1_mcart_1(sK6(k1_xboole_0)) = sK6(sK6(k1_xboole_0)) ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_42071,c_32]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_72952,plain,
% 27.55/4.00      ( m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) = iProver_top
% 27.55/4.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_72871,c_29554,c_42083]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_73593,plain,
% 27.55/4.00      ( r2_hidden(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) = iProver_top ),
% 27.55/4.00      inference(global_propositional_subsumption,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_72925,c_36,c_35,c_34,c_2289,c_4497,c_7488,c_24837,
% 27.55/4.00                 c_37550,c_42364,c_72935,c_72945,c_72952]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_73612,plain,
% 27.55/4.00      ( r2_hidden(k1_mcart_1(k1_xboole_0),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_73593,c_738]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_73619,plain,
% 27.55/4.00      ( r2_hidden(sK6(k1_xboole_0),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_73612,c_29554]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_75189,plain,
% 27.55/4.00      ( r2_hidden(k2_mcart_1(sK6(k1_xboole_0)),sK10) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_73619,c_739]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_75193,plain,
% 27.55/4.00      ( r2_hidden(sK7(sK6(k1_xboole_0)),sK10) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_75189,c_42084]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_75328,plain,
% 27.55/4.00      ( m1_subset_1(sK7(sK6(k1_xboole_0)),sK10) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_75193,c_728]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_75190,plain,
% 27.55/4.00      ( r2_hidden(k1_mcart_1(sK6(k1_xboole_0)),sK9) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_73619,c_738]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_75192,plain,
% 27.55/4.00      ( r2_hidden(sK6(sK6(k1_xboole_0)),sK9) = iProver_top ),
% 27.55/4.00      inference(light_normalisation,[status(thm)],[c_75190,c_42083]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_75324,plain,
% 27.55/4.00      ( m1_subset_1(sK6(sK6(k1_xboole_0)),sK9) = iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_75192,c_728]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_26096,plain,
% 27.55/4.00      ( sK5(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0) = k2_mcart_1(k1_xboole_0) ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_26085,c_31]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_29807,plain,
% 27.55/4.00      ( sK5(k2_zfmisc_1(sK9,sK10),sK11,k1_xboole_0) = sK7(k1_xboole_0) ),
% 27.55/4.00      inference(demodulation,[status(thm)],[c_29555,c_26096]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_8,plain,
% 27.55/4.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 27.55/4.00      | r2_hidden(sK5(X1,X2,X0),X2) ),
% 27.55/4.00      inference(cnf_transformation,[],[f101]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_745,plain,
% 27.55/4.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.55/4.00      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 27.55/4.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_3573,plain,
% 27.55/4.00      ( m1_subset_1(sK5(X0,X1,X2),X1) = iProver_top
% 27.55/4.00      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_745,c_728]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(c_47996,plain,
% 27.55/4.00      ( m1_subset_1(sK7(k1_xboole_0),sK11) = iProver_top
% 27.55/4.00      | r2_hidden(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK9,sK10),sK11)) != iProver_top ),
% 27.55/4.00      inference(superposition,[status(thm)],[c_29807,c_3573]) ).
% 27.55/4.00  
% 27.55/4.00  cnf(contradiction,plain,
% 27.55/4.00      ( $false ),
% 27.55/4.00      inference(minisat,
% 27.55/4.00                [status(thm)],
% 27.55/4.00                [c_75328,c_75324,c_73593,c_72935,c_47996,c_42364]) ).
% 27.55/4.00  
% 27.55/4.00  
% 27.55/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.55/4.00  
% 27.55/4.00  ------                               Statistics
% 27.55/4.00  
% 27.55/4.00  ------ General
% 27.55/4.00  
% 27.55/4.00  abstr_ref_over_cycles:                  0
% 27.55/4.00  abstr_ref_under_cycles:                 0
% 27.55/4.00  gc_basic_clause_elim:                   0
% 27.55/4.00  forced_gc_time:                         0
% 27.55/4.00  parsing_time:                           0.011
% 27.55/4.00  unif_index_cands_time:                  0.
% 27.55/4.00  unif_index_add_time:                    0.
% 27.55/4.00  orderings_time:                         0.
% 27.55/4.00  out_proof_time:                         0.029
% 27.55/4.00  total_time:                             3.053
% 27.55/4.00  num_of_symbols:                         57
% 27.55/4.00  num_of_terms:                           132954
% 27.55/4.00  
% 27.55/4.00  ------ Preprocessing
% 27.55/4.00  
% 27.55/4.00  num_of_splits:                          0
% 27.55/4.00  num_of_split_atoms:                     0
% 27.55/4.00  num_of_reused_defs:                     0
% 27.55/4.00  num_eq_ax_congr_red:                    64
% 27.55/4.00  num_of_sem_filtered_clauses:            1
% 27.55/4.00  num_of_subtypes:                        0
% 27.55/4.00  monotx_restored_types:                  0
% 27.55/4.00  sat_num_of_epr_types:                   0
% 27.55/4.00  sat_num_of_non_cyclic_types:            0
% 27.55/4.00  sat_guarded_non_collapsed_types:        0
% 27.55/4.00  num_pure_diseq_elim:                    0
% 27.55/4.00  simp_replaced_by:                       0
% 27.55/4.00  res_preprocessed:                       136
% 27.55/4.00  prep_upred:                             0
% 27.55/4.00  prep_unflattend:                        0
% 27.55/4.00  smt_new_axioms:                         0
% 27.55/4.00  pred_elim_cands:                        3
% 27.55/4.00  pred_elim:                              0
% 27.55/4.00  pred_elim_cl:                           0
% 27.55/4.00  pred_elim_cycles:                       1
% 27.55/4.00  merged_defs:                            0
% 27.55/4.00  merged_defs_ncl:                        0
% 27.55/4.00  bin_hyper_res:                          0
% 27.55/4.00  prep_cycles:                            3
% 27.55/4.00  pred_elim_time:                         0.001
% 27.55/4.00  splitting_time:                         0.
% 27.55/4.00  sem_filter_time:                        0.
% 27.55/4.00  monotx_time:                            0.001
% 27.55/4.00  subtype_inf_time:                       0.
% 27.55/4.00  
% 27.55/4.00  ------ Problem properties
% 27.55/4.00  
% 27.55/4.00  clauses:                                39
% 27.55/4.00  conjectures:                            6
% 27.55/4.00  epr:                                    8
% 27.55/4.00  horn:                                   28
% 27.55/4.00  ground:                                 5
% 27.55/4.00  unary:                                  13
% 27.55/4.00  binary:                                 10
% 27.55/4.00  lits:                                   94
% 27.55/4.00  lits_eq:                                47
% 27.55/4.00  fd_pure:                                0
% 27.55/4.00  fd_pseudo:                              0
% 27.55/4.00  fd_cond:                                8
% 27.55/4.00  fd_pseudo_cond:                         4
% 27.55/4.00  ac_symbols:                             0
% 27.55/4.00  
% 27.55/4.00  ------ Propositional Solver
% 27.55/4.00  
% 27.55/4.00  prop_solver_calls:                      44
% 27.55/4.00  prop_fast_solver_calls:                 3654
% 27.55/4.00  smt_solver_calls:                       0
% 27.55/4.00  smt_fast_solver_calls:                  0
% 27.55/4.00  prop_num_of_clauses:                    43122
% 27.55/4.00  prop_preprocess_simplified:             81111
% 27.55/4.00  prop_fo_subsumed:                       268
% 27.55/4.00  prop_solver_time:                       0.
% 27.55/4.00  smt_solver_time:                        0.
% 27.55/4.00  smt_fast_solver_time:                   0.
% 27.55/4.00  prop_fast_solver_time:                  0.
% 27.55/4.00  prop_unsat_core_time:                   0.004
% 27.55/4.00  
% 27.55/4.00  ------ QBF
% 27.55/4.00  
% 27.55/4.00  qbf_q_res:                              0
% 27.55/4.00  qbf_num_tautologies:                    0
% 27.55/4.00  qbf_prep_cycles:                        0
% 27.55/4.00  
% 27.55/4.00  ------ BMC1
% 27.55/4.00  
% 27.55/4.00  bmc1_current_bound:                     -1
% 27.55/4.00  bmc1_last_solved_bound:                 -1
% 27.55/4.00  bmc1_unsat_core_size:                   -1
% 27.55/4.00  bmc1_unsat_core_parents_size:           -1
% 27.55/4.00  bmc1_merge_next_fun:                    0
% 27.55/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.55/4.00  
% 27.55/4.00  ------ Instantiation
% 27.55/4.00  
% 27.55/4.00  inst_num_of_clauses:                    9805
% 27.55/4.00  inst_num_in_passive:                    7926
% 27.55/4.00  inst_num_in_active:                     1658
% 27.55/4.00  inst_num_in_unprocessed:                221
% 27.55/4.00  inst_num_of_loops:                      2280
% 27.55/4.00  inst_num_of_learning_restarts:          0
% 27.55/4.00  inst_num_moves_active_passive:          622
% 27.55/4.00  inst_lit_activity:                      0
% 27.55/4.00  inst_lit_activity_moves:                3
% 27.55/4.00  inst_num_tautologies:                   0
% 27.55/4.00  inst_num_prop_implied:                  0
% 27.55/4.00  inst_num_existing_simplified:           0
% 27.55/4.00  inst_num_eq_res_simplified:             0
% 27.55/4.00  inst_num_child_elim:                    0
% 27.55/4.00  inst_num_of_dismatching_blockings:      295
% 27.55/4.00  inst_num_of_non_proper_insts:           3786
% 27.55/4.00  inst_num_of_duplicates:                 0
% 27.55/4.00  inst_inst_num_from_inst_to_res:         0
% 27.55/4.00  inst_dismatching_checking_time:         0.
% 27.55/4.00  
% 27.55/4.00  ------ Resolution
% 27.55/4.00  
% 27.55/4.00  res_num_of_clauses:                     0
% 27.55/4.00  res_num_in_passive:                     0
% 27.55/4.00  res_num_in_active:                      0
% 27.55/4.00  res_num_of_loops:                       139
% 27.55/4.00  res_forward_subset_subsumed:            12
% 27.55/4.00  res_backward_subset_subsumed:           0
% 27.55/4.00  res_forward_subsumed:                   0
% 27.55/4.00  res_backward_subsumed:                  0
% 27.55/4.00  res_forward_subsumption_resolution:     0
% 27.55/4.00  res_backward_subsumption_resolution:    0
% 27.55/4.00  res_clause_to_clause_subsumption:       34289
% 27.55/4.00  res_orphan_elimination:                 0
% 27.55/4.00  res_tautology_del:                      6
% 27.55/4.00  res_num_eq_res_simplified:              0
% 27.55/4.00  res_num_sel_changes:                    0
% 27.55/4.00  res_moves_from_active_to_pass:          0
% 27.55/4.00  
% 27.55/4.00  ------ Superposition
% 27.55/4.00  
% 27.55/4.00  sup_time_total:                         0.
% 27.55/4.00  sup_time_generating:                    0.
% 27.55/4.00  sup_time_sim_full:                      0.
% 27.55/4.00  sup_time_sim_immed:                     0.
% 27.55/4.00  
% 27.55/4.00  sup_num_of_clauses:                     5331
% 27.55/4.00  sup_num_in_active:                      102
% 27.55/4.00  sup_num_in_passive:                     5229
% 27.55/4.00  sup_num_of_loops:                       455
% 27.55/4.00  sup_fw_superposition:                   6244
% 27.55/4.00  sup_bw_superposition:                   10543
% 27.55/4.00  sup_immediate_simplified:               5481
% 27.55/4.00  sup_given_eliminated:                   31
% 27.55/4.00  comparisons_done:                       0
% 27.55/4.00  comparisons_avoided:                    302
% 27.55/4.00  
% 27.55/4.00  ------ Simplifications
% 27.55/4.00  
% 27.55/4.00  
% 27.55/4.00  sim_fw_subset_subsumed:                 1786
% 27.55/4.00  sim_bw_subset_subsumed:                 596
% 27.55/4.00  sim_fw_subsumed:                        1476
% 27.55/4.00  sim_bw_subsumed:                        299
% 27.55/4.00  sim_fw_subsumption_res:                 0
% 27.55/4.00  sim_bw_subsumption_res:                 0
% 27.55/4.00  sim_tautology_del:                      60
% 27.55/4.00  sim_eq_tautology_del:                   2860
% 27.55/4.00  sim_eq_res_simp:                        36
% 27.55/4.00  sim_fw_demodulated:                     1415
% 27.55/4.00  sim_bw_demodulated:                     187
% 27.55/4.00  sim_light_normalised:                   1409
% 27.55/4.00  sim_joinable_taut:                      0
% 27.55/4.00  sim_joinable_simp:                      0
% 27.55/4.00  sim_ac_normalised:                      0
% 27.55/4.00  sim_smt_subsumption:                    0
% 27.55/4.00  
%------------------------------------------------------------------------------
