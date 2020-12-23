%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:19 EST 2020

% Result     : Theorem 51.28s
% Output     : CNFRefutation 51.28s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 309 expanded)
%              Number of clauses        :   62 ( 101 expanded)
%              Number of leaves         :   28 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  338 ( 804 expanded)
%              Number of equality atoms :  162 ( 315 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK3(X0,X1,X2),X2)
            & r2_hidden(sK3(X0,X1,X2),X1)
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f36])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4))
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f38])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK2(X0,X5),X0)
        & r2_hidden(X5,sK2(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(X2,sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK0(X0,X1),X3) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK0(X0,X1),X4) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK0(X0,X1),X3) )
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( ( r2_hidden(sK1(X0,X1),X0)
              & r2_hidden(sK0(X0,X1),sK1(X0,X1)) )
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK2(X0,X5),X0)
                & r2_hidden(X5,sK2(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f52])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f74])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f77,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f41,f76])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f75,f75])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f76])).

fof(f70,plain,(
    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_625,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_623,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_630,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1660,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_630])).

cnf(c_24,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_37,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_39,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_702,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | r2_hidden(sK5,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_703,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top
    | r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_3268,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1660,c_24,c_39,c_703])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_636,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3272,plain,
    ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(sK4))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3268,c_636])).

cnf(c_4426,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_3272])).

cnf(c_4659,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,sK5,X0),sK4) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_4426])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK3(X1,X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_626,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X0) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_28873,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4659,c_626])).

cnf(c_15,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_16,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_629,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1004,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_629])).

cnf(c_1006,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_28886,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(sK5,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_28873])).

cnf(c_153401,plain,
    ( r1_tarski(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28873,c_24,c_1006,c_28886])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_640,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_153405,plain,
    ( k3_xboole_0(sK5,sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_153401,c_640])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_820,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_153577,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
    inference(superposition,[status(thm)],[c_153405,c_820])).

cnf(c_3,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_627,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1732,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_627])).

cnf(c_8319,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4)) = k4_subset_1(sK4,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_623,c_1732])).

cnf(c_9545,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_3,c_8319])).

cnf(c_154322,plain,
    ( k4_subset_1(sK4,sK5,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_153577,c_9545])).

cnf(c_287,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4033,plain,
    ( X0 != X1
    | X0 = k4_subset_1(X2,sK5,X3)
    | k4_subset_1(X2,sK5,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_4034,plain,
    ( k4_subset_1(sK4,sK5,sK4) != sK4
    | sK4 = k4_subset_1(sK4,sK5,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4033])).

cnf(c_796,plain,
    ( X0 != X1
    | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != X1
    | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_2133,plain,
    ( X0 != k4_subset_1(X1,sK5,X2)
    | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = X0
    | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != k4_subset_1(X1,sK5,X2) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_2134,plain,
    ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != k4_subset_1(sK4,sK5,sK4)
    | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = sK4
    | sK4 != k4_subset_1(sK4,sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_295,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_798,plain,
    ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = k4_subset_1(X0,X1,X2)
    | k2_subset_1(sK4) != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_1165,plain,
    ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = k4_subset_1(X0,sK5,X1)
    | k2_subset_1(sK4) != X1
    | sK5 != sK5
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_1166,plain,
    ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = k4_subset_1(sK4,sK5,sK4)
    | k2_subset_1(sK4) != sK4
    | sK5 != sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_286,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_879,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_705,plain,
    ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != X0
    | k2_subset_1(sK4) != X0
    | k2_subset_1(sK4) = k4_subset_1(sK4,sK5,k2_subset_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_706,plain,
    ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != sK4
    | k2_subset_1(sK4) = k4_subset_1(sK4,sK5,k2_subset_1(sK4))
    | k2_subset_1(sK4) != sK4 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_304,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_43,plain,
    ( k2_subset_1(sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_22,negated_conjecture,
    ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_154322,c_4034,c_2134,c_1166,c_879,c_706,c_304,c_43,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 51.28/7.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.28/7.00  
% 51.28/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.28/7.00  
% 51.28/7.00  ------  iProver source info
% 51.28/7.00  
% 51.28/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.28/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.28/7.00  git: non_committed_changes: false
% 51.28/7.00  git: last_make_outside_of_git: false
% 51.28/7.00  
% 51.28/7.00  ------ 
% 51.28/7.00  ------ Parsing...
% 51.28/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.28/7.00  
% 51.28/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.28/7.00  
% 51.28/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.28/7.00  
% 51.28/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.28/7.00  ------ Proving...
% 51.28/7.00  ------ Problem Properties 
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  clauses                                 24
% 51.28/7.00  conjectures                             2
% 51.28/7.00  EPR                                     4
% 51.28/7.00  Horn                                    18
% 51.28/7.00  unary                                   9
% 51.28/7.00  binary                                  3
% 51.28/7.00  lits                                    55
% 51.28/7.00  lits eq                                 11
% 51.28/7.00  fd_pure                                 0
% 51.28/7.00  fd_pseudo                               0
% 51.28/7.00  fd_cond                                 0
% 51.28/7.00  fd_pseudo_cond                          3
% 51.28/7.00  AC symbols                              0
% 51.28/7.00  
% 51.28/7.00  ------ Input Options Time Limit: Unbounded
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  ------ 
% 51.28/7.00  Current options:
% 51.28/7.00  ------ 
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  ------ Proving...
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  % SZS status Theorem for theBenchmark.p
% 51.28/7.00  
% 51.28/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.28/7.00  
% 51.28/7.00  fof(f19,axiom,(
% 51.28/7.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f26,plain,(
% 51.28/7.00    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f19])).
% 51.28/7.00  
% 51.28/7.00  fof(f27,plain,(
% 51.28/7.00    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.28/7.00    inference(flattening,[],[f26])).
% 51.28/7.00  
% 51.28/7.00  fof(f36,plain,(
% 51.28/7.00    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f37,plain,(
% 51.28/7.00    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.28/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f36])).
% 51.28/7.00  
% 51.28/7.00  fof(f67,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.28/7.00    inference(cnf_transformation,[],[f37])).
% 51.28/7.00  
% 51.28/7.00  fof(f13,axiom,(
% 51.28/7.00    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f57,plain,(
% 51.28/7.00    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 51.28/7.00    inference(cnf_transformation,[],[f13])).
% 51.28/7.00  
% 51.28/7.00  fof(f20,conjecture,(
% 51.28/7.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f21,negated_conjecture,(
% 51.28/7.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 51.28/7.00    inference(negated_conjecture,[],[f20])).
% 51.28/7.00  
% 51.28/7.00  fof(f28,plain,(
% 51.28/7.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f21])).
% 51.28/7.00  
% 51.28/7.00  fof(f38,plain,(
% 51.28/7.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f39,plain,(
% 51.28/7.00    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 51.28/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f38])).
% 51.28/7.00  
% 51.28/7.00  fof(f69,plain,(
% 51.28/7.00    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 51.28/7.00    inference(cnf_transformation,[],[f39])).
% 51.28/7.00  
% 51.28/7.00  fof(f14,axiom,(
% 51.28/7.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f23,plain,(
% 51.28/7.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f14])).
% 51.28/7.00  
% 51.28/7.00  fof(f35,plain,(
% 51.28/7.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 51.28/7.00    inference(nnf_transformation,[],[f23])).
% 51.28/7.00  
% 51.28/7.00  fof(f58,plain,(
% 51.28/7.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f35])).
% 51.28/7.00  
% 51.28/7.00  fof(f17,axiom,(
% 51.28/7.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f64,plain,(
% 51.28/7.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 51.28/7.00    inference(cnf_transformation,[],[f17])).
% 51.28/7.00  
% 51.28/7.00  fof(f11,axiom,(
% 51.28/7.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f29,plain,(
% 51.28/7.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 51.28/7.00    inference(nnf_transformation,[],[f11])).
% 51.28/7.00  
% 51.28/7.00  fof(f30,plain,(
% 51.28/7.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 51.28/7.00    inference(rectify,[],[f29])).
% 51.28/7.00  
% 51.28/7.00  fof(f33,plain,(
% 51.28/7.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK2(X0,X5),X0) & r2_hidden(X5,sK2(X0,X5))))),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f32,plain,(
% 51.28/7.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK1(X0,X1),X0) & r2_hidden(X2,sK1(X0,X1))))) )),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f31,plain,(
% 51.28/7.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK0(X0,X1),X3)) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK0(X0,X1),X4)) | r2_hidden(sK0(X0,X1),X1))))),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f34,plain,(
% 51.28/7.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK0(X0,X1),X3)) | ~r2_hidden(sK0(X0,X1),X1)) & ((r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),sK1(X0,X1))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK2(X0,X5),X0) & r2_hidden(X5,sK2(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 51.28/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).
% 51.28/7.00  
% 51.28/7.00  fof(f52,plain,(
% 51.28/7.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 51.28/7.00    inference(cnf_transformation,[],[f34])).
% 51.28/7.00  
% 51.28/7.00  fof(f80,plain,(
% 51.28/7.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 51.28/7.00    inference(equality_resolution,[],[f52])).
% 51.28/7.00  
% 51.28/7.00  fof(f68,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.28/7.00    inference(cnf_transformation,[],[f37])).
% 51.28/7.00  
% 51.28/7.00  fof(f15,axiom,(
% 51.28/7.00    ! [X0] : k2_subset_1(X0) = X0),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f62,plain,(
% 51.28/7.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 51.28/7.00    inference(cnf_transformation,[],[f15])).
% 51.28/7.00  
% 51.28/7.00  fof(f16,axiom,(
% 51.28/7.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f63,plain,(
% 51.28/7.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 51.28/7.00    inference(cnf_transformation,[],[f16])).
% 51.28/7.00  
% 51.28/7.00  fof(f3,axiom,(
% 51.28/7.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f22,plain,(
% 51.28/7.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.28/7.00    inference(ennf_transformation,[],[f3])).
% 51.28/7.00  
% 51.28/7.00  fof(f42,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f22])).
% 51.28/7.00  
% 51.28/7.00  fof(f1,axiom,(
% 51.28/7.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f40,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f1])).
% 51.28/7.00  
% 51.28/7.00  fof(f2,axiom,(
% 51.28/7.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f41,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 51.28/7.00    inference(cnf_transformation,[],[f2])).
% 51.28/7.00  
% 51.28/7.00  fof(f12,axiom,(
% 51.28/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f56,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 51.28/7.00    inference(cnf_transformation,[],[f12])).
% 51.28/7.00  
% 51.28/7.00  fof(f5,axiom,(
% 51.28/7.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f44,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f5])).
% 51.28/7.00  
% 51.28/7.00  fof(f6,axiom,(
% 51.28/7.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f45,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f6])).
% 51.28/7.00  
% 51.28/7.00  fof(f7,axiom,(
% 51.28/7.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f46,plain,(
% 51.28/7.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f7])).
% 51.28/7.00  
% 51.28/7.00  fof(f8,axiom,(
% 51.28/7.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f47,plain,(
% 51.28/7.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f8])).
% 51.28/7.00  
% 51.28/7.00  fof(f9,axiom,(
% 51.28/7.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f48,plain,(
% 51.28/7.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f9])).
% 51.28/7.00  
% 51.28/7.00  fof(f10,axiom,(
% 51.28/7.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f49,plain,(
% 51.28/7.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f10])).
% 51.28/7.00  
% 51.28/7.00  fof(f71,plain,(
% 51.28/7.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 51.28/7.00    inference(definition_unfolding,[],[f48,f49])).
% 51.28/7.00  
% 51.28/7.00  fof(f72,plain,(
% 51.28/7.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 51.28/7.00    inference(definition_unfolding,[],[f47,f71])).
% 51.28/7.00  
% 51.28/7.00  fof(f73,plain,(
% 51.28/7.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 51.28/7.00    inference(definition_unfolding,[],[f46,f72])).
% 51.28/7.00  
% 51.28/7.00  fof(f74,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 51.28/7.00    inference(definition_unfolding,[],[f45,f73])).
% 51.28/7.00  
% 51.28/7.00  fof(f75,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 51.28/7.00    inference(definition_unfolding,[],[f44,f74])).
% 51.28/7.00  
% 51.28/7.00  fof(f76,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 51.28/7.00    inference(definition_unfolding,[],[f56,f75])).
% 51.28/7.00  
% 51.28/7.00  fof(f77,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 51.28/7.00    inference(definition_unfolding,[],[f41,f76])).
% 51.28/7.00  
% 51.28/7.00  fof(f4,axiom,(
% 51.28/7.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f43,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f4])).
% 51.28/7.00  
% 51.28/7.00  fof(f78,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 51.28/7.00    inference(definition_unfolding,[],[f43,f75,f75])).
% 51.28/7.00  
% 51.28/7.00  fof(f18,axiom,(
% 51.28/7.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f24,plain,(
% 51.28/7.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 51.28/7.00    inference(ennf_transformation,[],[f18])).
% 51.28/7.00  
% 51.28/7.00  fof(f25,plain,(
% 51.28/7.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.28/7.00    inference(flattening,[],[f24])).
% 51.28/7.00  
% 51.28/7.00  fof(f65,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.28/7.00    inference(cnf_transformation,[],[f25])).
% 51.28/7.00  
% 51.28/7.00  fof(f79,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.28/7.00    inference(definition_unfolding,[],[f65,f76])).
% 51.28/7.00  
% 51.28/7.00  fof(f70,plain,(
% 51.28/7.00    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4))),
% 51.28/7.00    inference(cnf_transformation,[],[f39])).
% 51.28/7.00  
% 51.28/7.00  cnf(c_20,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.28/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 51.28/7.00      | r2_hidden(sK3(X1,X2,X0),X2)
% 51.28/7.00      | r1_tarski(X2,X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f67]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_625,plain,
% 51.28/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.28/7.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 51.28/7.00      | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
% 51.28/7.00      | r1_tarski(X2,X0) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_10,plain,
% 51.28/7.00      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 51.28/7.00      inference(cnf_transformation,[],[f57]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_23,negated_conjecture,
% 51.28/7.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 51.28/7.00      inference(cnf_transformation,[],[f69]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_623,plain,
% 51.28/7.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_14,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f58]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_630,plain,
% 51.28/7.00      ( m1_subset_1(X0,X1) != iProver_top
% 51.28/7.00      | r2_hidden(X0,X1) = iProver_top
% 51.28/7.00      | v1_xboole_0(X1) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1660,plain,
% 51.28/7.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 51.28/7.00      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_623,c_630]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_24,plain,
% 51.28/7.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_17,plain,
% 51.28/7.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 51.28/7.00      inference(cnf_transformation,[],[f64]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_37,plain,
% 51.28/7.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_39,plain,
% 51.28/7.00      ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_37]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_702,plain,
% 51.28/7.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
% 51.28/7.00      | r2_hidden(sK5,k1_zfmisc_1(sK4))
% 51.28/7.00      | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_14]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_703,plain,
% 51.28/7.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top
% 51.28/7.00      | r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 51.28/7.00      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3268,plain,
% 51.28/7.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1660,c_24,c_39,c_703]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7,plain,
% 51.28/7.00      ( ~ r2_hidden(X0,X1)
% 51.28/7.00      | ~ r2_hidden(X2,X0)
% 51.28/7.00      | r2_hidden(X2,k3_tarski(X1)) ),
% 51.28/7.00      inference(cnf_transformation,[],[f80]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_636,plain,
% 51.28/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.28/7.00      | r2_hidden(X2,X0) != iProver_top
% 51.28/7.00      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3272,plain,
% 51.28/7.00      ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(sK4))) = iProver_top
% 51.28/7.00      | r2_hidden(X0,sK5) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_3268,c_636]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4426,plain,
% 51.28/7.00      ( r2_hidden(X0,sK5) != iProver_top
% 51.28/7.00      | r2_hidden(X0,sK4) = iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_10,c_3272]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4659,plain,
% 51.28/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.28/7.00      | m1_subset_1(sK5,k1_zfmisc_1(X1)) != iProver_top
% 51.28/7.00      | r2_hidden(sK3(X1,sK5,X0),sK4) = iProver_top
% 51.28/7.00      | r1_tarski(sK5,X0) = iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_625,c_4426]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_19,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.28/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 51.28/7.00      | ~ r2_hidden(sK3(X1,X2,X0),X0)
% 51.28/7.00      | r1_tarski(X2,X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f68]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_626,plain,
% 51.28/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.28/7.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 51.28/7.00      | r2_hidden(sK3(X1,X2,X0),X0) != iProver_top
% 51.28/7.00      | r1_tarski(X2,X0) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_28873,plain,
% 51.28/7.00      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 51.28/7.00      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 51.28/7.00      | r1_tarski(sK5,sK4) = iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4659,c_626]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_15,plain,
% 51.28/7.00      ( k2_subset_1(X0) = X0 ),
% 51.28/7.00      inference(cnf_transformation,[],[f62]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_16,plain,
% 51.28/7.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 51.28/7.00      inference(cnf_transformation,[],[f63]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_629,plain,
% 51.28/7.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1004,plain,
% 51.28/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_15,c_629]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1006,plain,
% 51.28/7.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK4)) = iProver_top ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_1004]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_28886,plain,
% 51.28/7.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top
% 51.28/7.00      | m1_subset_1(sK4,k1_zfmisc_1(sK4)) != iProver_top
% 51.28/7.00      | r1_tarski(sK5,sK4) = iProver_top ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_28873]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_153401,plain,
% 51.28/7.00      ( r1_tarski(sK5,sK4) = iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_28873,c_24,c_1006,c_28886]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2,plain,
% 51.28/7.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.28/7.00      inference(cnf_transformation,[],[f42]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_640,plain,
% 51.28/7.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_153405,plain,
% 51.28/7.00      ( k3_xboole_0(sK5,sK4) = sK5 ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_153401,c_640]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_0,plain,
% 51.28/7.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f40]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1,plain,
% 51.28/7.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
% 51.28/7.00      inference(cnf_transformation,[],[f77]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_820,plain,
% 51.28/7.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0 ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_153577,plain,
% 51.28/7.00      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_153405,c_820]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3,plain,
% 51.28/7.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f78]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_18,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.28/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 51.28/7.00      | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f79]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_627,plain,
% 51.28/7.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 51.28/7.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 51.28/7.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1732,plain,
% 51.28/7.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
% 51.28/7.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_1004,c_627]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8319,plain,
% 51.28/7.00      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4)) = k4_subset_1(sK4,sK5,sK4) ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_623,c_1732]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9545,plain,
% 51.28/7.00      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK5,sK4) ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_3,c_8319]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_154322,plain,
% 51.28/7.00      ( k4_subset_1(sK4,sK5,sK4) = sK4 ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_153577,c_9545]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_287,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4033,plain,
% 51.28/7.00      ( X0 != X1
% 51.28/7.00      | X0 = k4_subset_1(X2,sK5,X3)
% 51.28/7.00      | k4_subset_1(X2,sK5,X3) != X1 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_287]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4034,plain,
% 51.28/7.00      ( k4_subset_1(sK4,sK5,sK4) != sK4
% 51.28/7.00      | sK4 = k4_subset_1(sK4,sK5,sK4)
% 51.28/7.00      | sK4 != sK4 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_4033]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_796,plain,
% 51.28/7.00      ( X0 != X1
% 51.28/7.00      | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != X1
% 51.28/7.00      | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = X0 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_287]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2133,plain,
% 51.28/7.00      ( X0 != k4_subset_1(X1,sK5,X2)
% 51.28/7.00      | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = X0
% 51.28/7.00      | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != k4_subset_1(X1,sK5,X2) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_796]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2134,plain,
% 51.28/7.00      ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != k4_subset_1(sK4,sK5,sK4)
% 51.28/7.00      | k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = sK4
% 51.28/7.00      | sK4 != k4_subset_1(sK4,sK5,sK4) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_2133]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_295,plain,
% 51.28/7.00      ( X0 != X1
% 51.28/7.00      | X2 != X3
% 51.28/7.00      | X4 != X5
% 51.28/7.00      | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
% 51.28/7.00      theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_798,plain,
% 51.28/7.00      ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = k4_subset_1(X0,X1,X2)
% 51.28/7.00      | k2_subset_1(sK4) != X2
% 51.28/7.00      | sK5 != X1
% 51.28/7.00      | sK4 != X0 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_295]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1165,plain,
% 51.28/7.00      ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = k4_subset_1(X0,sK5,X1)
% 51.28/7.00      | k2_subset_1(sK4) != X1
% 51.28/7.00      | sK5 != sK5
% 51.28/7.00      | sK4 != X0 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_798]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1166,plain,
% 51.28/7.01      ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) = k4_subset_1(sK4,sK5,sK4)
% 51.28/7.01      | k2_subset_1(sK4) != sK4
% 51.28/7.01      | sK5 != sK5
% 51.28/7.01      | sK4 != sK4 ),
% 51.28/7.01      inference(instantiation,[status(thm)],[c_1165]) ).
% 51.28/7.01  
% 51.28/7.01  cnf(c_286,plain,( X0 = X0 ),theory(equality) ).
% 51.28/7.01  
% 51.28/7.01  cnf(c_879,plain,
% 51.28/7.01      ( sK5 = sK5 ),
% 51.28/7.01      inference(instantiation,[status(thm)],[c_286]) ).
% 51.28/7.01  
% 51.28/7.01  cnf(c_705,plain,
% 51.28/7.01      ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != X0
% 51.28/7.01      | k2_subset_1(sK4) != X0
% 51.28/7.01      | k2_subset_1(sK4) = k4_subset_1(sK4,sK5,k2_subset_1(sK4)) ),
% 51.28/7.01      inference(instantiation,[status(thm)],[c_287]) ).
% 51.28/7.01  
% 51.28/7.01  cnf(c_706,plain,
% 51.28/7.01      ( k4_subset_1(sK4,sK5,k2_subset_1(sK4)) != sK4
% 51.28/7.01      | k2_subset_1(sK4) = k4_subset_1(sK4,sK5,k2_subset_1(sK4))
% 51.28/7.01      | k2_subset_1(sK4) != sK4 ),
% 51.28/7.01      inference(instantiation,[status(thm)],[c_705]) ).
% 51.28/7.01  
% 51.28/7.01  cnf(c_304,plain,
% 51.28/7.01      ( sK4 = sK4 ),
% 51.28/7.01      inference(instantiation,[status(thm)],[c_286]) ).
% 51.28/7.01  
% 51.28/7.01  cnf(c_43,plain,
% 51.28/7.01      ( k2_subset_1(sK4) = sK4 ),
% 51.28/7.01      inference(instantiation,[status(thm)],[c_15]) ).
% 51.28/7.01  
% 51.28/7.01  cnf(c_22,negated_conjecture,
% 51.28/7.01      ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k2_subset_1(sK4)) ),
% 51.28/7.01      inference(cnf_transformation,[],[f70]) ).
% 51.28/7.01  
% 51.28/7.01  cnf(contradiction,plain,
% 51.28/7.01      ( $false ),
% 51.28/7.01      inference(minisat,
% 51.28/7.01                [status(thm)],
% 51.28/7.01                [c_154322,c_4034,c_2134,c_1166,c_879,c_706,c_304,c_43,
% 51.28/7.01                 c_22]) ).
% 51.28/7.01  
% 51.28/7.01  
% 51.28/7.01  % SZS output end CNFRefutation for theBenchmark.p
% 51.28/7.01  
% 51.28/7.01  ------                               Statistics
% 51.28/7.01  
% 51.28/7.01  ------ Selected
% 51.28/7.01  
% 51.28/7.01  total_time:                             6.196
% 51.28/7.01  
%------------------------------------------------------------------------------
