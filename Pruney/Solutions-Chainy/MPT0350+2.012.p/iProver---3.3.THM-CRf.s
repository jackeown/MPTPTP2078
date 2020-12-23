%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:07 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 439 expanded)
%              Number of clauses        :   52 ( 121 expanded)
%              Number of leaves         :   28 ( 113 expanded)
%              Depth                    :   19
%              Number of atoms          :  287 ( 946 expanded)
%              Number of equality atoms :  124 ( 393 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f33,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f43])).

fof(f76,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f40,f39,f38])).

fof(f61,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f61])).

fof(f16,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f72,f48])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f81])).

fof(f86,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f52,f82,f82])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f82])).

fof(f85,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f51,f83,f83,f48])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f75,f83])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f49,f83])).

fof(f77,plain,(
    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_227,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_671,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_672,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_677,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1544,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_672,c_677])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1822,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1544,c_31])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_683,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2161,plain,
    ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(sK4))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1822,c_683])).

cnf(c_13,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2162,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2161,c_13])).

cnf(c_3153,plain,
    ( k3_xboole_0(sK5,X0) = sK5
    | r2_hidden(sK0(sK5,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_2162])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_238,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_670,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_238])).

cnf(c_3494,plain,
    ( k3_xboole_0(sK5,sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_3153,c_670])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3916,plain,
    ( k3_xboole_0(sK4,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_3494,c_0])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_676,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1612,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_672,c_676])).

cnf(c_4042,plain,
    ( k3_subset_1(sK4,sK5) = k5_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3916,c_1612])).

cnf(c_6,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1819,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k3_subset_1(sK4,sK5))) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_1612,c_5])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_675,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_673,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_976,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0)) = k4_subset_1(sK4,sK5,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_672,c_673])).

cnf(c_1340,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k3_subset_1(sK4,X0))) = k4_subset_1(sK4,sK5,k3_subset_1(sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_675,c_976])).

cnf(c_1349,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k3_subset_1(sK4,sK5))) = k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_672,c_1340])).

cnf(c_1820,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4)) = k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1819,c_1349])).

cnf(c_1910,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_6,c_1820])).

cnf(c_4285,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_4042,c_1910])).

cnf(c_3,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_933,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_3914,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
    inference(superposition,[status(thm)],[c_3494,c_933])).

cnf(c_4290,plain,
    ( k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_4285,c_3914])).

cnf(c_23,negated_conjecture,
    ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_18,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_687,plain,
    ( k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) != sK4 ),
    inference(demodulation,[status(thm)],[c_23,c_18])).

cnf(c_4289,plain,
    ( k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) != sK4 ),
    inference(demodulation,[status(thm)],[c_4042,c_687])).

cnf(c_4293,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_4290,c_4289])).

cnf(c_4294,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4293])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:05:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.56/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/0.96  
% 3.56/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/0.96  
% 3.56/0.96  ------  iProver source info
% 3.56/0.96  
% 3.56/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.56/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/0.96  git: non_committed_changes: false
% 3.56/0.96  git: last_make_outside_of_git: false
% 3.56/0.96  
% 3.56/0.96  ------ 
% 3.56/0.96  
% 3.56/0.96  ------ Input Options
% 3.56/0.96  
% 3.56/0.96  --out_options                           all
% 3.56/0.96  --tptp_safe_out                         true
% 3.56/0.96  --problem_path                          ""
% 3.56/0.96  --include_path                          ""
% 3.56/0.96  --clausifier                            res/vclausify_rel
% 3.56/0.96  --clausifier_options                    ""
% 3.56/0.96  --stdin                                 false
% 3.56/0.96  --stats_out                             all
% 3.56/0.96  
% 3.56/0.96  ------ General Options
% 3.56/0.96  
% 3.56/0.96  --fof                                   false
% 3.56/0.96  --time_out_real                         305.
% 3.56/0.96  --time_out_virtual                      -1.
% 3.56/0.96  --symbol_type_check                     false
% 3.56/0.96  --clausify_out                          false
% 3.56/0.96  --sig_cnt_out                           false
% 3.56/0.96  --trig_cnt_out                          false
% 3.56/0.96  --trig_cnt_out_tolerance                1.
% 3.56/0.96  --trig_cnt_out_sk_spl                   false
% 3.56/0.96  --abstr_cl_out                          false
% 3.56/0.96  
% 3.56/0.96  ------ Global Options
% 3.56/0.96  
% 3.56/0.96  --schedule                              default
% 3.56/0.96  --add_important_lit                     false
% 3.56/0.96  --prop_solver_per_cl                    1000
% 3.56/0.96  --min_unsat_core                        false
% 3.56/0.96  --soft_assumptions                      false
% 3.56/0.96  --soft_lemma_size                       3
% 3.56/0.96  --prop_impl_unit_size                   0
% 3.56/0.96  --prop_impl_unit                        []
% 3.56/0.96  --share_sel_clauses                     true
% 3.56/0.96  --reset_solvers                         false
% 3.56/0.96  --bc_imp_inh                            [conj_cone]
% 3.56/0.96  --conj_cone_tolerance                   3.
% 3.56/0.96  --extra_neg_conj                        none
% 3.56/0.96  --large_theory_mode                     true
% 3.56/0.96  --prolific_symb_bound                   200
% 3.56/0.96  --lt_threshold                          2000
% 3.56/0.96  --clause_weak_htbl                      true
% 3.56/0.96  --gc_record_bc_elim                     false
% 3.56/0.96  
% 3.56/0.96  ------ Preprocessing Options
% 3.56/0.96  
% 3.56/0.96  --preprocessing_flag                    true
% 3.56/0.96  --time_out_prep_mult                    0.1
% 3.56/0.96  --splitting_mode                        input
% 3.56/0.96  --splitting_grd                         true
% 3.56/0.96  --splitting_cvd                         false
% 3.56/0.96  --splitting_cvd_svl                     false
% 3.56/0.96  --splitting_nvd                         32
% 3.56/0.96  --sub_typing                            true
% 3.56/0.96  --prep_gs_sim                           true
% 3.56/0.96  --prep_unflatten                        true
% 3.56/0.96  --prep_res_sim                          true
% 3.56/0.96  --prep_upred                            true
% 3.56/0.96  --prep_sem_filter                       exhaustive
% 3.56/0.96  --prep_sem_filter_out                   false
% 3.56/0.96  --pred_elim                             true
% 3.56/0.96  --res_sim_input                         true
% 3.56/0.96  --eq_ax_congr_red                       true
% 3.56/0.96  --pure_diseq_elim                       true
% 3.56/0.96  --brand_transform                       false
% 3.56/0.96  --non_eq_to_eq                          false
% 3.56/0.96  --prep_def_merge                        true
% 3.56/0.96  --prep_def_merge_prop_impl              false
% 3.56/0.96  --prep_def_merge_mbd                    true
% 3.56/0.96  --prep_def_merge_tr_red                 false
% 3.56/0.96  --prep_def_merge_tr_cl                  false
% 3.56/0.96  --smt_preprocessing                     true
% 3.56/0.96  --smt_ac_axioms                         fast
% 3.56/0.96  --preprocessed_out                      false
% 3.56/0.96  --preprocessed_stats                    false
% 3.56/0.96  
% 3.56/0.96  ------ Abstraction refinement Options
% 3.56/0.96  
% 3.56/0.96  --abstr_ref                             []
% 3.56/0.96  --abstr_ref_prep                        false
% 3.56/0.96  --abstr_ref_until_sat                   false
% 3.56/0.96  --abstr_ref_sig_restrict                funpre
% 3.56/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/0.96  --abstr_ref_under                       []
% 3.56/0.96  
% 3.56/0.96  ------ SAT Options
% 3.56/0.96  
% 3.56/0.96  --sat_mode                              false
% 3.56/0.96  --sat_fm_restart_options                ""
% 3.56/0.96  --sat_gr_def                            false
% 3.56/0.96  --sat_epr_types                         true
% 3.56/0.96  --sat_non_cyclic_types                  false
% 3.56/0.96  --sat_finite_models                     false
% 3.56/0.96  --sat_fm_lemmas                         false
% 3.56/0.96  --sat_fm_prep                           false
% 3.56/0.96  --sat_fm_uc_incr                        true
% 3.56/0.96  --sat_out_model                         small
% 3.56/0.96  --sat_out_clauses                       false
% 3.56/0.96  
% 3.56/0.96  ------ QBF Options
% 3.56/0.96  
% 3.56/0.96  --qbf_mode                              false
% 3.56/0.96  --qbf_elim_univ                         false
% 3.56/0.96  --qbf_dom_inst                          none
% 3.56/0.96  --qbf_dom_pre_inst                      false
% 3.56/0.96  --qbf_sk_in                             false
% 3.56/0.96  --qbf_pred_elim                         true
% 3.56/0.96  --qbf_split                             512
% 3.56/0.96  
% 3.56/0.96  ------ BMC1 Options
% 3.56/0.96  
% 3.56/0.96  --bmc1_incremental                      false
% 3.56/0.96  --bmc1_axioms                           reachable_all
% 3.56/0.96  --bmc1_min_bound                        0
% 3.56/0.96  --bmc1_max_bound                        -1
% 3.56/0.96  --bmc1_max_bound_default                -1
% 3.56/0.96  --bmc1_symbol_reachability              true
% 3.56/0.96  --bmc1_property_lemmas                  false
% 3.56/0.96  --bmc1_k_induction                      false
% 3.56/0.96  --bmc1_non_equiv_states                 false
% 3.56/0.96  --bmc1_deadlock                         false
% 3.56/0.96  --bmc1_ucm                              false
% 3.56/0.96  --bmc1_add_unsat_core                   none
% 3.56/0.96  --bmc1_unsat_core_children              false
% 3.56/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/0.96  --bmc1_out_stat                         full
% 3.56/0.96  --bmc1_ground_init                      false
% 3.56/0.96  --bmc1_pre_inst_next_state              false
% 3.56/0.96  --bmc1_pre_inst_state                   false
% 3.56/0.96  --bmc1_pre_inst_reach_state             false
% 3.56/0.96  --bmc1_out_unsat_core                   false
% 3.56/0.96  --bmc1_aig_witness_out                  false
% 3.56/0.96  --bmc1_verbose                          false
% 3.56/0.96  --bmc1_dump_clauses_tptp                false
% 3.56/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.56/0.96  --bmc1_dump_file                        -
% 3.56/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.56/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.56/0.96  --bmc1_ucm_extend_mode                  1
% 3.56/0.96  --bmc1_ucm_init_mode                    2
% 3.56/0.96  --bmc1_ucm_cone_mode                    none
% 3.56/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.56/0.96  --bmc1_ucm_relax_model                  4
% 3.56/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.56/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/0.96  --bmc1_ucm_layered_model                none
% 3.56/0.96  --bmc1_ucm_max_lemma_size               10
% 3.56/0.96  
% 3.56/0.96  ------ AIG Options
% 3.56/0.96  
% 3.56/0.96  --aig_mode                              false
% 3.56/0.96  
% 3.56/0.96  ------ Instantiation Options
% 3.56/0.96  
% 3.56/0.96  --instantiation_flag                    true
% 3.56/0.96  --inst_sos_flag                         true
% 3.56/0.96  --inst_sos_phase                        true
% 3.56/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/0.96  --inst_lit_sel_side                     num_symb
% 3.56/0.96  --inst_solver_per_active                1400
% 3.56/0.96  --inst_solver_calls_frac                1.
% 3.56/0.96  --inst_passive_queue_type               priority_queues
% 3.56/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/0.96  --inst_passive_queues_freq              [25;2]
% 3.56/0.96  --inst_dismatching                      true
% 3.56/0.96  --inst_eager_unprocessed_to_passive     true
% 3.56/0.96  --inst_prop_sim_given                   true
% 3.56/0.96  --inst_prop_sim_new                     false
% 3.56/0.96  --inst_subs_new                         false
% 3.56/0.96  --inst_eq_res_simp                      false
% 3.56/0.96  --inst_subs_given                       false
% 3.56/0.96  --inst_orphan_elimination               true
% 3.56/0.96  --inst_learning_loop_flag               true
% 3.56/0.96  --inst_learning_start                   3000
% 3.56/0.96  --inst_learning_factor                  2
% 3.56/0.96  --inst_start_prop_sim_after_learn       3
% 3.56/0.96  --inst_sel_renew                        solver
% 3.56/0.96  --inst_lit_activity_flag                true
% 3.56/0.96  --inst_restr_to_given                   false
% 3.56/0.96  --inst_activity_threshold               500
% 3.56/0.96  --inst_out_proof                        true
% 3.56/0.96  
% 3.56/0.96  ------ Resolution Options
% 3.56/0.96  
% 3.56/0.96  --resolution_flag                       true
% 3.56/0.96  --res_lit_sel                           adaptive
% 3.56/0.96  --res_lit_sel_side                      none
% 3.56/0.96  --res_ordering                          kbo
% 3.56/0.96  --res_to_prop_solver                    active
% 3.56/0.96  --res_prop_simpl_new                    false
% 3.56/0.96  --res_prop_simpl_given                  true
% 3.56/0.96  --res_passive_queue_type                priority_queues
% 3.56/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/0.96  --res_passive_queues_freq               [15;5]
% 3.56/0.96  --res_forward_subs                      full
% 3.56/0.96  --res_backward_subs                     full
% 3.56/0.96  --res_forward_subs_resolution           true
% 3.56/0.96  --res_backward_subs_resolution          true
% 3.56/0.96  --res_orphan_elimination                true
% 3.56/0.96  --res_time_limit                        2.
% 3.56/0.96  --res_out_proof                         true
% 3.56/0.96  
% 3.56/0.96  ------ Superposition Options
% 3.56/0.96  
% 3.56/0.96  --superposition_flag                    true
% 3.56/0.96  --sup_passive_queue_type                priority_queues
% 3.56/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.56/0.96  --demod_completeness_check              fast
% 3.56/0.96  --demod_use_ground                      true
% 3.56/0.96  --sup_to_prop_solver                    passive
% 3.56/0.96  --sup_prop_simpl_new                    true
% 3.56/0.96  --sup_prop_simpl_given                  true
% 3.56/0.96  --sup_fun_splitting                     true
% 3.56/0.96  --sup_smt_interval                      50000
% 3.56/0.96  
% 3.56/0.96  ------ Superposition Simplification Setup
% 3.56/0.96  
% 3.56/0.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.56/0.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.56/0.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.56/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.56/0.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.56/0.96  --sup_immed_triv                        [TrivRules]
% 3.56/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.96  --sup_immed_bw_main                     []
% 3.56/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.56/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.96  --sup_input_bw                          []
% 3.56/0.96  
% 3.56/0.96  ------ Combination Options
% 3.56/0.96  
% 3.56/0.96  --comb_res_mult                         3
% 3.56/0.96  --comb_sup_mult                         2
% 3.56/0.96  --comb_inst_mult                        10
% 3.56/0.96  
% 3.56/0.96  ------ Debug Options
% 3.56/0.96  
% 3.56/0.96  --dbg_backtrace                         false
% 3.56/0.96  --dbg_dump_prop_clauses                 false
% 3.56/0.96  --dbg_dump_prop_clauses_file            -
% 3.56/0.96  --dbg_out_stat                          false
% 3.56/0.96  ------ Parsing...
% 3.56/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/0.96  
% 3.56/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.56/0.96  
% 3.56/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/0.96  
% 3.56/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/0.96  ------ Proving...
% 3.56/0.96  ------ Problem Properties 
% 3.56/0.96  
% 3.56/0.96  
% 3.56/0.96  clauses                                 24
% 3.56/0.96  conjectures                             2
% 3.56/0.96  EPR                                     4
% 3.56/0.96  Horn                                    19
% 3.56/0.96  unary                                   9
% 3.56/0.96  binary                                  6
% 3.56/0.96  lits                                    49
% 3.56/0.96  lits eq                                 14
% 3.56/0.96  fd_pure                                 0
% 3.56/0.96  fd_pseudo                               0
% 3.56/0.96  fd_cond                                 0
% 3.56/0.96  fd_pseudo_cond                          3
% 3.56/0.96  AC symbols                              0
% 3.56/0.96  
% 3.56/0.96  ------ Schedule dynamic 5 is on 
% 3.56/0.96  
% 3.56/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.56/0.96  
% 3.56/0.96  
% 3.56/0.96  ------ 
% 3.56/0.96  Current options:
% 3.56/0.96  ------ 
% 3.56/0.96  
% 3.56/0.96  ------ Input Options
% 3.56/0.96  
% 3.56/0.96  --out_options                           all
% 3.56/0.96  --tptp_safe_out                         true
% 3.56/0.96  --problem_path                          ""
% 3.56/0.96  --include_path                          ""
% 3.56/0.96  --clausifier                            res/vclausify_rel
% 3.56/0.96  --clausifier_options                    ""
% 3.56/0.96  --stdin                                 false
% 3.56/0.96  --stats_out                             all
% 3.56/0.96  
% 3.56/0.96  ------ General Options
% 3.56/0.96  
% 3.56/0.96  --fof                                   false
% 3.56/0.96  --time_out_real                         305.
% 3.56/0.96  --time_out_virtual                      -1.
% 3.56/0.96  --symbol_type_check                     false
% 3.56/0.96  --clausify_out                          false
% 3.56/0.96  --sig_cnt_out                           false
% 3.56/0.96  --trig_cnt_out                          false
% 3.56/0.96  --trig_cnt_out_tolerance                1.
% 3.56/0.96  --trig_cnt_out_sk_spl                   false
% 3.56/0.96  --abstr_cl_out                          false
% 3.56/0.96  
% 3.56/0.96  ------ Global Options
% 3.56/0.96  
% 3.56/0.96  --schedule                              default
% 3.56/0.96  --add_important_lit                     false
% 3.56/0.96  --prop_solver_per_cl                    1000
% 3.56/0.96  --min_unsat_core                        false
% 3.56/0.96  --soft_assumptions                      false
% 3.56/0.96  --soft_lemma_size                       3
% 3.56/0.96  --prop_impl_unit_size                   0
% 3.56/0.96  --prop_impl_unit                        []
% 3.56/0.96  --share_sel_clauses                     true
% 3.56/0.96  --reset_solvers                         false
% 3.56/0.96  --bc_imp_inh                            [conj_cone]
% 3.56/0.96  --conj_cone_tolerance                   3.
% 3.56/0.96  --extra_neg_conj                        none
% 3.56/0.96  --large_theory_mode                     true
% 3.56/0.96  --prolific_symb_bound                   200
% 3.56/0.96  --lt_threshold                          2000
% 3.56/0.96  --clause_weak_htbl                      true
% 3.56/0.96  --gc_record_bc_elim                     false
% 3.56/0.96  
% 3.56/0.96  ------ Preprocessing Options
% 3.56/0.96  
% 3.56/0.96  --preprocessing_flag                    true
% 3.56/0.96  --time_out_prep_mult                    0.1
% 3.56/0.96  --splitting_mode                        input
% 3.56/0.96  --splitting_grd                         true
% 3.56/0.96  --splitting_cvd                         false
% 3.56/0.96  --splitting_cvd_svl                     false
% 3.56/0.96  --splitting_nvd                         32
% 3.56/0.96  --sub_typing                            true
% 3.56/0.96  --prep_gs_sim                           true
% 3.56/0.96  --prep_unflatten                        true
% 3.56/0.96  --prep_res_sim                          true
% 3.56/0.96  --prep_upred                            true
% 3.56/0.96  --prep_sem_filter                       exhaustive
% 3.56/0.96  --prep_sem_filter_out                   false
% 3.56/0.96  --pred_elim                             true
% 3.56/0.96  --res_sim_input                         true
% 3.56/0.96  --eq_ax_congr_red                       true
% 3.56/0.96  --pure_diseq_elim                       true
% 3.56/0.96  --brand_transform                       false
% 3.56/0.96  --non_eq_to_eq                          false
% 3.56/0.96  --prep_def_merge                        true
% 3.56/0.96  --prep_def_merge_prop_impl              false
% 3.56/0.96  --prep_def_merge_mbd                    true
% 3.56/0.96  --prep_def_merge_tr_red                 false
% 3.56/0.96  --prep_def_merge_tr_cl                  false
% 3.56/0.96  --smt_preprocessing                     true
% 3.56/0.96  --smt_ac_axioms                         fast
% 3.56/0.96  --preprocessed_out                      false
% 3.56/0.96  --preprocessed_stats                    false
% 3.56/0.96  
% 3.56/0.96  ------ Abstraction refinement Options
% 3.56/0.96  
% 3.56/0.96  --abstr_ref                             []
% 3.56/0.96  --abstr_ref_prep                        false
% 3.56/0.96  --abstr_ref_until_sat                   false
% 3.56/0.96  --abstr_ref_sig_restrict                funpre
% 3.56/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/0.96  --abstr_ref_under                       []
% 3.56/0.96  
% 3.56/0.96  ------ SAT Options
% 3.56/0.96  
% 3.56/0.96  --sat_mode                              false
% 3.56/0.96  --sat_fm_restart_options                ""
% 3.56/0.96  --sat_gr_def                            false
% 3.56/0.96  --sat_epr_types                         true
% 3.56/0.96  --sat_non_cyclic_types                  false
% 3.56/0.96  --sat_finite_models                     false
% 3.56/0.96  --sat_fm_lemmas                         false
% 3.56/0.96  --sat_fm_prep                           false
% 3.56/0.96  --sat_fm_uc_incr                        true
% 3.56/0.96  --sat_out_model                         small
% 3.56/0.96  --sat_out_clauses                       false
% 3.56/0.96  
% 3.56/0.96  ------ QBF Options
% 3.56/0.96  
% 3.56/0.96  --qbf_mode                              false
% 3.56/0.96  --qbf_elim_univ                         false
% 3.56/0.96  --qbf_dom_inst                          none
% 3.56/0.96  --qbf_dom_pre_inst                      false
% 3.56/0.96  --qbf_sk_in                             false
% 3.56/0.96  --qbf_pred_elim                         true
% 3.56/0.96  --qbf_split                             512
% 3.56/0.96  
% 3.56/0.96  ------ BMC1 Options
% 3.56/0.96  
% 3.56/0.96  --bmc1_incremental                      false
% 3.56/0.96  --bmc1_axioms                           reachable_all
% 3.56/0.96  --bmc1_min_bound                        0
% 3.56/0.96  --bmc1_max_bound                        -1
% 3.56/0.96  --bmc1_max_bound_default                -1
% 3.56/0.96  --bmc1_symbol_reachability              true
% 3.56/0.96  --bmc1_property_lemmas                  false
% 3.56/0.96  --bmc1_k_induction                      false
% 3.56/0.96  --bmc1_non_equiv_states                 false
% 3.56/0.96  --bmc1_deadlock                         false
% 3.56/0.96  --bmc1_ucm                              false
% 3.56/0.96  --bmc1_add_unsat_core                   none
% 3.56/0.96  --bmc1_unsat_core_children              false
% 3.56/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/0.96  --bmc1_out_stat                         full
% 3.56/0.96  --bmc1_ground_init                      false
% 3.56/0.96  --bmc1_pre_inst_next_state              false
% 3.56/0.96  --bmc1_pre_inst_state                   false
% 3.56/0.96  --bmc1_pre_inst_reach_state             false
% 3.56/0.96  --bmc1_out_unsat_core                   false
% 3.56/0.96  --bmc1_aig_witness_out                  false
% 3.56/0.96  --bmc1_verbose                          false
% 3.56/0.96  --bmc1_dump_clauses_tptp                false
% 3.56/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.56/0.96  --bmc1_dump_file                        -
% 3.56/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.56/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.56/0.96  --bmc1_ucm_extend_mode                  1
% 3.56/0.96  --bmc1_ucm_init_mode                    2
% 3.56/0.96  --bmc1_ucm_cone_mode                    none
% 3.56/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.56/0.96  --bmc1_ucm_relax_model                  4
% 3.56/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.56/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/0.96  --bmc1_ucm_layered_model                none
% 3.56/0.96  --bmc1_ucm_max_lemma_size               10
% 3.56/0.96  
% 3.56/0.96  ------ AIG Options
% 3.56/0.96  
% 3.56/0.96  --aig_mode                              false
% 3.56/0.96  
% 3.56/0.96  ------ Instantiation Options
% 3.56/0.96  
% 3.56/0.96  --instantiation_flag                    true
% 3.56/0.96  --inst_sos_flag                         true
% 3.56/0.96  --inst_sos_phase                        true
% 3.56/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/0.96  --inst_lit_sel_side                     none
% 3.56/0.96  --inst_solver_per_active                1400
% 3.56/0.96  --inst_solver_calls_frac                1.
% 3.56/0.96  --inst_passive_queue_type               priority_queues
% 3.56/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/0.96  --inst_passive_queues_freq              [25;2]
% 3.56/0.96  --inst_dismatching                      true
% 3.56/0.96  --inst_eager_unprocessed_to_passive     true
% 3.56/0.96  --inst_prop_sim_given                   true
% 3.56/0.96  --inst_prop_sim_new                     false
% 3.56/0.96  --inst_subs_new                         false
% 3.56/0.96  --inst_eq_res_simp                      false
% 3.56/0.96  --inst_subs_given                       false
% 3.56/0.96  --inst_orphan_elimination               true
% 3.56/0.96  --inst_learning_loop_flag               true
% 3.56/0.96  --inst_learning_start                   3000
% 3.56/0.96  --inst_learning_factor                  2
% 3.56/0.96  --inst_start_prop_sim_after_learn       3
% 3.56/0.96  --inst_sel_renew                        solver
% 3.56/0.96  --inst_lit_activity_flag                true
% 3.56/0.96  --inst_restr_to_given                   false
% 3.56/0.96  --inst_activity_threshold               500
% 3.56/0.96  --inst_out_proof                        true
% 3.56/0.96  
% 3.56/0.96  ------ Resolution Options
% 3.56/0.96  
% 3.56/0.96  --resolution_flag                       false
% 3.56/0.96  --res_lit_sel                           adaptive
% 3.56/0.96  --res_lit_sel_side                      none
% 3.56/0.96  --res_ordering                          kbo
% 3.56/0.96  --res_to_prop_solver                    active
% 3.56/0.96  --res_prop_simpl_new                    false
% 3.56/0.96  --res_prop_simpl_given                  true
% 3.56/0.96  --res_passive_queue_type                priority_queues
% 3.56/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/0.96  --res_passive_queues_freq               [15;5]
% 3.56/0.96  --res_forward_subs                      full
% 3.56/0.96  --res_backward_subs                     full
% 3.56/0.96  --res_forward_subs_resolution           true
% 3.56/0.96  --res_backward_subs_resolution          true
% 3.56/0.96  --res_orphan_elimination                true
% 3.56/0.96  --res_time_limit                        2.
% 3.56/0.96  --res_out_proof                         true
% 3.56/0.96  
% 3.56/0.96  ------ Superposition Options
% 3.56/0.96  
% 3.56/0.96  --superposition_flag                    true
% 3.56/0.96  --sup_passive_queue_type                priority_queues
% 3.56/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.56/0.96  --demod_completeness_check              fast
% 3.56/0.96  --demod_use_ground                      true
% 3.56/0.96  --sup_to_prop_solver                    passive
% 3.56/0.96  --sup_prop_simpl_new                    true
% 3.56/0.96  --sup_prop_simpl_given                  true
% 3.56/0.96  --sup_fun_splitting                     true
% 3.56/0.96  --sup_smt_interval                      50000
% 3.56/0.96  
% 3.56/0.96  ------ Superposition Simplification Setup
% 3.56/0.96  
% 3.56/0.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.56/0.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.56/0.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.56/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.56/0.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.56/0.96  --sup_immed_triv                        [TrivRules]
% 3.56/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.96  --sup_immed_bw_main                     []
% 3.56/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.56/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.96  --sup_input_bw                          []
% 3.56/0.96  
% 3.56/0.96  ------ Combination Options
% 3.56/0.96  
% 3.56/0.96  --comb_res_mult                         3
% 3.56/0.96  --comb_sup_mult                         2
% 3.56/0.96  --comb_inst_mult                        10
% 3.56/0.96  
% 3.56/0.96  ------ Debug Options
% 3.56/0.96  
% 3.56/0.96  --dbg_backtrace                         false
% 3.56/0.96  --dbg_dump_prop_clauses                 false
% 3.56/0.96  --dbg_dump_prop_clauses_file            -
% 3.56/0.96  --dbg_out_stat                          false
% 3.56/0.96  
% 3.56/0.96  
% 3.56/0.96  
% 3.56/0.96  
% 3.56/0.96  ------ Proving...
% 3.56/0.96  
% 3.56/0.96  
% 3.56/0.96  % SZS status Theorem for theBenchmark.p
% 3.56/0.96  
% 3.56/0.96   Resolution empty clause
% 3.56/0.96  
% 3.56/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/0.96  
% 3.56/0.96  fof(f2,axiom,(
% 3.56/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f25,plain,(
% 3.56/0.96    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.56/0.96    inference(unused_predicate_definition_removal,[],[f2])).
% 3.56/0.96  
% 3.56/0.96  fof(f26,plain,(
% 3.56/0.96    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.56/0.96    inference(ennf_transformation,[],[f25])).
% 3.56/0.96  
% 3.56/0.96  fof(f34,plain,(
% 3.56/0.96    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.56/0.96    introduced(choice_axiom,[])).
% 3.56/0.96  
% 3.56/0.96  fof(f35,plain,(
% 3.56/0.96    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.56/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f34])).
% 3.56/0.96  
% 3.56/0.96  fof(f46,plain,(
% 3.56/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f35])).
% 3.56/0.96  
% 3.56/0.96  fof(f5,axiom,(
% 3.56/0.96    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f27,plain,(
% 3.56/0.96    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.56/0.96    inference(ennf_transformation,[],[f5])).
% 3.56/0.96  
% 3.56/0.96  fof(f50,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f27])).
% 3.56/0.96  
% 3.56/0.96  fof(f23,conjecture,(
% 3.56/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f24,negated_conjecture,(
% 3.56/0.96    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 3.56/0.96    inference(negated_conjecture,[],[f23])).
% 3.56/0.96  
% 3.56/0.96  fof(f33,plain,(
% 3.56/0.96    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.96    inference(ennf_transformation,[],[f24])).
% 3.56/0.96  
% 3.56/0.96  fof(f43,plain,(
% 3.56/0.96    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 3.56/0.96    introduced(choice_axiom,[])).
% 3.56/0.96  
% 3.56/0.96  fof(f44,plain,(
% 3.56/0.96    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 3.56/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f43])).
% 3.56/0.96  
% 3.56/0.96  fof(f76,plain,(
% 3.56/0.96    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 3.56/0.96    inference(cnf_transformation,[],[f44])).
% 3.56/0.96  
% 3.56/0.96  fof(f17,axiom,(
% 3.56/0.96    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f28,plain,(
% 3.56/0.96    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.56/0.96    inference(ennf_transformation,[],[f17])).
% 3.56/0.96  
% 3.56/0.96  fof(f42,plain,(
% 3.56/0.96    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.56/0.96    inference(nnf_transformation,[],[f28])).
% 3.56/0.96  
% 3.56/0.96  fof(f67,plain,(
% 3.56/0.96    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f42])).
% 3.56/0.96  
% 3.56/0.96  fof(f21,axiom,(
% 3.56/0.96    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f74,plain,(
% 3.56/0.96    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.56/0.96    inference(cnf_transformation,[],[f21])).
% 3.56/0.96  
% 3.56/0.96  fof(f14,axiom,(
% 3.56/0.96    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f36,plain,(
% 3.56/0.96    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.56/0.96    inference(nnf_transformation,[],[f14])).
% 3.56/0.96  
% 3.56/0.96  fof(f37,plain,(
% 3.56/0.96    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.56/0.96    inference(rectify,[],[f36])).
% 3.56/0.96  
% 3.56/0.96  fof(f40,plain,(
% 3.56/0.96    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 3.56/0.96    introduced(choice_axiom,[])).
% 3.56/0.96  
% 3.56/0.96  fof(f39,plain,(
% 3.56/0.96    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 3.56/0.96    introduced(choice_axiom,[])).
% 3.56/0.96  
% 3.56/0.96  fof(f38,plain,(
% 3.56/0.96    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.56/0.96    introduced(choice_axiom,[])).
% 3.56/0.96  
% 3.56/0.96  fof(f41,plain,(
% 3.56/0.96    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.56/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f40,f39,f38])).
% 3.56/0.96  
% 3.56/0.96  fof(f61,plain,(
% 3.56/0.96    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 3.56/0.96    inference(cnf_transformation,[],[f41])).
% 3.56/0.96  
% 3.56/0.96  fof(f89,plain,(
% 3.56/0.96    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 3.56/0.96    inference(equality_resolution,[],[f61])).
% 3.56/0.96  
% 3.56/0.96  fof(f16,axiom,(
% 3.56/0.96    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f66,plain,(
% 3.56/0.96    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.56/0.96    inference(cnf_transformation,[],[f16])).
% 3.56/0.96  
% 3.56/0.96  fof(f47,plain,(
% 3.56/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f35])).
% 3.56/0.96  
% 3.56/0.96  fof(f1,axiom,(
% 3.56/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f45,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f1])).
% 3.56/0.96  
% 3.56/0.96  fof(f19,axiom,(
% 3.56/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f29,plain,(
% 3.56/0.96    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.96    inference(ennf_transformation,[],[f19])).
% 3.56/0.96  
% 3.56/0.96  fof(f72,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.96    inference(cnf_transformation,[],[f29])).
% 3.56/0.96  
% 3.56/0.96  fof(f3,axiom,(
% 3.56/0.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f48,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.56/0.96    inference(cnf_transformation,[],[f3])).
% 3.56/0.96  
% 3.56/0.96  fof(f87,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.96    inference(definition_unfolding,[],[f72,f48])).
% 3.56/0.96  
% 3.56/0.96  fof(f7,axiom,(
% 3.56/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f52,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f7])).
% 3.56/0.96  
% 3.56/0.96  fof(f8,axiom,(
% 3.56/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f53,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f8])).
% 3.56/0.96  
% 3.56/0.96  fof(f9,axiom,(
% 3.56/0.96    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f54,plain,(
% 3.56/0.96    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f9])).
% 3.56/0.96  
% 3.56/0.96  fof(f10,axiom,(
% 3.56/0.96    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f55,plain,(
% 3.56/0.96    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f10])).
% 3.56/0.96  
% 3.56/0.96  fof(f11,axiom,(
% 3.56/0.96    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f56,plain,(
% 3.56/0.96    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f11])).
% 3.56/0.96  
% 3.56/0.96  fof(f12,axiom,(
% 3.56/0.96    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f57,plain,(
% 3.56/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f12])).
% 3.56/0.96  
% 3.56/0.96  fof(f13,axiom,(
% 3.56/0.96    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f58,plain,(
% 3.56/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.56/0.96    inference(cnf_transformation,[],[f13])).
% 3.56/0.96  
% 3.56/0.96  fof(f78,plain,(
% 3.56/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.56/0.96    inference(definition_unfolding,[],[f57,f58])).
% 3.56/0.96  
% 3.56/0.96  fof(f79,plain,(
% 3.56/0.96    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.56/0.96    inference(definition_unfolding,[],[f56,f78])).
% 3.56/0.96  
% 3.56/0.96  fof(f80,plain,(
% 3.56/0.96    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.56/0.96    inference(definition_unfolding,[],[f55,f79])).
% 3.56/0.96  
% 3.56/0.96  fof(f81,plain,(
% 3.56/0.96    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.56/0.96    inference(definition_unfolding,[],[f54,f80])).
% 3.56/0.96  
% 3.56/0.96  fof(f82,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.56/0.96    inference(definition_unfolding,[],[f53,f81])).
% 3.56/0.96  
% 3.56/0.96  fof(f86,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.56/0.96    inference(definition_unfolding,[],[f52,f82,f82])).
% 3.56/0.96  
% 3.56/0.96  fof(f6,axiom,(
% 3.56/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f51,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.56/0.96    inference(cnf_transformation,[],[f6])).
% 3.56/0.96  
% 3.56/0.96  fof(f15,axiom,(
% 3.56/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f65,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.56/0.96    inference(cnf_transformation,[],[f15])).
% 3.56/0.96  
% 3.56/0.96  fof(f83,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.56/0.96    inference(definition_unfolding,[],[f65,f82])).
% 3.56/0.96  
% 3.56/0.96  fof(f85,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.56/0.96    inference(definition_unfolding,[],[f51,f83,f83,f48])).
% 3.56/0.96  
% 3.56/0.96  fof(f20,axiom,(
% 3.56/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f30,plain,(
% 3.56/0.96    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.96    inference(ennf_transformation,[],[f20])).
% 3.56/0.96  
% 3.56/0.96  fof(f73,plain,(
% 3.56/0.96    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.96    inference(cnf_transformation,[],[f30])).
% 3.56/0.96  
% 3.56/0.96  fof(f22,axiom,(
% 3.56/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f31,plain,(
% 3.56/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.56/0.96    inference(ennf_transformation,[],[f22])).
% 3.56/0.96  
% 3.56/0.96  fof(f32,plain,(
% 3.56/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.96    inference(flattening,[],[f31])).
% 3.56/0.96  
% 3.56/0.96  fof(f75,plain,(
% 3.56/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.96    inference(cnf_transformation,[],[f32])).
% 3.56/0.96  
% 3.56/0.96  fof(f88,plain,(
% 3.56/0.96    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.96    inference(definition_unfolding,[],[f75,f83])).
% 3.56/0.96  
% 3.56/0.96  fof(f4,axiom,(
% 3.56/0.96    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f49,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.56/0.96    inference(cnf_transformation,[],[f4])).
% 3.56/0.96  
% 3.56/0.96  fof(f84,plain,(
% 3.56/0.96    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 3.56/0.96    inference(definition_unfolding,[],[f49,f83])).
% 3.56/0.96  
% 3.56/0.96  fof(f77,plain,(
% 3.56/0.96    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5))),
% 3.56/0.96    inference(cnf_transformation,[],[f44])).
% 3.56/0.96  
% 3.56/0.96  fof(f18,axiom,(
% 3.56/0.96    ! [X0] : k2_subset_1(X0) = X0),
% 3.56/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.96  
% 3.56/0.96  fof(f71,plain,(
% 3.56/0.96    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.56/0.96    inference(cnf_transformation,[],[f18])).
% 3.56/0.96  
% 3.56/0.96  cnf(c_2,plain,
% 3.56/0.96      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.56/0.96      inference(cnf_transformation,[],[f46]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_4,plain,
% 3.56/0.96      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.56/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_227,plain,
% 3.56/0.96      ( r2_hidden(sK0(X0,X1),X0) | k3_xboole_0(X0,X1) = X0 ),
% 3.56/0.96      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_671,plain,
% 3.56/0.96      ( k3_xboole_0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 3.56/0.96      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_24,negated_conjecture,
% 3.56/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 3.56/0.96      inference(cnf_transformation,[],[f76]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_672,plain,
% 3.56/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.56/0.96      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_17,plain,
% 3.56/0.96      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.56/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_677,plain,
% 3.56/0.96      ( m1_subset_1(X0,X1) != iProver_top
% 3.56/0.96      | r2_hidden(X0,X1) = iProver_top
% 3.56/0.96      | v1_xboole_0(X1) = iProver_top ),
% 3.56/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_1544,plain,
% 3.56/0.96      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 3.56/0.96      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_672,c_677]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_21,plain,
% 3.56/0.96      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.56/0.96      inference(cnf_transformation,[],[f74]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_29,plain,
% 3.56/0.96      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.56/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_31,plain,
% 3.56/0.96      ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
% 3.56/0.96      inference(instantiation,[status(thm)],[c_29]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_1822,plain,
% 3.56/0.96      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.56/0.96      inference(global_propositional_subsumption,[status(thm)],[c_1544,c_31]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_10,plain,
% 3.56/0.96      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,k3_tarski(X1)) ),
% 3.56/0.96      inference(cnf_transformation,[],[f89]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_683,plain,
% 3.56/0.96      ( r2_hidden(X0,X1) != iProver_top
% 3.56/0.96      | r2_hidden(X2,X0) != iProver_top
% 3.56/0.96      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 3.56/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_2161,plain,
% 3.56/0.96      ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(sK4))) = iProver_top
% 3.56/0.96      | r2_hidden(X0,sK5) != iProver_top ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_1822,c_683]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_13,plain,
% 3.56/0.96      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.56/0.96      inference(cnf_transformation,[],[f66]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_2162,plain,
% 3.56/0.96      ( r2_hidden(X0,sK5) != iProver_top | r2_hidden(X0,sK4) = iProver_top ),
% 3.56/0.96      inference(demodulation,[status(thm)],[c_2161,c_13]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_3153,plain,
% 3.56/0.96      ( k3_xboole_0(sK5,X0) = sK5 | r2_hidden(sK0(sK5,X0),sK4) = iProver_top ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_671,c_2162]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_1,plain,
% 3.56/0.96      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.56/0.96      inference(cnf_transformation,[],[f47]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_238,plain,
% 3.56/0.96      ( ~ r2_hidden(sK0(X0,X1),X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.56/0.96      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_670,plain,
% 3.56/0.96      ( k3_xboole_0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 3.56/0.96      inference(predicate_to_equality,[status(thm)],[c_238]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_3494,plain,
% 3.56/0.96      ( k3_xboole_0(sK5,sK4) = sK5 ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_3153,c_670]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_0,plain,
% 3.56/0.96      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.56/0.96      inference(cnf_transformation,[],[f45]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_3916,plain,
% 3.56/0.96      ( k3_xboole_0(sK4,sK5) = sK5 ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_3494,c_0]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_19,plain,
% 3.56/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.96      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.56/0.96      inference(cnf_transformation,[],[f87]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_676,plain,
% 3.56/0.96      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.56/0.96      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.56/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_1612,plain,
% 3.56/0.96      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_672,c_676]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_4042,plain,
% 3.56/0.96      ( k3_subset_1(sK4,sK5) = k5_xboole_0(sK4,sK5) ),
% 3.56/0.96      inference(demodulation,[status(thm)],[c_3916,c_1612]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_6,plain,
% 3.56/0.96      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.56/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_5,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.56/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_1819,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k3_subset_1(sK4,sK5))) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4)) ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_1612,c_5]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_20,plain,
% 3.56/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.96      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.56/0.96      inference(cnf_transformation,[],[f73]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_675,plain,
% 3.56/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.56/0.96      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.56/0.96      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_22,plain,
% 3.56/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.56/0.96      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 3.56/0.96      inference(cnf_transformation,[],[f88]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_673,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.56/0.96      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.56/0.96      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.56/0.96      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_976,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0)) = k4_subset_1(sK4,sK5,X0)
% 3.56/0.96      | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_672,c_673]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_1340,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k3_subset_1(sK4,X0))) = k4_subset_1(sK4,sK5,k3_subset_1(sK4,X0))
% 3.56/0.96      | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_675,c_976]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_1349,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k3_subset_1(sK4,sK5))) = k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_672,c_1340]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_1820,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4)) = k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
% 3.56/0.96      inference(light_normalisation,[status(thm)],[c_1819,c_1349]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_1910,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_6,c_1820]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_4285,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) ),
% 3.56/0.96      inference(demodulation,[status(thm)],[c_4042,c_1910]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_3,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
% 3.56/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_933,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))) = X0 ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_3914,plain,
% 3.56/0.96      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
% 3.56/0.96      inference(superposition,[status(thm)],[c_3494,c_933]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_4290,plain,
% 3.56/0.96      ( k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) = sK4 ),
% 3.56/0.96      inference(light_normalisation,[status(thm)],[c_4285,c_3914]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_23,negated_conjecture,
% 3.56/0.96      ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
% 3.56/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_18,plain,
% 3.56/0.96      ( k2_subset_1(X0) = X0 ),
% 3.56/0.96      inference(cnf_transformation,[],[f71]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_687,plain,
% 3.56/0.96      ( k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) != sK4 ),
% 3.56/0.96      inference(demodulation,[status(thm)],[c_23,c_18]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_4289,plain,
% 3.56/0.96      ( k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) != sK4 ),
% 3.56/0.96      inference(demodulation,[status(thm)],[c_4042,c_687]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_4293,plain,
% 3.56/0.96      ( sK4 != sK4 ),
% 3.56/0.96      inference(demodulation,[status(thm)],[c_4290,c_4289]) ).
% 3.56/0.96  
% 3.56/0.96  cnf(c_4294,plain,
% 3.56/0.96      ( $false ),
% 3.56/0.96      inference(equality_resolution_simp,[status(thm)],[c_4293]) ).
% 3.56/0.96  
% 3.56/0.96  
% 3.56/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/0.96  
% 3.56/0.96  ------                               Statistics
% 3.56/0.96  
% 3.56/0.96  ------ General
% 3.56/0.96  
% 3.56/0.96  abstr_ref_over_cycles:                  0
% 3.56/0.96  abstr_ref_under_cycles:                 0
% 3.56/0.96  gc_basic_clause_elim:                   0
% 3.56/0.96  forced_gc_time:                         0
% 3.56/0.96  parsing_time:                           0.013
% 3.56/0.96  unif_index_cands_time:                  0.
% 3.56/0.96  unif_index_add_time:                    0.
% 3.56/0.96  orderings_time:                         0.
% 3.56/0.96  out_proof_time:                         0.01
% 3.56/0.96  total_time:                             0.241
% 3.56/0.96  num_of_symbols:                         49
% 3.56/0.96  num_of_terms:                           6197
% 3.56/0.96  
% 3.56/0.96  ------ Preprocessing
% 3.56/0.96  
% 3.56/0.96  num_of_splits:                          0
% 3.56/0.96  num_of_split_atoms:                     0
% 3.56/0.96  num_of_reused_defs:                     0
% 3.56/0.96  num_eq_ax_congr_red:                    56
% 3.56/0.96  num_of_sem_filtered_clauses:            1
% 3.56/0.96  num_of_subtypes:                        0
% 3.56/0.96  monotx_restored_types:                  0
% 3.56/0.96  sat_num_of_epr_types:                   0
% 3.56/0.96  sat_num_of_non_cyclic_types:            0
% 3.56/0.96  sat_guarded_non_collapsed_types:        0
% 3.56/0.96  num_pure_diseq_elim:                    0
% 3.56/0.96  simp_replaced_by:                       0
% 3.56/0.96  res_preprocessed:                       122
% 3.56/0.96  prep_upred:                             0
% 3.56/0.96  prep_unflattend:                        0
% 3.56/0.96  smt_new_axioms:                         0
% 3.56/0.96  pred_elim_cands:                        3
% 3.56/0.96  pred_elim:                              1
% 3.56/0.96  pred_elim_cl:                           1
% 3.56/0.96  pred_elim_cycles:                       3
% 3.56/0.96  merged_defs:                            0
% 3.56/0.96  merged_defs_ncl:                        0
% 3.56/0.96  bin_hyper_res:                          0
% 3.56/0.96  prep_cycles:                            4
% 3.56/0.96  pred_elim_time:                         0.001
% 3.56/0.96  splitting_time:                         0.
% 3.56/0.96  sem_filter_time:                        0.
% 3.56/0.96  monotx_time:                            0.
% 3.56/0.96  subtype_inf_time:                       0.
% 3.56/0.96  
% 3.56/0.96  ------ Problem properties
% 3.56/0.96  
% 3.56/0.96  clauses:                                24
% 3.56/0.96  conjectures:                            2
% 3.56/0.96  epr:                                    4
% 3.56/0.96  horn:                                   19
% 3.56/0.96  ground:                                 2
% 3.56/0.96  unary:                                  9
% 3.56/0.96  binary:                                 6
% 3.56/0.96  lits:                                   49
% 3.56/0.96  lits_eq:                                14
% 3.56/0.96  fd_pure:                                0
% 3.56/0.96  fd_pseudo:                              0
% 3.56/0.96  fd_cond:                                0
% 3.56/0.96  fd_pseudo_cond:                         3
% 3.56/0.96  ac_symbols:                             0
% 3.56/0.96  
% 3.56/0.96  ------ Propositional Solver
% 3.56/0.96  
% 3.56/0.96  prop_solver_calls:                      32
% 3.56/0.96  prop_fast_solver_calls:                 648
% 3.56/0.96  smt_solver_calls:                       0
% 3.56/0.96  smt_fast_solver_calls:                  0
% 3.56/0.96  prop_num_of_clauses:                    1804
% 3.56/0.96  prop_preprocess_simplified:             5774
% 3.56/0.96  prop_fo_subsumed:                       1
% 3.56/0.96  prop_solver_time:                       0.
% 3.56/0.96  smt_solver_time:                        0.
% 3.56/0.96  smt_fast_solver_time:                   0.
% 3.56/0.96  prop_fast_solver_time:                  0.
% 3.56/0.96  prop_unsat_core_time:                   0.
% 3.56/0.96  
% 3.56/0.96  ------ QBF
% 3.56/0.96  
% 3.56/0.96  qbf_q_res:                              0
% 3.56/0.96  qbf_num_tautologies:                    0
% 3.56/0.96  qbf_prep_cycles:                        0
% 3.56/0.96  
% 3.56/0.96  ------ BMC1
% 3.56/0.96  
% 3.56/0.96  bmc1_current_bound:                     -1
% 3.56/0.96  bmc1_last_solved_bound:                 -1
% 3.56/0.96  bmc1_unsat_core_size:                   -1
% 3.56/0.96  bmc1_unsat_core_parents_size:           -1
% 3.56/0.96  bmc1_merge_next_fun:                    0
% 3.56/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.56/0.96  
% 3.56/0.96  ------ Instantiation
% 3.56/0.96  
% 3.56/0.96  inst_num_of_clauses:                    745
% 3.56/0.96  inst_num_in_passive:                    433
% 3.56/0.96  inst_num_in_active:                     231
% 3.56/0.96  inst_num_in_unprocessed:                81
% 3.56/0.96  inst_num_of_loops:                      330
% 3.56/0.96  inst_num_of_learning_restarts:          0
% 3.56/0.96  inst_num_moves_active_passive:          94
% 3.56/0.96  inst_lit_activity:                      0
% 3.56/0.96  inst_lit_activity_moves:                0
% 3.56/0.96  inst_num_tautologies:                   0
% 3.56/0.96  inst_num_prop_implied:                  0
% 3.56/0.96  inst_num_existing_simplified:           0
% 3.56/0.96  inst_num_eq_res_simplified:             0
% 3.56/0.96  inst_num_child_elim:                    0
% 3.56/0.96  inst_num_of_dismatching_blockings:      349
% 3.56/0.96  inst_num_of_non_proper_insts:           872
% 3.56/0.96  inst_num_of_duplicates:                 0
% 3.56/0.96  inst_inst_num_from_inst_to_res:         0
% 3.56/0.96  inst_dismatching_checking_time:         0.
% 3.56/0.96  
% 3.56/0.96  ------ Resolution
% 3.56/0.96  
% 3.56/0.96  res_num_of_clauses:                     0
% 3.56/0.96  res_num_in_passive:                     0
% 3.56/0.96  res_num_in_active:                      0
% 3.56/0.96  res_num_of_loops:                       126
% 3.56/0.96  res_forward_subset_subsumed:            201
% 3.56/0.96  res_backward_subset_subsumed:           0
% 3.56/0.96  res_forward_subsumed:                   0
% 3.56/0.96  res_backward_subsumed:                  0
% 3.56/0.96  res_forward_subsumption_resolution:     0
% 3.56/0.96  res_backward_subsumption_resolution:    0
% 3.56/0.96  res_clause_to_clause_subsumption:       304
% 3.56/0.96  res_orphan_elimination:                 0
% 3.56/0.96  res_tautology_del:                      71
% 3.56/0.96  res_num_eq_res_simplified:              0
% 3.56/0.96  res_num_sel_changes:                    0
% 3.56/0.96  res_moves_from_active_to_pass:          0
% 3.56/0.96  
% 3.56/0.96  ------ Superposition
% 3.56/0.96  
% 3.56/0.96  sup_time_total:                         0.
% 3.56/0.96  sup_time_generating:                    0.
% 3.56/0.96  sup_time_sim_full:                      0.
% 3.56/0.96  sup_time_sim_immed:                     0.
% 3.56/0.96  
% 3.56/0.96  sup_num_of_clauses:                     87
% 3.56/0.96  sup_num_in_active:                      45
% 3.56/0.96  sup_num_in_passive:                     42
% 3.56/0.96  sup_num_of_loops:                       64
% 3.56/0.96  sup_fw_superposition:                   62
% 3.56/0.96  sup_bw_superposition:                   54
% 3.56/0.96  sup_immediate_simplified:               23
% 3.56/0.96  sup_given_eliminated:                   0
% 3.56/0.96  comparisons_done:                       0
% 3.56/0.96  comparisons_avoided:                    0
% 3.56/0.96  
% 3.56/0.96  ------ Simplifications
% 3.56/0.96  
% 3.56/0.96  
% 3.56/0.96  sim_fw_subset_subsumed:                 5
% 3.56/0.96  sim_bw_subset_subsumed:                 0
% 3.56/0.96  sim_fw_subsumed:                        12
% 3.56/0.96  sim_bw_subsumed:                        0
% 3.56/0.96  sim_fw_subsumption_res:                 0
% 3.56/0.96  sim_bw_subsumption_res:                 0
% 3.56/0.96  sim_tautology_del:                      2
% 3.56/0.96  sim_eq_tautology_del:                   0
% 3.56/0.96  sim_eq_res_simp:                        0
% 3.56/0.96  sim_fw_demodulated:                     3
% 3.56/0.96  sim_bw_demodulated:                     22
% 3.56/0.96  sim_light_normalised:                   5
% 3.56/0.96  sim_joinable_taut:                      0
% 3.56/0.96  sim_joinable_simp:                      0
% 3.56/0.96  sim_ac_normalised:                      0
% 3.56/0.96  sim_smt_subsumption:                    0
% 3.56/0.96  
%------------------------------------------------------------------------------
