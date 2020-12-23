%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:29 EST 2020

% Result     : Theorem 7.39s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 410 expanded)
%              Number of clauses        :   72 ( 128 expanded)
%              Number of leaves         :   24 ( 105 expanded)
%              Depth                    :   16
%              Number of atoms          :  343 ( 859 expanded)
%              Number of equality atoms :  183 ( 448 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f43,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f61,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK5) != k4_subset_1(sK5,sK6,k2_subset_1(sK5))
      & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( k2_subset_1(sK5) != k4_subset_1(sK5,sK6,k2_subset_1(sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f61])).

fof(f104,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f130,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f76,f106])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f75,f107])).

fof(f109,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f108])).

fof(f110,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f109])).

fof(f111,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f83,f110])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f111])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f98,f111])).

fof(f105,plain,(
    k2_subset_1(sK5) != k4_subset_1(sK5,sK6,k2_subset_1(sK5)) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f26,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f125,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f100,f64])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK4(X0,X1,X2),X2)
            & r2_hidden(sK4(X0,X1,X2),X1)
            & m1_subset_1(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f59])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f115,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f67,f64])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_923,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_934,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2557,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(sK5)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_934])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_940,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6640,plain,
    ( r1_tarski(sK6,sK5) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2557,c_940])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_949,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6925,plain,
    ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK5)) = sK5
    | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6640,c_949])).

cnf(c_22,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_933,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_964,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_933,c_21])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_929,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2514,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_929])).

cnf(c_12455,plain,
    ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK5)) = k4_subset_1(sK5,sK6,sK5) ),
    inference(superposition,[status(thm)],[c_923,c_2514])).

cnf(c_16752,plain,
    ( k4_subset_1(sK5,sK6,sK5) = sK5
    | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6925,c_12455])).

cnf(c_32,negated_conjecture,
    ( k2_subset_1(sK5) != k4_subset_1(sK5,sK6,k2_subset_1(sK5)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_969,plain,
    ( k4_subset_1(sK5,sK6,sK5) != sK5 ),
    inference(demodulation,[status(thm)],[c_32,c_21])).

cnf(c_16755,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16752,c_969])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_936,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2741,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_936])).

cnf(c_16760,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_16755,c_2741])).

cnf(c_28,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_927,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2511,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,o_0_0_xboole_0)) = k4_subset_1(X1,X0,o_0_0_xboole_0)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_929])).

cnf(c_10175,plain,
    ( k3_tarski(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) = k4_subset_1(X0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_927,c_2511])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK4(X1,X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_925,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK4(X1,X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_926,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X0) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1638,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_925,c_926])).

cnf(c_4440,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_1638])).

cnf(c_4682,plain,
    ( k3_tarski(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_4440,c_949])).

cnf(c_10487,plain,
    ( k4_subset_1(X0,o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10175,c_4682])).

cnf(c_10510,plain,
    ( k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10487])).

cnf(c_331,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1354,plain,
    ( X0 != X1
    | k2_subset_1(sK5) != X1
    | k2_subset_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_8902,plain,
    ( k4_subset_1(X0,X1,X2) != X3
    | k2_subset_1(sK5) != X3
    | k2_subset_1(sK5) = k4_subset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_8903,plain,
    ( k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | k2_subset_1(sK5) = k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | k2_subset_1(sK5) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8902])).

cnf(c_2642,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_5437,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2642])).

cnf(c_5438,plain,
    ( sK6 != sK6
    | sK6 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_5437])).

cnf(c_1583,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_4981,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_4982,plain,
    ( sK5 != sK5
    | sK5 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_4981])).

cnf(c_2740,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK5)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_936])).

cnf(c_330,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2504,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2421,plain,
    ( ~ v1_xboole_0(sK5)
    | o_0_0_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2422,plain,
    ( o_0_0_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2421])).

cnf(c_342,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_2379,plain,
    ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k4_subset_1(X0,X1,X2)
    | k2_subset_1(sK5) != X2
    | sK6 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_2381,plain,
    ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | k2_subset_1(sK5) != o_0_0_xboole_0
    | sK6 != o_0_0_xboole_0
    | sK5 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2379])).

cnf(c_1527,plain,
    ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != X0
    | k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k2_subset_1(sK5)
    | k2_subset_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_2378,plain,
    ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != k4_subset_1(X0,X1,X2)
    | k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k2_subset_1(sK5)
    | k2_subset_1(sK5) != k4_subset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_1527])).

cnf(c_2380,plain,
    ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k2_subset_1(sK5)
    | k2_subset_1(sK5) != k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_2298,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_2278,plain,
    ( ~ v1_xboole_0(sK6)
    | o_0_0_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2281,plain,
    ( o_0_0_xboole_0 = sK6
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2278])).

cnf(c_1598,plain,
    ( X0 != sK5
    | k2_subset_1(sK5) = X0
    | k2_subset_1(sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1599,plain,
    ( k2_subset_1(sK5) != sK5
    | k2_subset_1(sK5) = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_1363,plain,
    ( k2_subset_1(sK5) = k2_subset_1(sK5) ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_1218,plain,
    ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != X0
    | k2_subset_1(sK5) != X0
    | k2_subset_1(sK5) = k4_subset_1(sK5,sK6,k2_subset_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_1362,plain,
    ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != k2_subset_1(sK5)
    | k2_subset_1(sK5) = k4_subset_1(sK5,sK6,k2_subset_1(sK5))
    | k2_subset_1(sK5) != k2_subset_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1361,plain,
    ( k2_subset_1(sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16760,c_16755,c_10510,c_8903,c_5438,c_4982,c_2740,c_2504,c_2422,c_2381,c_2380,c_2298,c_2281,c_1599,c_1363,c_1362,c_1361,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:58:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.39/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/1.48  
% 7.39/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.39/1.48  
% 7.39/1.48  ------  iProver source info
% 7.39/1.48  
% 7.39/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.39/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.39/1.48  git: non_committed_changes: false
% 7.39/1.48  git: last_make_outside_of_git: false
% 7.39/1.48  
% 7.39/1.48  ------ 
% 7.39/1.48  
% 7.39/1.48  ------ Input Options
% 7.39/1.48  
% 7.39/1.48  --out_options                           all
% 7.39/1.48  --tptp_safe_out                         true
% 7.39/1.48  --problem_path                          ""
% 7.39/1.48  --include_path                          ""
% 7.39/1.48  --clausifier                            res/vclausify_rel
% 7.39/1.48  --clausifier_options                    --mode clausify
% 7.39/1.48  --stdin                                 false
% 7.39/1.48  --stats_out                             sel
% 7.39/1.48  
% 7.39/1.48  ------ General Options
% 7.39/1.48  
% 7.39/1.48  --fof                                   false
% 7.39/1.48  --time_out_real                         604.99
% 7.39/1.48  --time_out_virtual                      -1.
% 7.39/1.48  --symbol_type_check                     false
% 7.39/1.48  --clausify_out                          false
% 7.39/1.48  --sig_cnt_out                           false
% 7.39/1.48  --trig_cnt_out                          false
% 7.39/1.48  --trig_cnt_out_tolerance                1.
% 7.39/1.48  --trig_cnt_out_sk_spl                   false
% 7.39/1.48  --abstr_cl_out                          false
% 7.39/1.48  
% 7.39/1.48  ------ Global Options
% 7.39/1.48  
% 7.39/1.48  --schedule                              none
% 7.39/1.48  --add_important_lit                     false
% 7.39/1.48  --prop_solver_per_cl                    1000
% 7.39/1.48  --min_unsat_core                        false
% 7.39/1.48  --soft_assumptions                      false
% 7.39/1.48  --soft_lemma_size                       3
% 7.39/1.48  --prop_impl_unit_size                   0
% 7.39/1.48  --prop_impl_unit                        []
% 7.39/1.48  --share_sel_clauses                     true
% 7.39/1.48  --reset_solvers                         false
% 7.39/1.48  --bc_imp_inh                            [conj_cone]
% 7.39/1.48  --conj_cone_tolerance                   3.
% 7.39/1.48  --extra_neg_conj                        none
% 7.39/1.48  --large_theory_mode                     true
% 7.39/1.48  --prolific_symb_bound                   200
% 7.39/1.48  --lt_threshold                          2000
% 7.39/1.48  --clause_weak_htbl                      true
% 7.39/1.48  --gc_record_bc_elim                     false
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing Options
% 7.39/1.48  
% 7.39/1.48  --preprocessing_flag                    true
% 7.39/1.48  --time_out_prep_mult                    0.1
% 7.39/1.48  --splitting_mode                        input
% 7.39/1.48  --splitting_grd                         true
% 7.39/1.48  --splitting_cvd                         false
% 7.39/1.48  --splitting_cvd_svl                     false
% 7.39/1.48  --splitting_nvd                         32
% 7.39/1.48  --sub_typing                            true
% 7.39/1.48  --prep_gs_sim                           false
% 7.39/1.48  --prep_unflatten                        true
% 7.39/1.48  --prep_res_sim                          true
% 7.39/1.48  --prep_upred                            true
% 7.39/1.48  --prep_sem_filter                       exhaustive
% 7.39/1.48  --prep_sem_filter_out                   false
% 7.39/1.48  --pred_elim                             false
% 7.39/1.48  --res_sim_input                         true
% 7.39/1.48  --eq_ax_congr_red                       true
% 7.39/1.48  --pure_diseq_elim                       true
% 7.39/1.48  --brand_transform                       false
% 7.39/1.48  --non_eq_to_eq                          false
% 7.39/1.48  --prep_def_merge                        true
% 7.39/1.48  --prep_def_merge_prop_impl              false
% 7.39/1.48  --prep_def_merge_mbd                    true
% 7.39/1.48  --prep_def_merge_tr_red                 false
% 7.39/1.48  --prep_def_merge_tr_cl                  false
% 7.39/1.48  --smt_preprocessing                     true
% 7.39/1.48  --smt_ac_axioms                         fast
% 7.39/1.48  --preprocessed_out                      false
% 7.39/1.48  --preprocessed_stats                    false
% 7.39/1.48  
% 7.39/1.48  ------ Abstraction refinement Options
% 7.39/1.48  
% 7.39/1.48  --abstr_ref                             []
% 7.39/1.48  --abstr_ref_prep                        false
% 7.39/1.48  --abstr_ref_until_sat                   false
% 7.39/1.48  --abstr_ref_sig_restrict                funpre
% 7.39/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.39/1.48  --abstr_ref_under                       []
% 7.39/1.48  
% 7.39/1.48  ------ SAT Options
% 7.39/1.48  
% 7.39/1.48  --sat_mode                              false
% 7.39/1.48  --sat_fm_restart_options                ""
% 7.39/1.48  --sat_gr_def                            false
% 7.39/1.48  --sat_epr_types                         true
% 7.39/1.48  --sat_non_cyclic_types                  false
% 7.39/1.48  --sat_finite_models                     false
% 7.39/1.48  --sat_fm_lemmas                         false
% 7.39/1.48  --sat_fm_prep                           false
% 7.39/1.48  --sat_fm_uc_incr                        true
% 7.39/1.48  --sat_out_model                         small
% 7.39/1.48  --sat_out_clauses                       false
% 7.39/1.48  
% 7.39/1.48  ------ QBF Options
% 7.39/1.48  
% 7.39/1.48  --qbf_mode                              false
% 7.39/1.48  --qbf_elim_univ                         false
% 7.39/1.48  --qbf_dom_inst                          none
% 7.39/1.48  --qbf_dom_pre_inst                      false
% 7.39/1.48  --qbf_sk_in                             false
% 7.39/1.48  --qbf_pred_elim                         true
% 7.39/1.48  --qbf_split                             512
% 7.39/1.48  
% 7.39/1.48  ------ BMC1 Options
% 7.39/1.48  
% 7.39/1.48  --bmc1_incremental                      false
% 7.39/1.48  --bmc1_axioms                           reachable_all
% 7.39/1.48  --bmc1_min_bound                        0
% 7.39/1.48  --bmc1_max_bound                        -1
% 7.39/1.48  --bmc1_max_bound_default                -1
% 7.39/1.48  --bmc1_symbol_reachability              true
% 7.39/1.48  --bmc1_property_lemmas                  false
% 7.39/1.48  --bmc1_k_induction                      false
% 7.39/1.48  --bmc1_non_equiv_states                 false
% 7.39/1.48  --bmc1_deadlock                         false
% 7.39/1.48  --bmc1_ucm                              false
% 7.39/1.48  --bmc1_add_unsat_core                   none
% 7.39/1.48  --bmc1_unsat_core_children              false
% 7.39/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.39/1.48  --bmc1_out_stat                         full
% 7.39/1.48  --bmc1_ground_init                      false
% 7.39/1.48  --bmc1_pre_inst_next_state              false
% 7.39/1.48  --bmc1_pre_inst_state                   false
% 7.39/1.48  --bmc1_pre_inst_reach_state             false
% 7.39/1.48  --bmc1_out_unsat_core                   false
% 7.39/1.48  --bmc1_aig_witness_out                  false
% 7.39/1.48  --bmc1_verbose                          false
% 7.39/1.48  --bmc1_dump_clauses_tptp                false
% 7.39/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.39/1.48  --bmc1_dump_file                        -
% 7.39/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.39/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.39/1.48  --bmc1_ucm_extend_mode                  1
% 7.39/1.48  --bmc1_ucm_init_mode                    2
% 7.39/1.48  --bmc1_ucm_cone_mode                    none
% 7.39/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.39/1.48  --bmc1_ucm_relax_model                  4
% 7.39/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.39/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.39/1.48  --bmc1_ucm_layered_model                none
% 7.39/1.48  --bmc1_ucm_max_lemma_size               10
% 7.39/1.48  
% 7.39/1.48  ------ AIG Options
% 7.39/1.48  
% 7.39/1.48  --aig_mode                              false
% 7.39/1.48  
% 7.39/1.48  ------ Instantiation Options
% 7.39/1.48  
% 7.39/1.48  --instantiation_flag                    true
% 7.39/1.48  --inst_sos_flag                         false
% 7.39/1.48  --inst_sos_phase                        true
% 7.39/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.39/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.39/1.48  --inst_lit_sel_side                     num_symb
% 7.39/1.48  --inst_solver_per_active                1400
% 7.39/1.48  --inst_solver_calls_frac                1.
% 7.39/1.48  --inst_passive_queue_type               priority_queues
% 7.39/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.39/1.48  --inst_passive_queues_freq              [25;2]
% 7.39/1.48  --inst_dismatching                      true
% 7.39/1.48  --inst_eager_unprocessed_to_passive     true
% 7.39/1.48  --inst_prop_sim_given                   true
% 7.39/1.48  --inst_prop_sim_new                     false
% 7.39/1.48  --inst_subs_new                         false
% 7.39/1.48  --inst_eq_res_simp                      false
% 7.39/1.48  --inst_subs_given                       false
% 7.39/1.48  --inst_orphan_elimination               true
% 7.39/1.48  --inst_learning_loop_flag               true
% 7.39/1.48  --inst_learning_start                   3000
% 7.39/1.48  --inst_learning_factor                  2
% 7.39/1.48  --inst_start_prop_sim_after_learn       3
% 7.39/1.48  --inst_sel_renew                        solver
% 7.39/1.48  --inst_lit_activity_flag                true
% 7.39/1.48  --inst_restr_to_given                   false
% 7.39/1.48  --inst_activity_threshold               500
% 7.39/1.48  --inst_out_proof                        true
% 7.39/1.48  
% 7.39/1.48  ------ Resolution Options
% 7.39/1.48  
% 7.39/1.48  --resolution_flag                       true
% 7.39/1.48  --res_lit_sel                           adaptive
% 7.39/1.48  --res_lit_sel_side                      none
% 7.39/1.48  --res_ordering                          kbo
% 7.39/1.48  --res_to_prop_solver                    active
% 7.39/1.48  --res_prop_simpl_new                    false
% 7.39/1.48  --res_prop_simpl_given                  true
% 7.39/1.48  --res_passive_queue_type                priority_queues
% 7.39/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.39/1.48  --res_passive_queues_freq               [15;5]
% 7.39/1.48  --res_forward_subs                      full
% 7.39/1.48  --res_backward_subs                     full
% 7.39/1.48  --res_forward_subs_resolution           true
% 7.39/1.48  --res_backward_subs_resolution          true
% 7.39/1.48  --res_orphan_elimination                true
% 7.39/1.48  --res_time_limit                        2.
% 7.39/1.48  --res_out_proof                         true
% 7.39/1.48  
% 7.39/1.48  ------ Superposition Options
% 7.39/1.48  
% 7.39/1.48  --superposition_flag                    true
% 7.39/1.48  --sup_passive_queue_type                priority_queues
% 7.39/1.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.39/1.48  --sup_passive_queues_freq               [1;4]
% 7.39/1.48  --demod_completeness_check              fast
% 7.39/1.48  --demod_use_ground                      true
% 7.39/1.48  --sup_to_prop_solver                    passive
% 7.39/1.48  --sup_prop_simpl_new                    true
% 7.39/1.48  --sup_prop_simpl_given                  true
% 7.39/1.48  --sup_fun_splitting                     false
% 7.39/1.48  --sup_smt_interval                      50000
% 7.39/1.48  
% 7.39/1.48  ------ Superposition Simplification Setup
% 7.39/1.48  
% 7.39/1.48  --sup_indices_passive                   []
% 7.39/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.39/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.48  --sup_full_bw                           [BwDemod]
% 7.39/1.48  --sup_immed_triv                        [TrivRules]
% 7.39/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.48  --sup_immed_bw_main                     []
% 7.39/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.39/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.39/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.39/1.48  
% 7.39/1.48  ------ Combination Options
% 7.39/1.48  
% 7.39/1.48  --comb_res_mult                         3
% 7.39/1.48  --comb_sup_mult                         2
% 7.39/1.48  --comb_inst_mult                        10
% 7.39/1.48  
% 7.39/1.48  ------ Debug Options
% 7.39/1.48  
% 7.39/1.48  --dbg_backtrace                         false
% 7.39/1.48  --dbg_dump_prop_clauses                 false
% 7.39/1.48  --dbg_dump_prop_clauses_file            -
% 7.39/1.48  --dbg_out_stat                          false
% 7.39/1.48  ------ Parsing...
% 7.39/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.48  ------ Proving...
% 7.39/1.48  ------ Problem Properties 
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  clauses                                 34
% 7.39/1.48  conjectures                             2
% 7.39/1.48  EPR                                     5
% 7.39/1.48  Horn                                    27
% 7.39/1.48  unary                                   11
% 7.39/1.48  binary                                  7
% 7.39/1.48  lits                                    76
% 7.39/1.48  lits eq                                 21
% 7.39/1.48  fd_pure                                 0
% 7.39/1.48  fd_pseudo                               0
% 7.39/1.48  fd_cond                                 2
% 7.39/1.48  fd_pseudo_cond                          4
% 7.39/1.48  AC symbols                              0
% 7.39/1.48  
% 7.39/1.48  ------ Input Options Time Limit: Unbounded
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  ------ 
% 7.39/1.48  Current options:
% 7.39/1.48  ------ 
% 7.39/1.48  
% 7.39/1.48  ------ Input Options
% 7.39/1.48  
% 7.39/1.48  --out_options                           all
% 7.39/1.48  --tptp_safe_out                         true
% 7.39/1.48  --problem_path                          ""
% 7.39/1.48  --include_path                          ""
% 7.39/1.48  --clausifier                            res/vclausify_rel
% 7.39/1.48  --clausifier_options                    --mode clausify
% 7.39/1.48  --stdin                                 false
% 7.39/1.48  --stats_out                             sel
% 7.39/1.48  
% 7.39/1.48  ------ General Options
% 7.39/1.48  
% 7.39/1.48  --fof                                   false
% 7.39/1.48  --time_out_real                         604.99
% 7.39/1.48  --time_out_virtual                      -1.
% 7.39/1.48  --symbol_type_check                     false
% 7.39/1.48  --clausify_out                          false
% 7.39/1.48  --sig_cnt_out                           false
% 7.39/1.48  --trig_cnt_out                          false
% 7.39/1.48  --trig_cnt_out_tolerance                1.
% 7.39/1.48  --trig_cnt_out_sk_spl                   false
% 7.39/1.48  --abstr_cl_out                          false
% 7.39/1.48  
% 7.39/1.48  ------ Global Options
% 7.39/1.48  
% 7.39/1.48  --schedule                              none
% 7.39/1.48  --add_important_lit                     false
% 7.39/1.48  --prop_solver_per_cl                    1000
% 7.39/1.48  --min_unsat_core                        false
% 7.39/1.48  --soft_assumptions                      false
% 7.39/1.48  --soft_lemma_size                       3
% 7.39/1.48  --prop_impl_unit_size                   0
% 7.39/1.48  --prop_impl_unit                        []
% 7.39/1.48  --share_sel_clauses                     true
% 7.39/1.48  --reset_solvers                         false
% 7.39/1.48  --bc_imp_inh                            [conj_cone]
% 7.39/1.48  --conj_cone_tolerance                   3.
% 7.39/1.48  --extra_neg_conj                        none
% 7.39/1.48  --large_theory_mode                     true
% 7.39/1.48  --prolific_symb_bound                   200
% 7.39/1.48  --lt_threshold                          2000
% 7.39/1.48  --clause_weak_htbl                      true
% 7.39/1.48  --gc_record_bc_elim                     false
% 7.39/1.48  
% 7.39/1.48  ------ Preprocessing Options
% 7.39/1.48  
% 7.39/1.48  --preprocessing_flag                    true
% 7.39/1.48  --time_out_prep_mult                    0.1
% 7.39/1.48  --splitting_mode                        input
% 7.39/1.48  --splitting_grd                         true
% 7.39/1.48  --splitting_cvd                         false
% 7.39/1.48  --splitting_cvd_svl                     false
% 7.39/1.48  --splitting_nvd                         32
% 7.39/1.48  --sub_typing                            true
% 7.39/1.48  --prep_gs_sim                           false
% 7.39/1.48  --prep_unflatten                        true
% 7.39/1.48  --prep_res_sim                          true
% 7.39/1.48  --prep_upred                            true
% 7.39/1.48  --prep_sem_filter                       exhaustive
% 7.39/1.48  --prep_sem_filter_out                   false
% 7.39/1.48  --pred_elim                             false
% 7.39/1.48  --res_sim_input                         true
% 7.39/1.48  --eq_ax_congr_red                       true
% 7.39/1.48  --pure_diseq_elim                       true
% 7.39/1.48  --brand_transform                       false
% 7.39/1.48  --non_eq_to_eq                          false
% 7.39/1.48  --prep_def_merge                        true
% 7.39/1.48  --prep_def_merge_prop_impl              false
% 7.39/1.48  --prep_def_merge_mbd                    true
% 7.39/1.48  --prep_def_merge_tr_red                 false
% 7.39/1.48  --prep_def_merge_tr_cl                  false
% 7.39/1.48  --smt_preprocessing                     true
% 7.39/1.48  --smt_ac_axioms                         fast
% 7.39/1.48  --preprocessed_out                      false
% 7.39/1.48  --preprocessed_stats                    false
% 7.39/1.48  
% 7.39/1.48  ------ Abstraction refinement Options
% 7.39/1.48  
% 7.39/1.48  --abstr_ref                             []
% 7.39/1.48  --abstr_ref_prep                        false
% 7.39/1.48  --abstr_ref_until_sat                   false
% 7.39/1.48  --abstr_ref_sig_restrict                funpre
% 7.39/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.39/1.48  --abstr_ref_under                       []
% 7.39/1.48  
% 7.39/1.48  ------ SAT Options
% 7.39/1.48  
% 7.39/1.48  --sat_mode                              false
% 7.39/1.48  --sat_fm_restart_options                ""
% 7.39/1.48  --sat_gr_def                            false
% 7.39/1.48  --sat_epr_types                         true
% 7.39/1.48  --sat_non_cyclic_types                  false
% 7.39/1.48  --sat_finite_models                     false
% 7.39/1.48  --sat_fm_lemmas                         false
% 7.39/1.48  --sat_fm_prep                           false
% 7.39/1.48  --sat_fm_uc_incr                        true
% 7.39/1.48  --sat_out_model                         small
% 7.39/1.48  --sat_out_clauses                       false
% 7.39/1.48  
% 7.39/1.48  ------ QBF Options
% 7.39/1.48  
% 7.39/1.48  --qbf_mode                              false
% 7.39/1.48  --qbf_elim_univ                         false
% 7.39/1.48  --qbf_dom_inst                          none
% 7.39/1.48  --qbf_dom_pre_inst                      false
% 7.39/1.48  --qbf_sk_in                             false
% 7.39/1.48  --qbf_pred_elim                         true
% 7.39/1.48  --qbf_split                             512
% 7.39/1.48  
% 7.39/1.48  ------ BMC1 Options
% 7.39/1.48  
% 7.39/1.48  --bmc1_incremental                      false
% 7.39/1.48  --bmc1_axioms                           reachable_all
% 7.39/1.48  --bmc1_min_bound                        0
% 7.39/1.48  --bmc1_max_bound                        -1
% 7.39/1.48  --bmc1_max_bound_default                -1
% 7.39/1.48  --bmc1_symbol_reachability              true
% 7.39/1.48  --bmc1_property_lemmas                  false
% 7.39/1.48  --bmc1_k_induction                      false
% 7.39/1.48  --bmc1_non_equiv_states                 false
% 7.39/1.48  --bmc1_deadlock                         false
% 7.39/1.48  --bmc1_ucm                              false
% 7.39/1.48  --bmc1_add_unsat_core                   none
% 7.39/1.48  --bmc1_unsat_core_children              false
% 7.39/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.39/1.48  --bmc1_out_stat                         full
% 7.39/1.48  --bmc1_ground_init                      false
% 7.39/1.48  --bmc1_pre_inst_next_state              false
% 7.39/1.48  --bmc1_pre_inst_state                   false
% 7.39/1.48  --bmc1_pre_inst_reach_state             false
% 7.39/1.48  --bmc1_out_unsat_core                   false
% 7.39/1.48  --bmc1_aig_witness_out                  false
% 7.39/1.48  --bmc1_verbose                          false
% 7.39/1.48  --bmc1_dump_clauses_tptp                false
% 7.39/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.39/1.48  --bmc1_dump_file                        -
% 7.39/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.39/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.39/1.48  --bmc1_ucm_extend_mode                  1
% 7.39/1.48  --bmc1_ucm_init_mode                    2
% 7.39/1.48  --bmc1_ucm_cone_mode                    none
% 7.39/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.39/1.48  --bmc1_ucm_relax_model                  4
% 7.39/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.39/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.39/1.48  --bmc1_ucm_layered_model                none
% 7.39/1.48  --bmc1_ucm_max_lemma_size               10
% 7.39/1.48  
% 7.39/1.48  ------ AIG Options
% 7.39/1.48  
% 7.39/1.48  --aig_mode                              false
% 7.39/1.48  
% 7.39/1.48  ------ Instantiation Options
% 7.39/1.48  
% 7.39/1.48  --instantiation_flag                    true
% 7.39/1.48  --inst_sos_flag                         false
% 7.39/1.48  --inst_sos_phase                        true
% 7.39/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.39/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.39/1.48  --inst_lit_sel_side                     num_symb
% 7.39/1.48  --inst_solver_per_active                1400
% 7.39/1.48  --inst_solver_calls_frac                1.
% 7.39/1.48  --inst_passive_queue_type               priority_queues
% 7.39/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.39/1.48  --inst_passive_queues_freq              [25;2]
% 7.39/1.48  --inst_dismatching                      true
% 7.39/1.48  --inst_eager_unprocessed_to_passive     true
% 7.39/1.48  --inst_prop_sim_given                   true
% 7.39/1.48  --inst_prop_sim_new                     false
% 7.39/1.48  --inst_subs_new                         false
% 7.39/1.48  --inst_eq_res_simp                      false
% 7.39/1.48  --inst_subs_given                       false
% 7.39/1.48  --inst_orphan_elimination               true
% 7.39/1.48  --inst_learning_loop_flag               true
% 7.39/1.48  --inst_learning_start                   3000
% 7.39/1.48  --inst_learning_factor                  2
% 7.39/1.48  --inst_start_prop_sim_after_learn       3
% 7.39/1.48  --inst_sel_renew                        solver
% 7.39/1.48  --inst_lit_activity_flag                true
% 7.39/1.48  --inst_restr_to_given                   false
% 7.39/1.48  --inst_activity_threshold               500
% 7.39/1.48  --inst_out_proof                        true
% 7.39/1.48  
% 7.39/1.48  ------ Resolution Options
% 7.39/1.48  
% 7.39/1.48  --resolution_flag                       true
% 7.39/1.48  --res_lit_sel                           adaptive
% 7.39/1.48  --res_lit_sel_side                      none
% 7.39/1.48  --res_ordering                          kbo
% 7.39/1.48  --res_to_prop_solver                    active
% 7.39/1.48  --res_prop_simpl_new                    false
% 7.39/1.48  --res_prop_simpl_given                  true
% 7.39/1.48  --res_passive_queue_type                priority_queues
% 7.39/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.39/1.48  --res_passive_queues_freq               [15;5]
% 7.39/1.48  --res_forward_subs                      full
% 7.39/1.48  --res_backward_subs                     full
% 7.39/1.48  --res_forward_subs_resolution           true
% 7.39/1.48  --res_backward_subs_resolution          true
% 7.39/1.48  --res_orphan_elimination                true
% 7.39/1.48  --res_time_limit                        2.
% 7.39/1.48  --res_out_proof                         true
% 7.39/1.48  
% 7.39/1.48  ------ Superposition Options
% 7.39/1.48  
% 7.39/1.48  --superposition_flag                    true
% 7.39/1.48  --sup_passive_queue_type                priority_queues
% 7.39/1.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.39/1.48  --sup_passive_queues_freq               [1;4]
% 7.39/1.48  --demod_completeness_check              fast
% 7.39/1.48  --demod_use_ground                      true
% 7.39/1.48  --sup_to_prop_solver                    passive
% 7.39/1.48  --sup_prop_simpl_new                    true
% 7.39/1.48  --sup_prop_simpl_given                  true
% 7.39/1.48  --sup_fun_splitting                     false
% 7.39/1.48  --sup_smt_interval                      50000
% 7.39/1.48  
% 7.39/1.48  ------ Superposition Simplification Setup
% 7.39/1.48  
% 7.39/1.48  --sup_indices_passive                   []
% 7.39/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.39/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.48  --sup_full_bw                           [BwDemod]
% 7.39/1.48  --sup_immed_triv                        [TrivRules]
% 7.39/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.48  --sup_immed_bw_main                     []
% 7.39/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.39/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.39/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.39/1.48  
% 7.39/1.48  ------ Combination Options
% 7.39/1.48  
% 7.39/1.48  --comb_res_mult                         3
% 7.39/1.48  --comb_sup_mult                         2
% 7.39/1.48  --comb_inst_mult                        10
% 7.39/1.48  
% 7.39/1.48  ------ Debug Options
% 7.39/1.48  
% 7.39/1.48  --dbg_backtrace                         false
% 7.39/1.48  --dbg_dump_prop_clauses                 false
% 7.39/1.48  --dbg_dump_prop_clauses_file            -
% 7.39/1.48  --dbg_out_stat                          false
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  ------ Proving...
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  % SZS status Theorem for theBenchmark.p
% 7.39/1.48  
% 7.39/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.39/1.48  
% 7.39/1.48  fof(f28,conjecture,(
% 7.39/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f29,negated_conjecture,(
% 7.39/1.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 7.39/1.48    inference(negated_conjecture,[],[f28])).
% 7.39/1.48  
% 7.39/1.48  fof(f43,plain,(
% 7.39/1.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.39/1.48    inference(ennf_transformation,[],[f29])).
% 7.39/1.48  
% 7.39/1.48  fof(f61,plain,(
% 7.39/1.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK5) != k4_subset_1(sK5,sK6,k2_subset_1(sK5)) & m1_subset_1(sK6,k1_zfmisc_1(sK5)))),
% 7.39/1.48    introduced(choice_axiom,[])).
% 7.39/1.48  
% 7.39/1.48  fof(f62,plain,(
% 7.39/1.48    k2_subset_1(sK5) != k4_subset_1(sK5,sK6,k2_subset_1(sK5)) & m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 7.39/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f61])).
% 7.39/1.48  
% 7.39/1.48  fof(f104,plain,(
% 7.39/1.48    m1_subset_1(sK6,k1_zfmisc_1(sK5))),
% 7.39/1.48    inference(cnf_transformation,[],[f62])).
% 7.39/1.48  
% 7.39/1.48  fof(f18,axiom,(
% 7.39/1.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f33,plain,(
% 7.39/1.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.39/1.48    inference(ennf_transformation,[],[f18])).
% 7.39/1.48  
% 7.39/1.48  fof(f56,plain,(
% 7.39/1.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.39/1.48    inference(nnf_transformation,[],[f33])).
% 7.39/1.48  
% 7.39/1.48  fof(f89,plain,(
% 7.39/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f56])).
% 7.39/1.48  
% 7.39/1.48  fof(f14,axiom,(
% 7.39/1.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f48,plain,(
% 7.39/1.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.39/1.48    inference(nnf_transformation,[],[f14])).
% 7.39/1.48  
% 7.39/1.48  fof(f49,plain,(
% 7.39/1.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.39/1.48    inference(rectify,[],[f48])).
% 7.39/1.48  
% 7.39/1.48  fof(f50,plain,(
% 7.39/1.48    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.39/1.48    introduced(choice_axiom,[])).
% 7.39/1.48  
% 7.39/1.48  fof(f51,plain,(
% 7.39/1.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.39/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 7.39/1.48  
% 7.39/1.48  fof(f79,plain,(
% 7.39/1.48    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.39/1.48    inference(cnf_transformation,[],[f51])).
% 7.39/1.48  
% 7.39/1.48  fof(f130,plain,(
% 7.39/1.48    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.39/1.48    inference(equality_resolution,[],[f79])).
% 7.39/1.48  
% 7.39/1.48  fof(f3,axiom,(
% 7.39/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f30,plain,(
% 7.39/1.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.39/1.48    inference(ennf_transformation,[],[f3])).
% 7.39/1.48  
% 7.39/1.48  fof(f65,plain,(
% 7.39/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f30])).
% 7.39/1.48  
% 7.39/1.48  fof(f15,axiom,(
% 7.39/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f83,plain,(
% 7.39/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f15])).
% 7.39/1.48  
% 7.39/1.48  fof(f8,axiom,(
% 7.39/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f73,plain,(
% 7.39/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f8])).
% 7.39/1.48  
% 7.39/1.48  fof(f9,axiom,(
% 7.39/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f74,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f9])).
% 7.39/1.48  
% 7.39/1.48  fof(f10,axiom,(
% 7.39/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f75,plain,(
% 7.39/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f10])).
% 7.39/1.48  
% 7.39/1.48  fof(f11,axiom,(
% 7.39/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f76,plain,(
% 7.39/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f11])).
% 7.39/1.48  
% 7.39/1.48  fof(f12,axiom,(
% 7.39/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f77,plain,(
% 7.39/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f12])).
% 7.39/1.48  
% 7.39/1.48  fof(f13,axiom,(
% 7.39/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f78,plain,(
% 7.39/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f13])).
% 7.39/1.48  
% 7.39/1.48  fof(f106,plain,(
% 7.39/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.39/1.48    inference(definition_unfolding,[],[f77,f78])).
% 7.39/1.48  
% 7.39/1.48  fof(f107,plain,(
% 7.39/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.39/1.48    inference(definition_unfolding,[],[f76,f106])).
% 7.39/1.48  
% 7.39/1.48  fof(f108,plain,(
% 7.39/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.39/1.48    inference(definition_unfolding,[],[f75,f107])).
% 7.39/1.48  
% 7.39/1.48  fof(f109,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.39/1.48    inference(definition_unfolding,[],[f74,f108])).
% 7.39/1.48  
% 7.39/1.48  fof(f110,plain,(
% 7.39/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.39/1.48    inference(definition_unfolding,[],[f73,f109])).
% 7.39/1.48  
% 7.39/1.48  fof(f111,plain,(
% 7.39/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.39/1.48    inference(definition_unfolding,[],[f83,f110])).
% 7.39/1.48  
% 7.39/1.48  fof(f113,plain,(
% 7.39/1.48    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.39/1.48    inference(definition_unfolding,[],[f65,f111])).
% 7.39/1.48  
% 7.39/1.48  fof(f20,axiom,(
% 7.39/1.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f94,plain,(
% 7.39/1.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f20])).
% 7.39/1.48  
% 7.39/1.48  fof(f19,axiom,(
% 7.39/1.48    ! [X0] : k2_subset_1(X0) = X0),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f93,plain,(
% 7.39/1.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.39/1.48    inference(cnf_transformation,[],[f19])).
% 7.39/1.48  
% 7.39/1.48  fof(f24,axiom,(
% 7.39/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f37,plain,(
% 7.39/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.39/1.48    inference(ennf_transformation,[],[f24])).
% 7.39/1.48  
% 7.39/1.48  fof(f38,plain,(
% 7.39/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.39/1.48    inference(flattening,[],[f37])).
% 7.39/1.48  
% 7.39/1.48  fof(f98,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f38])).
% 7.39/1.48  
% 7.39/1.48  fof(f124,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.39/1.48    inference(definition_unfolding,[],[f98,f111])).
% 7.39/1.48  
% 7.39/1.48  fof(f105,plain,(
% 7.39/1.48    k2_subset_1(sK5) != k4_subset_1(sK5,sK6,k2_subset_1(sK5))),
% 7.39/1.48    inference(cnf_transformation,[],[f62])).
% 7.39/1.48  
% 7.39/1.48  fof(f91,plain,(
% 7.39/1.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f56])).
% 7.39/1.48  
% 7.39/1.48  fof(f26,axiom,(
% 7.39/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f100,plain,(
% 7.39/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f26])).
% 7.39/1.48  
% 7.39/1.48  fof(f2,axiom,(
% 7.39/1.48    k1_xboole_0 = o_0_0_xboole_0),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f64,plain,(
% 7.39/1.48    k1_xboole_0 = o_0_0_xboole_0),
% 7.39/1.48    inference(cnf_transformation,[],[f2])).
% 7.39/1.48  
% 7.39/1.48  fof(f125,plain,(
% 7.39/1.48    ( ! [X0] : (m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))) )),
% 7.39/1.48    inference(definition_unfolding,[],[f100,f64])).
% 7.39/1.48  
% 7.39/1.48  fof(f27,axiom,(
% 7.39/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f41,plain,(
% 7.39/1.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.39/1.48    inference(ennf_transformation,[],[f27])).
% 7.39/1.48  
% 7.39/1.48  fof(f42,plain,(
% 7.39/1.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.39/1.48    inference(flattening,[],[f41])).
% 7.39/1.48  
% 7.39/1.48  fof(f59,plain,(
% 7.39/1.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),X0)))),
% 7.39/1.48    introduced(choice_axiom,[])).
% 7.39/1.48  
% 7.39/1.48  fof(f60,plain,(
% 7.39/1.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.39/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f59])).
% 7.39/1.48  
% 7.39/1.48  fof(f102,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f60])).
% 7.39/1.48  
% 7.39/1.48  fof(f103,plain,(
% 7.39/1.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.39/1.48    inference(cnf_transformation,[],[f60])).
% 7.39/1.48  
% 7.39/1.48  fof(f5,axiom,(
% 7.39/1.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.39/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.48  
% 7.39/1.48  fof(f31,plain,(
% 7.39/1.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.39/1.48    inference(ennf_transformation,[],[f5])).
% 7.39/1.48  
% 7.39/1.48  fof(f67,plain,(
% 7.39/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.39/1.48    inference(cnf_transformation,[],[f31])).
% 7.39/1.48  
% 7.39/1.48  fof(f115,plain,(
% 7.39/1.48    ( ! [X0] : (o_0_0_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.39/1.48    inference(definition_unfolding,[],[f67,f64])).
% 7.39/1.48  
% 7.39/1.48  cnf(c_33,negated_conjecture,
% 7.39/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
% 7.39/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_923,plain,
% 7.39/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(sK5)) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_20,plain,
% 7.39/1.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.39/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_934,plain,
% 7.39/1.48      ( m1_subset_1(X0,X1) != iProver_top
% 7.39/1.48      | r2_hidden(X0,X1) = iProver_top
% 7.39/1.48      | v1_xboole_0(X1) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2557,plain,
% 7.39/1.48      ( r2_hidden(sK6,k1_zfmisc_1(sK5)) = iProver_top
% 7.39/1.48      | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_923,c_934]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_11,plain,
% 7.39/1.48      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.39/1.48      inference(cnf_transformation,[],[f130]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_940,plain,
% 7.39/1.48      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.39/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_6640,plain,
% 7.39/1.48      ( r1_tarski(sK6,sK5) = iProver_top
% 7.39/1.48      | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_2557,c_940]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1,plain,
% 7.39/1.48      ( ~ r1_tarski(X0,X1)
% 7.39/1.48      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 7.39/1.48      inference(cnf_transformation,[],[f113]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_949,plain,
% 7.39/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 7.39/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_6925,plain,
% 7.39/1.48      ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK5)) = sK5
% 7.39/1.48      | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_6640,c_949]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_22,plain,
% 7.39/1.48      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.39/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_933,plain,
% 7.39/1.48      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_21,plain,
% 7.39/1.48      ( k2_subset_1(X0) = X0 ),
% 7.39/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_964,plain,
% 7.39/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.39/1.48      inference(light_normalisation,[status(thm)],[c_933,c_21]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_26,plain,
% 7.39/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.39/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.39/1.48      | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 7.39/1.48      inference(cnf_transformation,[],[f124]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_929,plain,
% 7.39/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 7.39/1.48      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 7.39/1.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2514,plain,
% 7.39/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
% 7.39/1.48      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_964,c_929]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_12455,plain,
% 7.39/1.48      ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK5)) = k4_subset_1(sK5,sK6,sK5) ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_923,c_2514]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_16752,plain,
% 7.39/1.48      ( k4_subset_1(sK5,sK6,sK5) = sK5
% 7.39/1.48      | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
% 7.39/1.48      inference(demodulation,[status(thm)],[c_6925,c_12455]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_32,negated_conjecture,
% 7.39/1.48      ( k2_subset_1(sK5) != k4_subset_1(sK5,sK6,k2_subset_1(sK5)) ),
% 7.39/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_969,plain,
% 7.39/1.48      ( k4_subset_1(sK5,sK6,sK5) != sK5 ),
% 7.39/1.48      inference(demodulation,[status(thm)],[c_32,c_21]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_16755,plain,
% 7.39/1.48      ( v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
% 7.39/1.48      inference(forward_subsumption_resolution,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_16752,c_969]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_18,plain,
% 7.39/1.48      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 7.39/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_936,plain,
% 7.39/1.48      ( m1_subset_1(X0,X1) != iProver_top
% 7.39/1.48      | v1_xboole_0(X1) != iProver_top
% 7.39/1.48      | v1_xboole_0(X0) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2741,plain,
% 7.39/1.48      ( v1_xboole_0(X0) = iProver_top
% 7.39/1.48      | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_964,c_936]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_16760,plain,
% 7.39/1.48      ( v1_xboole_0(sK5) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_16755,c_2741]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_28,plain,
% 7.39/1.48      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
% 7.39/1.48      inference(cnf_transformation,[],[f125]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_927,plain,
% 7.39/1.48      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2511,plain,
% 7.39/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,o_0_0_xboole_0)) = k4_subset_1(X1,X0,o_0_0_xboole_0)
% 7.39/1.48      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_927,c_929]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_10175,plain,
% 7.39/1.48      ( k3_tarski(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) = k4_subset_1(X0,o_0_0_xboole_0,o_0_0_xboole_0) ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_927,c_2511]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_30,plain,
% 7.39/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.39/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.39/1.48      | r2_hidden(sK4(X1,X2,X0),X2)
% 7.39/1.48      | r1_tarski(X2,X0) ),
% 7.39/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_925,plain,
% 7.39/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.39/1.48      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.39/1.48      | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
% 7.39/1.48      | r1_tarski(X2,X0) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_29,plain,
% 7.39/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.39/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.39/1.48      | ~ r2_hidden(sK4(X1,X2,X0),X0)
% 7.39/1.48      | r1_tarski(X2,X0) ),
% 7.39/1.48      inference(cnf_transformation,[],[f103]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_926,plain,
% 7.39/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.39/1.48      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.39/1.48      | r2_hidden(sK4(X1,X2,X0),X0) != iProver_top
% 7.39/1.48      | r1_tarski(X2,X0) = iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1638,plain,
% 7.39/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.39/1.48      | r1_tarski(X0,X0) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_925,c_926]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4440,plain,
% 7.39/1.48      ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_927,c_1638]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4682,plain,
% 7.39/1.48      ( k3_tarski(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_4440,c_949]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_10487,plain,
% 7.39/1.48      ( k4_subset_1(X0,o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 7.39/1.48      inference(light_normalisation,[status(thm)],[c_10175,c_4682]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_10510,plain,
% 7.39/1.48      ( k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_10487]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_331,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1354,plain,
% 7.39/1.48      ( X0 != X1 | k2_subset_1(sK5) != X1 | k2_subset_1(sK5) = X0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_331]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_8902,plain,
% 7.39/1.48      ( k4_subset_1(X0,X1,X2) != X3
% 7.39/1.48      | k2_subset_1(sK5) != X3
% 7.39/1.48      | k2_subset_1(sK5) = k4_subset_1(X0,X1,X2) ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1354]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_8903,plain,
% 7.39/1.48      ( k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
% 7.39/1.48      | k2_subset_1(sK5) = k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
% 7.39/1.48      | k2_subset_1(sK5) != o_0_0_xboole_0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_8902]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2642,plain,
% 7.39/1.48      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_331]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_5437,plain,
% 7.39/1.48      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_2642]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_5438,plain,
% 7.39/1.48      ( sK6 != sK6 | sK6 = o_0_0_xboole_0 | o_0_0_xboole_0 != sK6 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_5437]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1583,plain,
% 7.39/1.48      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_331]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4981,plain,
% 7.39/1.48      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1583]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_4982,plain,
% 7.39/1.48      ( sK5 != sK5 | sK5 = o_0_0_xboole_0 | o_0_0_xboole_0 != sK5 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_4981]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2740,plain,
% 7.39/1.48      ( v1_xboole_0(k1_zfmisc_1(sK5)) != iProver_top
% 7.39/1.48      | v1_xboole_0(sK6) = iProver_top ),
% 7.39/1.48      inference(superposition,[status(thm)],[c_923,c_936]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_330,plain,( X0 = X0 ),theory(equality) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2504,plain,
% 7.39/1.48      ( sK5 = sK5 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_330]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_3,plain,
% 7.39/1.48      ( ~ v1_xboole_0(X0) | o_0_0_xboole_0 = X0 ),
% 7.39/1.48      inference(cnf_transformation,[],[f115]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2421,plain,
% 7.39/1.48      ( ~ v1_xboole_0(sK5) | o_0_0_xboole_0 = sK5 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2422,plain,
% 7.39/1.48      ( o_0_0_xboole_0 = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_2421]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_342,plain,
% 7.39/1.48      ( X0 != X1
% 7.39/1.48      | X2 != X3
% 7.39/1.48      | X4 != X5
% 7.39/1.48      | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
% 7.39/1.48      theory(equality) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2379,plain,
% 7.39/1.48      ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k4_subset_1(X0,X1,X2)
% 7.39/1.48      | k2_subset_1(sK5) != X2
% 7.39/1.48      | sK6 != X1
% 7.39/1.48      | sK5 != X0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_342]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2381,plain,
% 7.39/1.48      ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
% 7.39/1.48      | k2_subset_1(sK5) != o_0_0_xboole_0
% 7.39/1.48      | sK6 != o_0_0_xboole_0
% 7.39/1.48      | sK5 != o_0_0_xboole_0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_2379]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1527,plain,
% 7.39/1.48      ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != X0
% 7.39/1.48      | k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k2_subset_1(sK5)
% 7.39/1.48      | k2_subset_1(sK5) != X0 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_331]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2378,plain,
% 7.39/1.48      ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != k4_subset_1(X0,X1,X2)
% 7.39/1.48      | k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k2_subset_1(sK5)
% 7.39/1.48      | k2_subset_1(sK5) != k4_subset_1(X0,X1,X2) ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1527]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2380,plain,
% 7.39/1.48      ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
% 7.39/1.48      | k4_subset_1(sK5,sK6,k2_subset_1(sK5)) = k2_subset_1(sK5)
% 7.39/1.48      | k2_subset_1(sK5) != k4_subset_1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_2378]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2298,plain,
% 7.39/1.48      ( sK6 = sK6 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_330]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2278,plain,
% 7.39/1.48      ( ~ v1_xboole_0(sK6) | o_0_0_xboole_0 = sK6 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_2281,plain,
% 7.39/1.48      ( o_0_0_xboole_0 = sK6 | v1_xboole_0(sK6) != iProver_top ),
% 7.39/1.48      inference(predicate_to_equality,[status(thm)],[c_2278]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1598,plain,
% 7.39/1.48      ( X0 != sK5 | k2_subset_1(sK5) = X0 | k2_subset_1(sK5) != sK5 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1354]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1599,plain,
% 7.39/1.48      ( k2_subset_1(sK5) != sK5
% 7.39/1.48      | k2_subset_1(sK5) = o_0_0_xboole_0
% 7.39/1.48      | o_0_0_xboole_0 != sK5 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1598]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1363,plain,
% 7.39/1.48      ( k2_subset_1(sK5) = k2_subset_1(sK5) ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_330]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1218,plain,
% 7.39/1.48      ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != X0
% 7.39/1.48      | k2_subset_1(sK5) != X0
% 7.39/1.48      | k2_subset_1(sK5) = k4_subset_1(sK5,sK6,k2_subset_1(sK5)) ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_331]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1362,plain,
% 7.39/1.48      ( k4_subset_1(sK5,sK6,k2_subset_1(sK5)) != k2_subset_1(sK5)
% 7.39/1.48      | k2_subset_1(sK5) = k4_subset_1(sK5,sK6,k2_subset_1(sK5))
% 7.39/1.48      | k2_subset_1(sK5) != k2_subset_1(sK5) ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_1218]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(c_1361,plain,
% 7.39/1.48      ( k2_subset_1(sK5) = sK5 ),
% 7.39/1.48      inference(instantiation,[status(thm)],[c_21]) ).
% 7.39/1.48  
% 7.39/1.48  cnf(contradiction,plain,
% 7.39/1.48      ( $false ),
% 7.39/1.48      inference(minisat,
% 7.39/1.48                [status(thm)],
% 7.39/1.48                [c_16760,c_16755,c_10510,c_8903,c_5438,c_4982,c_2740,
% 7.39/1.48                 c_2504,c_2422,c_2381,c_2380,c_2298,c_2281,c_1599,c_1363,
% 7.39/1.48                 c_1362,c_1361,c_32]) ).
% 7.39/1.48  
% 7.39/1.48  
% 7.39/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.39/1.48  
% 7.39/1.48  ------                               Statistics
% 7.39/1.48  
% 7.39/1.48  ------ Selected
% 7.39/1.48  
% 7.39/1.48  total_time:                             0.58
% 7.39/1.48  
%------------------------------------------------------------------------------
