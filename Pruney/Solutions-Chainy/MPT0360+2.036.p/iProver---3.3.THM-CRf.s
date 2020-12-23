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
% DateTime   : Thu Dec  3 11:40:19 EST 2020

% Result     : Theorem 15.25s
% Output     : CNFRefutation 15.25s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 506 expanded)
%              Number of clauses        :   71 ( 164 expanded)
%              Number of leaves         :   30 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          :  424 (1595 expanded)
%              Number of equality atoms :  149 ( 463 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f53,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f53])).

fof(f77,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK7
      & r1_tarski(sK7,k3_subset_1(sK6,sK8))
      & r1_tarski(sK7,sK8)
      & m1_subset_1(sK8,k1_zfmisc_1(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( k1_xboole_0 != sK7
    & r1_tarski(sK7,k3_subset_1(sK6,sK8))
    & r1_tarski(sK7,sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f54,f77])).

fof(f130,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK6)) ),
    inference(cnf_transformation,[],[f78])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f63,plain,(
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

fof(f64,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f151,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f103])).

fof(f131,plain,(
    r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f78])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f150,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f120,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f132,plain,(
    r1_tarski(sK7,k3_subset_1(sK6,sK8)) ),
    inference(cnf_transformation,[],[f78])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f124,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f133,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f78])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f30,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f148,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f128,f123])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f28,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f118,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f26,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f149,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f89])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f72])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f139,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f108,f138])).

fof(f140,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f95,f139])).

fof(f141,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f85,f140])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f134,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f101,f102])).

fof(f135,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f100,f134])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f99,f135])).

fof(f137,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f98,f136])).

fof(f138,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f97,f137])).

fof(f142,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f96,f138])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ) ),
    inference(definition_unfolding,[],[f116,f141,f142])).

fof(f153,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(equality_resolution,[],[f145])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK6)) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1571,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1580,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9515,plain,
    ( r2_hidden(sK8,k1_zfmisc_1(sK6)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_1580])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_1593,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13394,plain,
    ( r1_tarski(sK8,sK6) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9515,c_1593])).

cnf(c_42,negated_conjecture,
    ( r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1572,plain,
    ( r1_tarski(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1599,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_29412,plain,
    ( r1_tarski(sK8,X0) != iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1599])).

cnf(c_33185,plain,
    ( r1_tarski(sK7,sK6) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13394,c_29412])).

cnf(c_17,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_5044,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK6))
    | ~ r1_tarski(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_23772,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(sK6))
    | ~ r1_tarski(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_5044])).

cnf(c_23778,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(sK6)) = iProver_top
    | r1_tarski(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23772])).

cnf(c_32,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3181,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK6))
    | ~ r2_hidden(X0,k1_zfmisc_1(sK6))
    | v1_xboole_0(k1_zfmisc_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_28245,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK6))
    | ~ r2_hidden(sK7,k1_zfmisc_1(sK6))
    | v1_xboole_0(k1_zfmisc_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_3181])).

cnf(c_28248,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK6)) = iProver_top
    | r2_hidden(sK7,k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28245])).

cnf(c_41,negated_conjecture,
    ( r1_tarski(sK7,k3_subset_1(sK6,sK8)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1573,plain,
    ( r1_tarski(sK7,k3_subset_1(sK6,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1578,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_18968,plain,
    ( k3_subset_1(sK6,k3_subset_1(sK6,sK8)) = sK8 ),
    inference(superposition,[status(thm)],[c_1571,c_1578])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_19294,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(k3_subset_1(sK6,sK8),k1_zfmisc_1(sK6)) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK6,sK8)) != iProver_top
    | r1_tarski(sK8,k3_subset_1(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18968,c_1576])).

cnf(c_44,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1879,plain,
    ( m1_subset_1(k3_subset_1(sK6,sK8),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1880,plain,
    ( m1_subset_1(k3_subset_1(sK6,sK8),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1879])).

cnf(c_20534,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK6)) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK6,sK8)) != iProver_top
    | r1_tarski(sK8,k3_subset_1(sK6,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19294,c_44,c_1880])).

cnf(c_20545,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK6)) != iProver_top
    | r1_tarski(sK8,k3_subset_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_20534])).

cnf(c_33187,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK6)) != iProver_top
    | r1_tarski(sK7,k3_subset_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20545,c_29412])).

cnf(c_40,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f148])).

cnf(c_1894,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK7,k3_subset_1(X0,sK7))
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_9434,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK6))
    | ~ r1_tarski(sK7,k3_subset_1(sK6,sK7))
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_9437,plain,
    ( k1_xboole_0 = sK7
    | m1_subset_1(sK7,k1_zfmisc_1(sK6)) != iProver_top
    | r1_tarski(sK7,k3_subset_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9434])).

cnf(c_34946,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33187,c_40,c_9437])).

cnf(c_38600,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33185,c_40,c_9437,c_23778,c_28248,c_33187])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1601,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_38605,plain,
    ( k1_zfmisc_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_38600,c_1601])).

cnf(c_29,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_46310,plain,
    ( k3_tarski(k1_xboole_0) = sK6 ),
    inference(superposition,[status(thm)],[c_38605,c_29])).

cnf(c_25,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_46328,plain,
    ( sK6 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_46310,c_25])).

cnf(c_46332,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_46328,c_38605])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7883,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7887,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))))) ),
    inference(instantiation,[status(thm)],[c_7883])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2639,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))))
    | ~ r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2641,plain,
    ( r2_hidden(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))))) ),
    inference(instantiation,[status(thm)],[c_2639])).

cnf(c_815,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2084,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X2),X3)
    | X3 != X1
    | k1_zfmisc_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_2086,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_1885,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X2))
    | ~ r1_tarski(k1_zfmisc_1(X2),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1887,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_128,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_125,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_107,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_80,plain,
    ( ~ r2_hidden(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46332,c_7887,c_2641,c_2086,c_1887,c_128,c_125,c_10,c_107,c_80])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.25/2.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.25/2.47  
% 15.25/2.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.25/2.47  
% 15.25/2.47  ------  iProver source info
% 15.25/2.47  
% 15.25/2.47  git: date: 2020-06-30 10:37:57 +0100
% 15.25/2.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.25/2.47  git: non_committed_changes: false
% 15.25/2.47  git: last_make_outside_of_git: false
% 15.25/2.47  
% 15.25/2.47  ------ 
% 15.25/2.47  
% 15.25/2.47  ------ Input Options
% 15.25/2.47  
% 15.25/2.47  --out_options                           all
% 15.25/2.47  --tptp_safe_out                         true
% 15.25/2.47  --problem_path                          ""
% 15.25/2.47  --include_path                          ""
% 15.25/2.47  --clausifier                            res/vclausify_rel
% 15.25/2.47  --clausifier_options                    --mode clausify
% 15.25/2.47  --stdin                                 false
% 15.25/2.47  --stats_out                             all
% 15.25/2.47  
% 15.25/2.47  ------ General Options
% 15.25/2.47  
% 15.25/2.47  --fof                                   false
% 15.25/2.47  --time_out_real                         305.
% 15.25/2.47  --time_out_virtual                      -1.
% 15.25/2.47  --symbol_type_check                     false
% 15.25/2.47  --clausify_out                          false
% 15.25/2.47  --sig_cnt_out                           false
% 15.25/2.47  --trig_cnt_out                          false
% 15.25/2.47  --trig_cnt_out_tolerance                1.
% 15.25/2.47  --trig_cnt_out_sk_spl                   false
% 15.25/2.47  --abstr_cl_out                          false
% 15.25/2.47  
% 15.25/2.47  ------ Global Options
% 15.25/2.47  
% 15.25/2.47  --schedule                              default
% 15.25/2.47  --add_important_lit                     false
% 15.25/2.47  --prop_solver_per_cl                    1000
% 15.25/2.47  --min_unsat_core                        false
% 15.25/2.47  --soft_assumptions                      false
% 15.25/2.47  --soft_lemma_size                       3
% 15.25/2.47  --prop_impl_unit_size                   0
% 15.25/2.47  --prop_impl_unit                        []
% 15.25/2.47  --share_sel_clauses                     true
% 15.25/2.47  --reset_solvers                         false
% 15.25/2.47  --bc_imp_inh                            [conj_cone]
% 15.25/2.47  --conj_cone_tolerance                   3.
% 15.25/2.47  --extra_neg_conj                        none
% 15.25/2.47  --large_theory_mode                     true
% 15.25/2.47  --prolific_symb_bound                   200
% 15.25/2.47  --lt_threshold                          2000
% 15.25/2.47  --clause_weak_htbl                      true
% 15.25/2.47  --gc_record_bc_elim                     false
% 15.25/2.47  
% 15.25/2.47  ------ Preprocessing Options
% 15.25/2.47  
% 15.25/2.47  --preprocessing_flag                    true
% 15.25/2.47  --time_out_prep_mult                    0.1
% 15.25/2.47  --splitting_mode                        input
% 15.25/2.47  --splitting_grd                         true
% 15.25/2.47  --splitting_cvd                         false
% 15.25/2.47  --splitting_cvd_svl                     false
% 15.25/2.47  --splitting_nvd                         32
% 15.25/2.47  --sub_typing                            true
% 15.25/2.47  --prep_gs_sim                           true
% 15.25/2.47  --prep_unflatten                        true
% 15.25/2.47  --prep_res_sim                          true
% 15.25/2.47  --prep_upred                            true
% 15.25/2.47  --prep_sem_filter                       exhaustive
% 15.25/2.47  --prep_sem_filter_out                   false
% 15.25/2.47  --pred_elim                             true
% 15.25/2.47  --res_sim_input                         true
% 15.25/2.47  --eq_ax_congr_red                       true
% 15.25/2.47  --pure_diseq_elim                       true
% 15.25/2.47  --brand_transform                       false
% 15.25/2.47  --non_eq_to_eq                          false
% 15.25/2.47  --prep_def_merge                        true
% 15.25/2.47  --prep_def_merge_prop_impl              false
% 15.25/2.47  --prep_def_merge_mbd                    true
% 15.25/2.47  --prep_def_merge_tr_red                 false
% 15.25/2.47  --prep_def_merge_tr_cl                  false
% 15.25/2.47  --smt_preprocessing                     true
% 15.25/2.47  --smt_ac_axioms                         fast
% 15.25/2.47  --preprocessed_out                      false
% 15.25/2.47  --preprocessed_stats                    false
% 15.25/2.47  
% 15.25/2.47  ------ Abstraction refinement Options
% 15.25/2.47  
% 15.25/2.47  --abstr_ref                             []
% 15.25/2.47  --abstr_ref_prep                        false
% 15.25/2.47  --abstr_ref_until_sat                   false
% 15.25/2.47  --abstr_ref_sig_restrict                funpre
% 15.25/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 15.25/2.47  --abstr_ref_under                       []
% 15.25/2.47  
% 15.25/2.47  ------ SAT Options
% 15.25/2.47  
% 15.25/2.47  --sat_mode                              false
% 15.25/2.47  --sat_fm_restart_options                ""
% 15.25/2.47  --sat_gr_def                            false
% 15.25/2.47  --sat_epr_types                         true
% 15.25/2.47  --sat_non_cyclic_types                  false
% 15.25/2.47  --sat_finite_models                     false
% 15.25/2.47  --sat_fm_lemmas                         false
% 15.25/2.47  --sat_fm_prep                           false
% 15.25/2.47  --sat_fm_uc_incr                        true
% 15.25/2.47  --sat_out_model                         small
% 15.25/2.47  --sat_out_clauses                       false
% 15.25/2.47  
% 15.25/2.47  ------ QBF Options
% 15.25/2.47  
% 15.25/2.47  --qbf_mode                              false
% 15.25/2.47  --qbf_elim_univ                         false
% 15.25/2.47  --qbf_dom_inst                          none
% 15.25/2.47  --qbf_dom_pre_inst                      false
% 15.25/2.47  --qbf_sk_in                             false
% 15.25/2.47  --qbf_pred_elim                         true
% 15.25/2.47  --qbf_split                             512
% 15.25/2.47  
% 15.25/2.47  ------ BMC1 Options
% 15.25/2.47  
% 15.25/2.47  --bmc1_incremental                      false
% 15.25/2.47  --bmc1_axioms                           reachable_all
% 15.25/2.47  --bmc1_min_bound                        0
% 15.25/2.47  --bmc1_max_bound                        -1
% 15.25/2.47  --bmc1_max_bound_default                -1
% 15.25/2.47  --bmc1_symbol_reachability              true
% 15.25/2.47  --bmc1_property_lemmas                  false
% 15.25/2.47  --bmc1_k_induction                      false
% 15.25/2.47  --bmc1_non_equiv_states                 false
% 15.25/2.47  --bmc1_deadlock                         false
% 15.25/2.47  --bmc1_ucm                              false
% 15.25/2.47  --bmc1_add_unsat_core                   none
% 15.25/2.47  --bmc1_unsat_core_children              false
% 15.25/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 15.25/2.47  --bmc1_out_stat                         full
% 15.25/2.47  --bmc1_ground_init                      false
% 15.25/2.47  --bmc1_pre_inst_next_state              false
% 15.25/2.47  --bmc1_pre_inst_state                   false
% 15.25/2.47  --bmc1_pre_inst_reach_state             false
% 15.25/2.47  --bmc1_out_unsat_core                   false
% 15.25/2.47  --bmc1_aig_witness_out                  false
% 15.25/2.47  --bmc1_verbose                          false
% 15.25/2.47  --bmc1_dump_clauses_tptp                false
% 15.25/2.47  --bmc1_dump_unsat_core_tptp             false
% 15.25/2.47  --bmc1_dump_file                        -
% 15.25/2.47  --bmc1_ucm_expand_uc_limit              128
% 15.25/2.47  --bmc1_ucm_n_expand_iterations          6
% 15.25/2.47  --bmc1_ucm_extend_mode                  1
% 15.25/2.47  --bmc1_ucm_init_mode                    2
% 15.25/2.47  --bmc1_ucm_cone_mode                    none
% 15.25/2.47  --bmc1_ucm_reduced_relation_type        0
% 15.25/2.47  --bmc1_ucm_relax_model                  4
% 15.25/2.47  --bmc1_ucm_full_tr_after_sat            true
% 15.25/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 15.25/2.47  --bmc1_ucm_layered_model                none
% 15.25/2.47  --bmc1_ucm_max_lemma_size               10
% 15.25/2.47  
% 15.25/2.47  ------ AIG Options
% 15.25/2.47  
% 15.25/2.47  --aig_mode                              false
% 15.25/2.47  
% 15.25/2.47  ------ Instantiation Options
% 15.25/2.47  
% 15.25/2.47  --instantiation_flag                    true
% 15.25/2.47  --inst_sos_flag                         false
% 15.25/2.47  --inst_sos_phase                        true
% 15.25/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.25/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.25/2.47  --inst_lit_sel_side                     num_symb
% 15.25/2.47  --inst_solver_per_active                1400
% 15.25/2.47  --inst_solver_calls_frac                1.
% 15.25/2.47  --inst_passive_queue_type               priority_queues
% 15.25/2.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.25/2.47  --inst_passive_queues_freq              [25;2]
% 15.25/2.47  --inst_dismatching                      true
% 15.25/2.47  --inst_eager_unprocessed_to_passive     true
% 15.25/2.47  --inst_prop_sim_given                   true
% 15.25/2.47  --inst_prop_sim_new                     false
% 15.25/2.47  --inst_subs_new                         false
% 15.25/2.47  --inst_eq_res_simp                      false
% 15.25/2.47  --inst_subs_given                       false
% 15.25/2.47  --inst_orphan_elimination               true
% 15.25/2.47  --inst_learning_loop_flag               true
% 15.25/2.47  --inst_learning_start                   3000
% 15.25/2.47  --inst_learning_factor                  2
% 15.25/2.47  --inst_start_prop_sim_after_learn       3
% 15.25/2.47  --inst_sel_renew                        solver
% 15.25/2.47  --inst_lit_activity_flag                true
% 15.25/2.47  --inst_restr_to_given                   false
% 15.25/2.47  --inst_activity_threshold               500
% 15.25/2.47  --inst_out_proof                        true
% 15.25/2.47  
% 15.25/2.47  ------ Resolution Options
% 15.25/2.47  
% 15.25/2.47  --resolution_flag                       true
% 15.25/2.47  --res_lit_sel                           adaptive
% 15.25/2.47  --res_lit_sel_side                      none
% 15.25/2.47  --res_ordering                          kbo
% 15.25/2.47  --res_to_prop_solver                    active
% 15.25/2.47  --res_prop_simpl_new                    false
% 15.25/2.47  --res_prop_simpl_given                  true
% 15.25/2.47  --res_passive_queue_type                priority_queues
% 15.25/2.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.25/2.47  --res_passive_queues_freq               [15;5]
% 15.25/2.47  --res_forward_subs                      full
% 15.25/2.47  --res_backward_subs                     full
% 15.25/2.47  --res_forward_subs_resolution           true
% 15.25/2.47  --res_backward_subs_resolution          true
% 15.25/2.47  --res_orphan_elimination                true
% 15.25/2.47  --res_time_limit                        2.
% 15.25/2.47  --res_out_proof                         true
% 15.25/2.47  
% 15.25/2.47  ------ Superposition Options
% 15.25/2.47  
% 15.25/2.47  --superposition_flag                    true
% 15.25/2.47  --sup_passive_queue_type                priority_queues
% 15.25/2.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.25/2.47  --sup_passive_queues_freq               [8;1;4]
% 15.25/2.47  --demod_completeness_check              fast
% 15.25/2.47  --demod_use_ground                      true
% 15.25/2.47  --sup_to_prop_solver                    passive
% 15.25/2.47  --sup_prop_simpl_new                    true
% 15.25/2.47  --sup_prop_simpl_given                  true
% 15.25/2.47  --sup_fun_splitting                     false
% 15.25/2.47  --sup_smt_interval                      50000
% 15.25/2.47  
% 15.25/2.47  ------ Superposition Simplification Setup
% 15.25/2.47  
% 15.25/2.47  --sup_indices_passive                   []
% 15.25/2.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.25/2.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.25/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.25/2.47  --sup_full_triv                         [TrivRules;PropSubs]
% 15.25/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.25/2.47  --sup_full_bw                           [BwDemod]
% 15.25/2.47  --sup_immed_triv                        [TrivRules]
% 15.25/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.25/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.25/2.47  --sup_immed_bw_main                     []
% 15.25/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.25/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 15.25/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.25/2.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.25/2.47  
% 15.25/2.47  ------ Combination Options
% 15.25/2.47  
% 15.25/2.47  --comb_res_mult                         3
% 15.25/2.47  --comb_sup_mult                         2
% 15.25/2.47  --comb_inst_mult                        10
% 15.25/2.47  
% 15.25/2.47  ------ Debug Options
% 15.25/2.47  
% 15.25/2.47  --dbg_backtrace                         false
% 15.25/2.47  --dbg_dump_prop_clauses                 false
% 15.25/2.47  --dbg_dump_prop_clauses_file            -
% 15.25/2.47  --dbg_out_stat                          false
% 15.25/2.47  ------ Parsing...
% 15.25/2.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.25/2.47  
% 15.25/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.25/2.47  
% 15.25/2.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.25/2.47  
% 15.25/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.25/2.47  ------ Proving...
% 15.25/2.47  ------ Problem Properties 
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  clauses                                 42
% 15.25/2.47  conjectures                             4
% 15.25/2.47  EPR                                     12
% 15.25/2.47  Horn                                    36
% 15.25/2.47  unary                                   13
% 15.25/2.47  binary                                  15
% 15.25/2.47  lits                                    88
% 15.25/2.47  lits eq                                 16
% 15.25/2.47  fd_pure                                 0
% 15.25/2.47  fd_pseudo                               0
% 15.25/2.47  fd_cond                                 3
% 15.25/2.47  fd_pseudo_cond                          4
% 15.25/2.47  AC symbols                              0
% 15.25/2.47  
% 15.25/2.47  ------ Schedule dynamic 5 is on 
% 15.25/2.47  
% 15.25/2.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  ------ 
% 15.25/2.47  Current options:
% 15.25/2.47  ------ 
% 15.25/2.47  
% 15.25/2.47  ------ Input Options
% 15.25/2.47  
% 15.25/2.47  --out_options                           all
% 15.25/2.47  --tptp_safe_out                         true
% 15.25/2.47  --problem_path                          ""
% 15.25/2.47  --include_path                          ""
% 15.25/2.47  --clausifier                            res/vclausify_rel
% 15.25/2.47  --clausifier_options                    --mode clausify
% 15.25/2.47  --stdin                                 false
% 15.25/2.47  --stats_out                             all
% 15.25/2.47  
% 15.25/2.47  ------ General Options
% 15.25/2.47  
% 15.25/2.47  --fof                                   false
% 15.25/2.47  --time_out_real                         305.
% 15.25/2.47  --time_out_virtual                      -1.
% 15.25/2.47  --symbol_type_check                     false
% 15.25/2.47  --clausify_out                          false
% 15.25/2.47  --sig_cnt_out                           false
% 15.25/2.47  --trig_cnt_out                          false
% 15.25/2.47  --trig_cnt_out_tolerance                1.
% 15.25/2.47  --trig_cnt_out_sk_spl                   false
% 15.25/2.47  --abstr_cl_out                          false
% 15.25/2.47  
% 15.25/2.47  ------ Global Options
% 15.25/2.47  
% 15.25/2.47  --schedule                              default
% 15.25/2.47  --add_important_lit                     false
% 15.25/2.47  --prop_solver_per_cl                    1000
% 15.25/2.47  --min_unsat_core                        false
% 15.25/2.47  --soft_assumptions                      false
% 15.25/2.47  --soft_lemma_size                       3
% 15.25/2.47  --prop_impl_unit_size                   0
% 15.25/2.47  --prop_impl_unit                        []
% 15.25/2.47  --share_sel_clauses                     true
% 15.25/2.47  --reset_solvers                         false
% 15.25/2.47  --bc_imp_inh                            [conj_cone]
% 15.25/2.47  --conj_cone_tolerance                   3.
% 15.25/2.47  --extra_neg_conj                        none
% 15.25/2.47  --large_theory_mode                     true
% 15.25/2.47  --prolific_symb_bound                   200
% 15.25/2.47  --lt_threshold                          2000
% 15.25/2.47  --clause_weak_htbl                      true
% 15.25/2.47  --gc_record_bc_elim                     false
% 15.25/2.47  
% 15.25/2.47  ------ Preprocessing Options
% 15.25/2.47  
% 15.25/2.47  --preprocessing_flag                    true
% 15.25/2.47  --time_out_prep_mult                    0.1
% 15.25/2.47  --splitting_mode                        input
% 15.25/2.47  --splitting_grd                         true
% 15.25/2.47  --splitting_cvd                         false
% 15.25/2.47  --splitting_cvd_svl                     false
% 15.25/2.47  --splitting_nvd                         32
% 15.25/2.47  --sub_typing                            true
% 15.25/2.47  --prep_gs_sim                           true
% 15.25/2.47  --prep_unflatten                        true
% 15.25/2.47  --prep_res_sim                          true
% 15.25/2.47  --prep_upred                            true
% 15.25/2.47  --prep_sem_filter                       exhaustive
% 15.25/2.47  --prep_sem_filter_out                   false
% 15.25/2.47  --pred_elim                             true
% 15.25/2.47  --res_sim_input                         true
% 15.25/2.47  --eq_ax_congr_red                       true
% 15.25/2.47  --pure_diseq_elim                       true
% 15.25/2.47  --brand_transform                       false
% 15.25/2.47  --non_eq_to_eq                          false
% 15.25/2.47  --prep_def_merge                        true
% 15.25/2.47  --prep_def_merge_prop_impl              false
% 15.25/2.47  --prep_def_merge_mbd                    true
% 15.25/2.47  --prep_def_merge_tr_red                 false
% 15.25/2.47  --prep_def_merge_tr_cl                  false
% 15.25/2.47  --smt_preprocessing                     true
% 15.25/2.47  --smt_ac_axioms                         fast
% 15.25/2.47  --preprocessed_out                      false
% 15.25/2.47  --preprocessed_stats                    false
% 15.25/2.47  
% 15.25/2.47  ------ Abstraction refinement Options
% 15.25/2.47  
% 15.25/2.47  --abstr_ref                             []
% 15.25/2.47  --abstr_ref_prep                        false
% 15.25/2.47  --abstr_ref_until_sat                   false
% 15.25/2.47  --abstr_ref_sig_restrict                funpre
% 15.25/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 15.25/2.47  --abstr_ref_under                       []
% 15.25/2.47  
% 15.25/2.47  ------ SAT Options
% 15.25/2.47  
% 15.25/2.47  --sat_mode                              false
% 15.25/2.47  --sat_fm_restart_options                ""
% 15.25/2.47  --sat_gr_def                            false
% 15.25/2.47  --sat_epr_types                         true
% 15.25/2.47  --sat_non_cyclic_types                  false
% 15.25/2.47  --sat_finite_models                     false
% 15.25/2.47  --sat_fm_lemmas                         false
% 15.25/2.47  --sat_fm_prep                           false
% 15.25/2.47  --sat_fm_uc_incr                        true
% 15.25/2.47  --sat_out_model                         small
% 15.25/2.47  --sat_out_clauses                       false
% 15.25/2.47  
% 15.25/2.47  ------ QBF Options
% 15.25/2.47  
% 15.25/2.47  --qbf_mode                              false
% 15.25/2.47  --qbf_elim_univ                         false
% 15.25/2.47  --qbf_dom_inst                          none
% 15.25/2.47  --qbf_dom_pre_inst                      false
% 15.25/2.47  --qbf_sk_in                             false
% 15.25/2.47  --qbf_pred_elim                         true
% 15.25/2.47  --qbf_split                             512
% 15.25/2.47  
% 15.25/2.47  ------ BMC1 Options
% 15.25/2.47  
% 15.25/2.47  --bmc1_incremental                      false
% 15.25/2.47  --bmc1_axioms                           reachable_all
% 15.25/2.47  --bmc1_min_bound                        0
% 15.25/2.47  --bmc1_max_bound                        -1
% 15.25/2.47  --bmc1_max_bound_default                -1
% 15.25/2.47  --bmc1_symbol_reachability              true
% 15.25/2.47  --bmc1_property_lemmas                  false
% 15.25/2.47  --bmc1_k_induction                      false
% 15.25/2.47  --bmc1_non_equiv_states                 false
% 15.25/2.47  --bmc1_deadlock                         false
% 15.25/2.47  --bmc1_ucm                              false
% 15.25/2.47  --bmc1_add_unsat_core                   none
% 15.25/2.47  --bmc1_unsat_core_children              false
% 15.25/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 15.25/2.47  --bmc1_out_stat                         full
% 15.25/2.47  --bmc1_ground_init                      false
% 15.25/2.47  --bmc1_pre_inst_next_state              false
% 15.25/2.47  --bmc1_pre_inst_state                   false
% 15.25/2.47  --bmc1_pre_inst_reach_state             false
% 15.25/2.47  --bmc1_out_unsat_core                   false
% 15.25/2.47  --bmc1_aig_witness_out                  false
% 15.25/2.47  --bmc1_verbose                          false
% 15.25/2.47  --bmc1_dump_clauses_tptp                false
% 15.25/2.47  --bmc1_dump_unsat_core_tptp             false
% 15.25/2.47  --bmc1_dump_file                        -
% 15.25/2.47  --bmc1_ucm_expand_uc_limit              128
% 15.25/2.47  --bmc1_ucm_n_expand_iterations          6
% 15.25/2.47  --bmc1_ucm_extend_mode                  1
% 15.25/2.47  --bmc1_ucm_init_mode                    2
% 15.25/2.47  --bmc1_ucm_cone_mode                    none
% 15.25/2.47  --bmc1_ucm_reduced_relation_type        0
% 15.25/2.47  --bmc1_ucm_relax_model                  4
% 15.25/2.47  --bmc1_ucm_full_tr_after_sat            true
% 15.25/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 15.25/2.47  --bmc1_ucm_layered_model                none
% 15.25/2.47  --bmc1_ucm_max_lemma_size               10
% 15.25/2.47  
% 15.25/2.47  ------ AIG Options
% 15.25/2.47  
% 15.25/2.47  --aig_mode                              false
% 15.25/2.47  
% 15.25/2.47  ------ Instantiation Options
% 15.25/2.47  
% 15.25/2.47  --instantiation_flag                    true
% 15.25/2.47  --inst_sos_flag                         false
% 15.25/2.47  --inst_sos_phase                        true
% 15.25/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.25/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.25/2.47  --inst_lit_sel_side                     none
% 15.25/2.47  --inst_solver_per_active                1400
% 15.25/2.47  --inst_solver_calls_frac                1.
% 15.25/2.47  --inst_passive_queue_type               priority_queues
% 15.25/2.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.25/2.47  --inst_passive_queues_freq              [25;2]
% 15.25/2.47  --inst_dismatching                      true
% 15.25/2.47  --inst_eager_unprocessed_to_passive     true
% 15.25/2.47  --inst_prop_sim_given                   true
% 15.25/2.47  --inst_prop_sim_new                     false
% 15.25/2.47  --inst_subs_new                         false
% 15.25/2.47  --inst_eq_res_simp                      false
% 15.25/2.47  --inst_subs_given                       false
% 15.25/2.47  --inst_orphan_elimination               true
% 15.25/2.47  --inst_learning_loop_flag               true
% 15.25/2.47  --inst_learning_start                   3000
% 15.25/2.47  --inst_learning_factor                  2
% 15.25/2.47  --inst_start_prop_sim_after_learn       3
% 15.25/2.47  --inst_sel_renew                        solver
% 15.25/2.47  --inst_lit_activity_flag                true
% 15.25/2.47  --inst_restr_to_given                   false
% 15.25/2.47  --inst_activity_threshold               500
% 15.25/2.47  --inst_out_proof                        true
% 15.25/2.47  
% 15.25/2.47  ------ Resolution Options
% 15.25/2.47  
% 15.25/2.47  --resolution_flag                       false
% 15.25/2.47  --res_lit_sel                           adaptive
% 15.25/2.47  --res_lit_sel_side                      none
% 15.25/2.47  --res_ordering                          kbo
% 15.25/2.47  --res_to_prop_solver                    active
% 15.25/2.47  --res_prop_simpl_new                    false
% 15.25/2.47  --res_prop_simpl_given                  true
% 15.25/2.47  --res_passive_queue_type                priority_queues
% 15.25/2.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.25/2.47  --res_passive_queues_freq               [15;5]
% 15.25/2.47  --res_forward_subs                      full
% 15.25/2.47  --res_backward_subs                     full
% 15.25/2.47  --res_forward_subs_resolution           true
% 15.25/2.47  --res_backward_subs_resolution          true
% 15.25/2.47  --res_orphan_elimination                true
% 15.25/2.47  --res_time_limit                        2.
% 15.25/2.47  --res_out_proof                         true
% 15.25/2.47  
% 15.25/2.47  ------ Superposition Options
% 15.25/2.47  
% 15.25/2.47  --superposition_flag                    true
% 15.25/2.47  --sup_passive_queue_type                priority_queues
% 15.25/2.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.25/2.47  --sup_passive_queues_freq               [8;1;4]
% 15.25/2.47  --demod_completeness_check              fast
% 15.25/2.47  --demod_use_ground                      true
% 15.25/2.47  --sup_to_prop_solver                    passive
% 15.25/2.47  --sup_prop_simpl_new                    true
% 15.25/2.47  --sup_prop_simpl_given                  true
% 15.25/2.47  --sup_fun_splitting                     false
% 15.25/2.47  --sup_smt_interval                      50000
% 15.25/2.47  
% 15.25/2.47  ------ Superposition Simplification Setup
% 15.25/2.47  
% 15.25/2.47  --sup_indices_passive                   []
% 15.25/2.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.25/2.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.25/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.25/2.47  --sup_full_triv                         [TrivRules;PropSubs]
% 15.25/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.25/2.47  --sup_full_bw                           [BwDemod]
% 15.25/2.47  --sup_immed_triv                        [TrivRules]
% 15.25/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.25/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.25/2.47  --sup_immed_bw_main                     []
% 15.25/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.25/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 15.25/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.25/2.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.25/2.47  
% 15.25/2.47  ------ Combination Options
% 15.25/2.47  
% 15.25/2.47  --comb_res_mult                         3
% 15.25/2.47  --comb_sup_mult                         2
% 15.25/2.47  --comb_inst_mult                        10
% 15.25/2.47  
% 15.25/2.47  ------ Debug Options
% 15.25/2.47  
% 15.25/2.47  --dbg_backtrace                         false
% 15.25/2.47  --dbg_dump_prop_clauses                 false
% 15.25/2.47  --dbg_dump_prop_clauses_file            -
% 15.25/2.47  --dbg_out_stat                          false
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  ------ Proving...
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  % SZS status Theorem for theBenchmark.p
% 15.25/2.47  
% 15.25/2.47  % SZS output start CNFRefutation for theBenchmark.p
% 15.25/2.47  
% 15.25/2.47  fof(f35,conjecture,(
% 15.25/2.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f36,negated_conjecture,(
% 15.25/2.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 15.25/2.47    inference(negated_conjecture,[],[f35])).
% 15.25/2.47  
% 15.25/2.47  fof(f53,plain,(
% 15.25/2.47    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.25/2.47    inference(ennf_transformation,[],[f36])).
% 15.25/2.47  
% 15.25/2.47  fof(f54,plain,(
% 15.25/2.47    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.25/2.47    inference(flattening,[],[f53])).
% 15.25/2.47  
% 15.25/2.47  fof(f77,plain,(
% 15.25/2.47    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK7 & r1_tarski(sK7,k3_subset_1(sK6,sK8)) & r1_tarski(sK7,sK8) & m1_subset_1(sK8,k1_zfmisc_1(sK6)))),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f78,plain,(
% 15.25/2.47    k1_xboole_0 != sK7 & r1_tarski(sK7,k3_subset_1(sK6,sK8)) & r1_tarski(sK7,sK8) & m1_subset_1(sK8,k1_zfmisc_1(sK6))),
% 15.25/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f54,f77])).
% 15.25/2.47  
% 15.25/2.47  fof(f130,plain,(
% 15.25/2.47    m1_subset_1(sK8,k1_zfmisc_1(sK6))),
% 15.25/2.47    inference(cnf_transformation,[],[f78])).
% 15.25/2.47  
% 15.25/2.47  fof(f29,axiom,(
% 15.25/2.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f48,plain,(
% 15.25/2.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 15.25/2.47    inference(ennf_transformation,[],[f29])).
% 15.25/2.47  
% 15.25/2.47  fof(f74,plain,(
% 15.25/2.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 15.25/2.47    inference(nnf_transformation,[],[f48])).
% 15.25/2.47  
% 15.25/2.47  fof(f119,plain,(
% 15.25/2.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f74])).
% 15.25/2.47  
% 15.25/2.47  fof(f22,axiom,(
% 15.25/2.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f61,plain,(
% 15.25/2.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.25/2.47    inference(nnf_transformation,[],[f22])).
% 15.25/2.47  
% 15.25/2.47  fof(f62,plain,(
% 15.25/2.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.25/2.47    inference(rectify,[],[f61])).
% 15.25/2.47  
% 15.25/2.47  fof(f63,plain,(
% 15.25/2.47    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f64,plain,(
% 15.25/2.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 15.25/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).
% 15.25/2.47  
% 15.25/2.47  fof(f103,plain,(
% 15.25/2.47    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 15.25/2.47    inference(cnf_transformation,[],[f64])).
% 15.25/2.47  
% 15.25/2.47  fof(f151,plain,(
% 15.25/2.47    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 15.25/2.47    inference(equality_resolution,[],[f103])).
% 15.25/2.47  
% 15.25/2.47  fof(f131,plain,(
% 15.25/2.47    r1_tarski(sK7,sK8)),
% 15.25/2.47    inference(cnf_transformation,[],[f78])).
% 15.25/2.47  
% 15.25/2.47  fof(f6,axiom,(
% 15.25/2.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f41,plain,(
% 15.25/2.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 15.25/2.47    inference(ennf_transformation,[],[f6])).
% 15.25/2.47  
% 15.25/2.47  fof(f42,plain,(
% 15.25/2.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 15.25/2.47    inference(flattening,[],[f41])).
% 15.25/2.47  
% 15.25/2.47  fof(f86,plain,(
% 15.25/2.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f42])).
% 15.25/2.47  
% 15.25/2.47  fof(f104,plain,(
% 15.25/2.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 15.25/2.47    inference(cnf_transformation,[],[f64])).
% 15.25/2.47  
% 15.25/2.47  fof(f150,plain,(
% 15.25/2.47    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 15.25/2.47    inference(equality_resolution,[],[f104])).
% 15.25/2.47  
% 15.25/2.47  fof(f120,plain,(
% 15.25/2.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f74])).
% 15.25/2.47  
% 15.25/2.47  fof(f132,plain,(
% 15.25/2.47    r1_tarski(sK7,k3_subset_1(sK6,sK8))),
% 15.25/2.47    inference(cnf_transformation,[],[f78])).
% 15.25/2.47  
% 15.25/2.47  fof(f32,axiom,(
% 15.25/2.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f50,plain,(
% 15.25/2.47    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.25/2.47    inference(ennf_transformation,[],[f32])).
% 15.25/2.47  
% 15.25/2.47  fof(f125,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f50])).
% 15.25/2.47  
% 15.25/2.47  fof(f33,axiom,(
% 15.25/2.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f51,plain,(
% 15.25/2.47    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.25/2.47    inference(ennf_transformation,[],[f33])).
% 15.25/2.47  
% 15.25/2.47  fof(f75,plain,(
% 15.25/2.47    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.25/2.47    inference(nnf_transformation,[],[f51])).
% 15.25/2.47  
% 15.25/2.47  fof(f126,plain,(
% 15.25/2.47    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f75])).
% 15.25/2.47  
% 15.25/2.47  fof(f31,axiom,(
% 15.25/2.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f49,plain,(
% 15.25/2.47    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.25/2.47    inference(ennf_transformation,[],[f31])).
% 15.25/2.47  
% 15.25/2.47  fof(f124,plain,(
% 15.25/2.47    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f49])).
% 15.25/2.47  
% 15.25/2.47  fof(f133,plain,(
% 15.25/2.47    k1_xboole_0 != sK7),
% 15.25/2.47    inference(cnf_transformation,[],[f78])).
% 15.25/2.47  
% 15.25/2.47  fof(f34,axiom,(
% 15.25/2.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f52,plain,(
% 15.25/2.47    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.25/2.47    inference(ennf_transformation,[],[f34])).
% 15.25/2.47  
% 15.25/2.47  fof(f76,plain,(
% 15.25/2.47    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.25/2.47    inference(nnf_transformation,[],[f52])).
% 15.25/2.47  
% 15.25/2.47  fof(f128,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f76])).
% 15.25/2.47  
% 15.25/2.47  fof(f30,axiom,(
% 15.25/2.47    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f123,plain,(
% 15.25/2.47    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f30])).
% 15.25/2.47  
% 15.25/2.47  fof(f148,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.25/2.47    inference(definition_unfolding,[],[f128,f123])).
% 15.25/2.47  
% 15.25/2.47  fof(f3,axiom,(
% 15.25/2.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f39,plain,(
% 15.25/2.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 15.25/2.47    inference(ennf_transformation,[],[f3])).
% 15.25/2.47  
% 15.25/2.47  fof(f83,plain,(
% 15.25/2.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f39])).
% 15.25/2.47  
% 15.25/2.47  fof(f28,axiom,(
% 15.25/2.47    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f118,plain,(
% 15.25/2.47    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 15.25/2.47    inference(cnf_transformation,[],[f28])).
% 15.25/2.47  
% 15.25/2.47  fof(f26,axiom,(
% 15.25/2.47    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f114,plain,(
% 15.25/2.47    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 15.25/2.47    inference(cnf_transformation,[],[f26])).
% 15.25/2.47  
% 15.25/2.47  fof(f7,axiom,(
% 15.25/2.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f87,plain,(
% 15.25/2.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f7])).
% 15.25/2.47  
% 15.25/2.47  fof(f1,axiom,(
% 15.25/2.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f38,plain,(
% 15.25/2.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.25/2.47    inference(ennf_transformation,[],[f1])).
% 15.25/2.47  
% 15.25/2.47  fof(f55,plain,(
% 15.25/2.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.25/2.47    inference(nnf_transformation,[],[f38])).
% 15.25/2.47  
% 15.25/2.47  fof(f56,plain,(
% 15.25/2.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.25/2.47    inference(rectify,[],[f55])).
% 15.25/2.47  
% 15.25/2.47  fof(f57,plain,(
% 15.25/2.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f58,plain,(
% 15.25/2.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.25/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).
% 15.25/2.47  
% 15.25/2.47  fof(f79,plain,(
% 15.25/2.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f58])).
% 15.25/2.47  
% 15.25/2.47  fof(f9,axiom,(
% 15.25/2.47    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f43,plain,(
% 15.25/2.47    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 15.25/2.47    inference(ennf_transformation,[],[f9])).
% 15.25/2.47  
% 15.25/2.47  fof(f90,plain,(
% 15.25/2.47    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 15.25/2.47    inference(cnf_transformation,[],[f43])).
% 15.25/2.47  
% 15.25/2.47  fof(f89,plain,(
% 15.25/2.47    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f43])).
% 15.25/2.47  
% 15.25/2.47  fof(f149,plain,(
% 15.25/2.47    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 15.25/2.47    inference(equality_resolution,[],[f89])).
% 15.25/2.47  
% 15.25/2.47  fof(f27,axiom,(
% 15.25/2.47    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f72,plain,(
% 15.25/2.47    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 15.25/2.47    inference(nnf_transformation,[],[f27])).
% 15.25/2.47  
% 15.25/2.47  fof(f73,plain,(
% 15.25/2.47    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 15.25/2.47    inference(flattening,[],[f72])).
% 15.25/2.47  
% 15.25/2.47  fof(f116,plain,(
% 15.25/2.47    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f73])).
% 15.25/2.47  
% 15.25/2.47  fof(f5,axiom,(
% 15.25/2.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f85,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f5])).
% 15.25/2.47  
% 15.25/2.47  fof(f14,axiom,(
% 15.25/2.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f95,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f14])).
% 15.25/2.47  
% 15.25/2.47  fof(f24,axiom,(
% 15.25/2.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f108,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f24])).
% 15.25/2.47  
% 15.25/2.47  fof(f139,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 15.25/2.47    inference(definition_unfolding,[],[f108,f138])).
% 15.25/2.47  
% 15.25/2.47  fof(f140,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 15.25/2.47    inference(definition_unfolding,[],[f95,f139])).
% 15.25/2.47  
% 15.25/2.47  fof(f141,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 15.25/2.47    inference(definition_unfolding,[],[f85,f140])).
% 15.25/2.47  
% 15.25/2.47  fof(f15,axiom,(
% 15.25/2.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f96,plain,(
% 15.25/2.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f15])).
% 15.25/2.47  
% 15.25/2.47  fof(f16,axiom,(
% 15.25/2.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f97,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f16])).
% 15.25/2.47  
% 15.25/2.47  fof(f17,axiom,(
% 15.25/2.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f98,plain,(
% 15.25/2.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f17])).
% 15.25/2.47  
% 15.25/2.47  fof(f18,axiom,(
% 15.25/2.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f99,plain,(
% 15.25/2.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f18])).
% 15.25/2.47  
% 15.25/2.47  fof(f19,axiom,(
% 15.25/2.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f100,plain,(
% 15.25/2.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f19])).
% 15.25/2.47  
% 15.25/2.47  fof(f20,axiom,(
% 15.25/2.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f101,plain,(
% 15.25/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f20])).
% 15.25/2.47  
% 15.25/2.47  fof(f21,axiom,(
% 15.25/2.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 15.25/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f102,plain,(
% 15.25/2.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f21])).
% 15.25/2.47  
% 15.25/2.47  fof(f134,plain,(
% 15.25/2.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 15.25/2.47    inference(definition_unfolding,[],[f101,f102])).
% 15.25/2.47  
% 15.25/2.47  fof(f135,plain,(
% 15.25/2.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 15.25/2.47    inference(definition_unfolding,[],[f100,f134])).
% 15.25/2.47  
% 15.25/2.47  fof(f136,plain,(
% 15.25/2.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 15.25/2.47    inference(definition_unfolding,[],[f99,f135])).
% 15.25/2.47  
% 15.25/2.47  fof(f137,plain,(
% 15.25/2.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 15.25/2.47    inference(definition_unfolding,[],[f98,f136])).
% 15.25/2.47  
% 15.25/2.47  fof(f138,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 15.25/2.47    inference(definition_unfolding,[],[f97,f137])).
% 15.25/2.47  
% 15.25/2.47  fof(f142,plain,(
% 15.25/2.47    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 15.25/2.47    inference(definition_unfolding,[],[f96,f138])).
% 15.25/2.47  
% 15.25/2.47  fof(f145,plain,(
% 15.25/2.47    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 15.25/2.47    inference(definition_unfolding,[],[f116,f141,f142])).
% 15.25/2.47  
% 15.25/2.47  fof(f153,plain,(
% 15.25/2.47    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 15.25/2.47    inference(equality_resolution,[],[f145])).
% 15.25/2.47  
% 15.25/2.47  cnf(c_43,negated_conjecture,
% 15.25/2.47      ( m1_subset_1(sK8,k1_zfmisc_1(sK6)) ),
% 15.25/2.47      inference(cnf_transformation,[],[f130]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1571,plain,
% 15.25/2.47      ( m1_subset_1(sK8,k1_zfmisc_1(sK6)) = iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_33,plain,
% 15.25/2.47      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.25/2.47      inference(cnf_transformation,[],[f119]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1580,plain,
% 15.25/2.47      ( m1_subset_1(X0,X1) != iProver_top
% 15.25/2.47      | r2_hidden(X0,X1) = iProver_top
% 15.25/2.47      | v1_xboole_0(X1) = iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_9515,plain,
% 15.25/2.47      ( r2_hidden(sK8,k1_zfmisc_1(sK6)) = iProver_top
% 15.25/2.47      | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
% 15.25/2.47      inference(superposition,[status(thm)],[c_1571,c_1580]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_18,plain,
% 15.25/2.47      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.25/2.47      inference(cnf_transformation,[],[f151]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1593,plain,
% 15.25/2.47      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.25/2.47      | r1_tarski(X0,X1) = iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_13394,plain,
% 15.25/2.47      ( r1_tarski(sK8,sK6) = iProver_top
% 15.25/2.47      | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
% 15.25/2.47      inference(superposition,[status(thm)],[c_9515,c_1593]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_42,negated_conjecture,
% 15.25/2.47      ( r1_tarski(sK7,sK8) ),
% 15.25/2.47      inference(cnf_transformation,[],[f131]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1572,plain,
% 15.25/2.47      ( r1_tarski(sK7,sK8) = iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_6,plain,
% 15.25/2.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 15.25/2.47      inference(cnf_transformation,[],[f86]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1599,plain,
% 15.25/2.47      ( r1_tarski(X0,X1) != iProver_top
% 15.25/2.47      | r1_tarski(X1,X2) != iProver_top
% 15.25/2.47      | r1_tarski(X0,X2) = iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_29412,plain,
% 15.25/2.47      ( r1_tarski(sK8,X0) != iProver_top
% 15.25/2.47      | r1_tarski(sK7,X0) = iProver_top ),
% 15.25/2.47      inference(superposition,[status(thm)],[c_1572,c_1599]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_33185,plain,
% 15.25/2.47      ( r1_tarski(sK7,sK6) = iProver_top
% 15.25/2.47      | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
% 15.25/2.48      inference(superposition,[status(thm)],[c_13394,c_29412]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_17,plain,
% 15.25/2.48      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.25/2.48      inference(cnf_transformation,[],[f150]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_5044,plain,
% 15.25/2.48      ( r2_hidden(X0,k1_zfmisc_1(sK6)) | ~ r1_tarski(X0,sK6) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_17]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_23772,plain,
% 15.25/2.48      ( r2_hidden(sK7,k1_zfmisc_1(sK6)) | ~ r1_tarski(sK7,sK6) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_5044]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_23778,plain,
% 15.25/2.48      ( r2_hidden(sK7,k1_zfmisc_1(sK6)) = iProver_top
% 15.25/2.48      | r1_tarski(sK7,sK6) != iProver_top ),
% 15.25/2.48      inference(predicate_to_equality,[status(thm)],[c_23772]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_32,plain,
% 15.25/2.48      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.25/2.48      inference(cnf_transformation,[],[f120]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_3181,plain,
% 15.25/2.48      ( m1_subset_1(X0,k1_zfmisc_1(sK6))
% 15.25/2.48      | ~ r2_hidden(X0,k1_zfmisc_1(sK6))
% 15.25/2.48      | v1_xboole_0(k1_zfmisc_1(sK6)) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_32]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_28245,plain,
% 15.25/2.48      ( m1_subset_1(sK7,k1_zfmisc_1(sK6))
% 15.25/2.48      | ~ r2_hidden(sK7,k1_zfmisc_1(sK6))
% 15.25/2.48      | v1_xboole_0(k1_zfmisc_1(sK6)) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_3181]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_28248,plain,
% 15.25/2.48      ( m1_subset_1(sK7,k1_zfmisc_1(sK6)) = iProver_top
% 15.25/2.48      | r2_hidden(sK7,k1_zfmisc_1(sK6)) != iProver_top
% 15.25/2.48      | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
% 15.25/2.48      inference(predicate_to_equality,[status(thm)],[c_28245]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_41,negated_conjecture,
% 15.25/2.48      ( r1_tarski(sK7,k3_subset_1(sK6,sK8)) ),
% 15.25/2.48      inference(cnf_transformation,[],[f132]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_1573,plain,
% 15.25/2.48      ( r1_tarski(sK7,k3_subset_1(sK6,sK8)) = iProver_top ),
% 15.25/2.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_35,plain,
% 15.25/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.25/2.48      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.25/2.48      inference(cnf_transformation,[],[f125]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_1578,plain,
% 15.25/2.48      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 15.25/2.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.25/2.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_18968,plain,
% 15.25/2.48      ( k3_subset_1(sK6,k3_subset_1(sK6,sK8)) = sK8 ),
% 15.25/2.48      inference(superposition,[status(thm)],[c_1571,c_1578]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_37,plain,
% 15.25/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.25/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.25/2.48      | ~ r1_tarski(X0,X2)
% 15.25/2.48      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 15.25/2.48      inference(cnf_transformation,[],[f126]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_1576,plain,
% 15.25/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.25/2.48      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 15.25/2.48      | r1_tarski(X0,X2) != iProver_top
% 15.25/2.48      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
% 15.25/2.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_19294,plain,
% 15.25/2.48      ( m1_subset_1(X0,k1_zfmisc_1(sK6)) != iProver_top
% 15.25/2.48      | m1_subset_1(k3_subset_1(sK6,sK8),k1_zfmisc_1(sK6)) != iProver_top
% 15.25/2.48      | r1_tarski(X0,k3_subset_1(sK6,sK8)) != iProver_top
% 15.25/2.48      | r1_tarski(sK8,k3_subset_1(sK6,X0)) = iProver_top ),
% 15.25/2.48      inference(superposition,[status(thm)],[c_18968,c_1576]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_44,plain,
% 15.25/2.48      ( m1_subset_1(sK8,k1_zfmisc_1(sK6)) = iProver_top ),
% 15.25/2.48      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_34,plain,
% 15.25/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.25/2.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 15.25/2.48      inference(cnf_transformation,[],[f124]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_1879,plain,
% 15.25/2.48      ( m1_subset_1(k3_subset_1(sK6,sK8),k1_zfmisc_1(sK6))
% 15.25/2.48      | ~ m1_subset_1(sK8,k1_zfmisc_1(sK6)) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_34]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_1880,plain,
% 15.25/2.48      ( m1_subset_1(k3_subset_1(sK6,sK8),k1_zfmisc_1(sK6)) = iProver_top
% 15.25/2.48      | m1_subset_1(sK8,k1_zfmisc_1(sK6)) != iProver_top ),
% 15.25/2.48      inference(predicate_to_equality,[status(thm)],[c_1879]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_20534,plain,
% 15.25/2.48      ( m1_subset_1(X0,k1_zfmisc_1(sK6)) != iProver_top
% 15.25/2.48      | r1_tarski(X0,k3_subset_1(sK6,sK8)) != iProver_top
% 15.25/2.48      | r1_tarski(sK8,k3_subset_1(sK6,X0)) = iProver_top ),
% 15.25/2.48      inference(global_propositional_subsumption,
% 15.25/2.48                [status(thm)],
% 15.25/2.48                [c_19294,c_44,c_1880]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_20545,plain,
% 15.25/2.48      ( m1_subset_1(sK7,k1_zfmisc_1(sK6)) != iProver_top
% 15.25/2.48      | r1_tarski(sK8,k3_subset_1(sK6,sK7)) = iProver_top ),
% 15.25/2.48      inference(superposition,[status(thm)],[c_1573,c_20534]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_33187,plain,
% 15.25/2.48      ( m1_subset_1(sK7,k1_zfmisc_1(sK6)) != iProver_top
% 15.25/2.48      | r1_tarski(sK7,k3_subset_1(sK6,sK7)) = iProver_top ),
% 15.25/2.48      inference(superposition,[status(thm)],[c_20545,c_29412]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_40,negated_conjecture,
% 15.25/2.48      ( k1_xboole_0 != sK7 ),
% 15.25/2.48      inference(cnf_transformation,[],[f133]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_39,plain,
% 15.25/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.25/2.48      | ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 15.25/2.48      | k1_xboole_0 = X0 ),
% 15.25/2.48      inference(cnf_transformation,[],[f148]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_1894,plain,
% 15.25/2.48      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 15.25/2.48      | ~ r1_tarski(sK7,k3_subset_1(X0,sK7))
% 15.25/2.48      | k1_xboole_0 = sK7 ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_39]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_9434,plain,
% 15.25/2.48      ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK6))
% 15.25/2.48      | ~ r1_tarski(sK7,k3_subset_1(sK6,sK7))
% 15.25/2.48      | k1_xboole_0 = sK7 ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_1894]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_9437,plain,
% 15.25/2.48      ( k1_xboole_0 = sK7
% 15.25/2.48      | m1_subset_1(sK7,k1_zfmisc_1(sK6)) != iProver_top
% 15.25/2.48      | r1_tarski(sK7,k3_subset_1(sK6,sK7)) != iProver_top ),
% 15.25/2.48      inference(predicate_to_equality,[status(thm)],[c_9434]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_34946,plain,
% 15.25/2.48      ( m1_subset_1(sK7,k1_zfmisc_1(sK6)) != iProver_top ),
% 15.25/2.48      inference(global_propositional_subsumption,
% 15.25/2.48                [status(thm)],
% 15.25/2.48                [c_33187,c_40,c_9437]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_38600,plain,
% 15.25/2.48      ( v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
% 15.25/2.48      inference(global_propositional_subsumption,
% 15.25/2.48                [status(thm)],
% 15.25/2.48                [c_33185,c_40,c_9437,c_23778,c_28248,c_33187]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_4,plain,
% 15.25/2.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 15.25/2.48      inference(cnf_transformation,[],[f83]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_1601,plain,
% 15.25/2.48      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 15.25/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_38605,plain,
% 15.25/2.48      ( k1_zfmisc_1(sK6) = k1_xboole_0 ),
% 15.25/2.48      inference(superposition,[status(thm)],[c_38600,c_1601]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_29,plain,
% 15.25/2.48      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 15.25/2.48      inference(cnf_transformation,[],[f118]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_46310,plain,
% 15.25/2.48      ( k3_tarski(k1_xboole_0) = sK6 ),
% 15.25/2.48      inference(superposition,[status(thm)],[c_38605,c_29]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_25,plain,
% 15.25/2.48      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 15.25/2.48      inference(cnf_transformation,[],[f114]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_46328,plain,
% 15.25/2.48      ( sK6 = k1_xboole_0 ),
% 15.25/2.48      inference(light_normalisation,[status(thm)],[c_46310,c_25]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_46332,plain,
% 15.25/2.48      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
% 15.25/2.48      inference(demodulation,[status(thm)],[c_46328,c_38605]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_7,plain,
% 15.25/2.48      ( r1_tarski(k1_xboole_0,X0) ),
% 15.25/2.48      inference(cnf_transformation,[],[f87]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_7883,plain,
% 15.25/2.48      ( r1_tarski(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_7]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_7887,plain,
% 15.25/2.48      ( r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))))) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_7883]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_2,plain,
% 15.25/2.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.25/2.48      inference(cnf_transformation,[],[f79]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_2639,plain,
% 15.25/2.48      ( ~ r2_hidden(X0,X1)
% 15.25/2.48      | r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))))
% 15.25/2.48      | ~ r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_2]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_2641,plain,
% 15.25/2.48      ( r2_hidden(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))))
% 15.25/2.48      | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 15.25/2.48      | ~ r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))))) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_2639]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_815,plain,
% 15.25/2.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.25/2.48      theory(equality) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_2084,plain,
% 15.25/2.48      ( ~ r1_tarski(X0,X1)
% 15.25/2.48      | r1_tarski(k1_zfmisc_1(X2),X3)
% 15.25/2.48      | X3 != X1
% 15.25/2.48      | k1_zfmisc_1(X2) != X0 ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_815]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_2086,plain,
% 15.25/2.48      ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
% 15.25/2.48      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.25/2.48      | k1_zfmisc_1(k1_xboole_0) != k1_xboole_0
% 15.25/2.48      | k1_xboole_0 != k1_xboole_0 ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_2084]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_1885,plain,
% 15.25/2.48      ( r2_hidden(X0,X1)
% 15.25/2.48      | ~ r2_hidden(X0,k1_zfmisc_1(X2))
% 15.25/2.48      | ~ r1_tarski(k1_zfmisc_1(X2),X1) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_2]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_1887,plain,
% 15.25/2.48      ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 15.25/2.48      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 15.25/2.48      | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_1885]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_128,plain,
% 15.25/2.48      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_7]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_9,plain,
% 15.25/2.48      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 15.25/2.48      inference(cnf_transformation,[],[f90]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_125,plain,
% 15.25/2.48      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 15.25/2.48      | k1_xboole_0 = k1_xboole_0 ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_9]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_10,plain,
% 15.25/2.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 15.25/2.48      inference(cnf_transformation,[],[f149]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_107,plain,
% 15.25/2.48      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 15.25/2.48      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_17]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_27,plain,
% 15.25/2.48      ( ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) ),
% 15.25/2.48      inference(cnf_transformation,[],[f153]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(c_80,plain,
% 15.25/2.48      ( ~ r2_hidden(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))))) ),
% 15.25/2.48      inference(instantiation,[status(thm)],[c_27]) ).
% 15.25/2.48  
% 15.25/2.48  cnf(contradiction,plain,
% 15.25/2.48      ( $false ),
% 15.25/2.48      inference(minisat,
% 15.25/2.48                [status(thm)],
% 15.25/2.48                [c_46332,c_7887,c_2641,c_2086,c_1887,c_128,c_125,c_10,
% 15.25/2.48                 c_107,c_80]) ).
% 15.25/2.48  
% 15.25/2.48  
% 15.25/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.25/2.48  
% 15.25/2.48  ------                               Statistics
% 15.25/2.48  
% 15.25/2.48  ------ General
% 15.25/2.48  
% 15.25/2.48  abstr_ref_over_cycles:                  0
% 15.25/2.48  abstr_ref_under_cycles:                 0
% 15.25/2.48  gc_basic_clause_elim:                   0
% 15.25/2.48  forced_gc_time:                         0
% 15.25/2.48  parsing_time:                           0.01
% 15.25/2.48  unif_index_cands_time:                  0.
% 15.25/2.48  unif_index_add_time:                    0.
% 15.25/2.48  orderings_time:                         0.
% 15.25/2.48  out_proof_time:                         0.012
% 15.25/2.48  total_time:                             1.624
% 15.25/2.48  num_of_symbols:                         51
% 15.25/2.48  num_of_terms:                           60815
% 15.25/2.48  
% 15.25/2.48  ------ Preprocessing
% 15.25/2.48  
% 15.25/2.48  num_of_splits:                          0
% 15.25/2.48  num_of_split_atoms:                     0
% 15.25/2.48  num_of_reused_defs:                     0
% 15.25/2.48  num_eq_ax_congr_red:                    52
% 15.25/2.48  num_of_sem_filtered_clauses:            1
% 15.25/2.48  num_of_subtypes:                        0
% 15.25/2.48  monotx_restored_types:                  0
% 15.25/2.48  sat_num_of_epr_types:                   0
% 15.25/2.48  sat_num_of_non_cyclic_types:            0
% 15.25/2.48  sat_guarded_non_collapsed_types:        0
% 15.25/2.48  num_pure_diseq_elim:                    0
% 15.25/2.48  simp_replaced_by:                       0
% 15.25/2.48  res_preprocessed:                       193
% 15.25/2.48  prep_upred:                             0
% 15.25/2.48  prep_unflattend:                        3
% 15.25/2.48  smt_new_axioms:                         0
% 15.25/2.48  pred_elim_cands:                        4
% 15.25/2.48  pred_elim:                              1
% 15.25/2.48  pred_elim_cl:                           2
% 15.25/2.48  pred_elim_cycles:                       3
% 15.25/2.48  merged_defs:                            8
% 15.25/2.48  merged_defs_ncl:                        0
% 15.25/2.48  bin_hyper_res:                          8
% 15.25/2.48  prep_cycles:                            4
% 15.25/2.48  pred_elim_time:                         0.001
% 15.25/2.48  splitting_time:                         0.
% 15.25/2.48  sem_filter_time:                        0.
% 15.25/2.48  monotx_time:                            0.001
% 15.25/2.48  subtype_inf_time:                       0.
% 15.25/2.48  
% 15.25/2.48  ------ Problem properties
% 15.25/2.48  
% 15.25/2.48  clauses:                                42
% 15.25/2.48  conjectures:                            4
% 15.25/2.48  epr:                                    12
% 15.25/2.48  horn:                                   36
% 15.25/2.48  ground:                                 6
% 15.25/2.48  unary:                                  13
% 15.25/2.48  binary:                                 15
% 15.25/2.48  lits:                                   88
% 15.25/2.48  lits_eq:                                16
% 15.25/2.48  fd_pure:                                0
% 15.25/2.48  fd_pseudo:                              0
% 15.25/2.48  fd_cond:                                3
% 15.25/2.48  fd_pseudo_cond:                         4
% 15.25/2.48  ac_symbols:                             1
% 15.25/2.48  
% 15.25/2.48  ------ Propositional Solver
% 15.25/2.48  
% 15.25/2.48  prop_solver_calls:                      28
% 15.25/2.48  prop_fast_solver_calls:                 1192
% 15.25/2.48  smt_solver_calls:                       0
% 15.25/2.48  smt_fast_solver_calls:                  0
% 15.25/2.48  prop_num_of_clauses:                    10227
% 15.25/2.48  prop_preprocess_simplified:             17046
% 15.25/2.48  prop_fo_subsumed:                       21
% 15.25/2.48  prop_solver_time:                       0.
% 15.25/2.48  smt_solver_time:                        0.
% 15.25/2.48  smt_fast_solver_time:                   0.
% 15.25/2.48  prop_fast_solver_time:                  0.
% 15.25/2.48  prop_unsat_core_time:                   0.001
% 15.25/2.48  
% 15.25/2.48  ------ QBF
% 15.25/2.48  
% 15.25/2.48  qbf_q_res:                              0
% 15.25/2.48  qbf_num_tautologies:                    0
% 15.25/2.48  qbf_prep_cycles:                        0
% 15.25/2.48  
% 15.25/2.48  ------ BMC1
% 15.25/2.48  
% 15.25/2.48  bmc1_current_bound:                     -1
% 15.25/2.48  bmc1_last_solved_bound:                 -1
% 15.25/2.48  bmc1_unsat_core_size:                   -1
% 15.25/2.48  bmc1_unsat_core_parents_size:           -1
% 15.25/2.48  bmc1_merge_next_fun:                    0
% 15.25/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.25/2.48  
% 15.25/2.48  ------ Instantiation
% 15.25/2.48  
% 15.25/2.48  inst_num_of_clauses:                    1753
% 15.25/2.48  inst_num_in_passive:                    420
% 15.25/2.48  inst_num_in_active:                     546
% 15.25/2.48  inst_num_in_unprocessed:                787
% 15.25/2.48  inst_num_of_loops:                      740
% 15.25/2.48  inst_num_of_learning_restarts:          0
% 15.25/2.48  inst_num_moves_active_passive:          192
% 15.25/2.48  inst_lit_activity:                      0
% 15.25/2.48  inst_lit_activity_moves:                0
% 15.25/2.48  inst_num_tautologies:                   0
% 15.25/2.48  inst_num_prop_implied:                  0
% 15.25/2.48  inst_num_existing_simplified:           0
% 15.25/2.48  inst_num_eq_res_simplified:             0
% 15.25/2.48  inst_num_child_elim:                    0
% 15.25/2.48  inst_num_of_dismatching_blockings:      1108
% 15.25/2.48  inst_num_of_non_proper_insts:           1585
% 15.25/2.48  inst_num_of_duplicates:                 0
% 15.25/2.48  inst_inst_num_from_inst_to_res:         0
% 15.25/2.48  inst_dismatching_checking_time:         0.
% 15.25/2.48  
% 15.25/2.48  ------ Resolution
% 15.25/2.48  
% 15.25/2.48  res_num_of_clauses:                     0
% 15.25/2.48  res_num_in_passive:                     0
% 15.25/2.48  res_num_in_active:                      0
% 15.25/2.48  res_num_of_loops:                       197
% 15.25/2.48  res_forward_subset_subsumed:            73
% 15.25/2.48  res_backward_subset_subsumed:           0
% 15.25/2.48  res_forward_subsumed:                   0
% 15.25/2.48  res_backward_subsumed:                  0
% 15.25/2.48  res_forward_subsumption_resolution:     0
% 15.25/2.48  res_backward_subsumption_resolution:    0
% 15.25/2.48  res_clause_to_clause_subsumption:       287863
% 15.25/2.48  res_orphan_elimination:                 0
% 15.25/2.48  res_tautology_del:                      52
% 15.25/2.48  res_num_eq_res_simplified:              0
% 15.25/2.48  res_num_sel_changes:                    0
% 15.25/2.48  res_moves_from_active_to_pass:          0
% 15.25/2.48  
% 15.25/2.48  ------ Superposition
% 15.25/2.48  
% 15.25/2.48  sup_time_total:                         0.
% 15.25/2.48  sup_time_generating:                    0.
% 15.25/2.48  sup_time_sim_full:                      0.
% 15.25/2.48  sup_time_sim_immed:                     0.
% 15.25/2.48  
% 15.25/2.48  sup_num_of_clauses:                     3306
% 15.25/2.48  sup_num_in_active:                      102
% 15.25/2.48  sup_num_in_passive:                     3204
% 15.25/2.48  sup_num_of_loops:                       147
% 15.25/2.48  sup_fw_superposition:                   8807
% 15.25/2.48  sup_bw_superposition:                   6758
% 15.25/2.48  sup_immediate_simplified:               4407
% 15.25/2.48  sup_given_eliminated:                   9
% 15.25/2.48  comparisons_done:                       0
% 15.25/2.48  comparisons_avoided:                    0
% 15.25/2.48  
% 15.25/2.48  ------ Simplifications
% 15.25/2.48  
% 15.25/2.48  
% 15.25/2.48  sim_fw_subset_subsumed:                 14
% 15.25/2.48  sim_bw_subset_subsumed:                 5
% 15.25/2.48  sim_fw_subsumed:                        248
% 15.25/2.48  sim_bw_subsumed:                        1
% 15.25/2.48  sim_fw_subsumption_res:                 2
% 15.25/2.48  sim_bw_subsumption_res:                 0
% 15.25/2.48  sim_tautology_del:                      19
% 15.25/2.48  sim_eq_tautology_del:                   335
% 15.25/2.48  sim_eq_res_simp:                        0
% 15.25/2.48  sim_fw_demodulated:                     1972
% 15.25/2.48  sim_bw_demodulated:                     462
% 15.25/2.48  sim_light_normalised:                   1689
% 15.25/2.48  sim_joinable_taut:                      1043
% 15.25/2.48  sim_joinable_simp:                      0
% 15.25/2.48  sim_ac_normalised:                      0
% 15.25/2.48  sim_smt_subsumption:                    0
% 15.25/2.48  
%------------------------------------------------------------------------------
