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
% DateTime   : Thu Dec  3 11:40:19 EST 2020

% Result     : Theorem 23.64s
% Output     : CNFRefutation 23.64s
% Verified   : 
% Statistics : Number of formulae       :  224 (1459 expanded)
%              Number of clauses        :  113 ( 626 expanded)
%              Number of leaves         :   35 ( 341 expanded)
%              Depth                    :   22
%              Number of atoms          :  482 (2617 expanded)
%              Number of equality atoms :  240 (1488 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
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

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f64,plain,(
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

fof(f65,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f63,f64])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f163,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f81,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f133,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f36,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f55,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f54])).

fof(f84,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK10
      & r1_tarski(sK10,k3_subset_1(sK9,sK11))
      & r1_tarski(sK10,sK11)
      & m1_subset_1(sK11,k1_zfmisc_1(sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
    ( k1_xboole_0 != sK10
    & r1_tarski(sK10,k3_subset_1(sK9,sK11))
    & r1_tarski(sK10,sK11)
    & m1_subset_1(sK11,k1_zfmisc_1(sK9)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f55,f84])).

fof(f145,plain,(
    r1_tarski(sK10,k3_subset_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f85])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f137,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f143,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(sK9)) ),
    inference(cnf_transformation,[],[f85])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f146,plain,(
    k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f85])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f162,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f95])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f144,plain,(
    r1_tarski(sK10,sK11) ),
    inference(cnf_transformation,[],[f85])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f141,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f31,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f136,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f141,f136])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f164,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f29,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f131,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f26,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f126,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f38])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f120,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f147,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f108,f109])).

fof(f148,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f107,f147])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f106,f148])).

fof(f150,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f105,f149])).

fof(f151,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f104,f150])).

fof(f152,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f120,f151])).

fof(f156,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f89,f152])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f79])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f153,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f102,f152])).

fof(f154,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f91,f153])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f155,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f103,f151])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ) ),
    inference(definition_unfolding,[],[f128,f154,f155])).

fof(f169,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(equality_resolution,[],[f158])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_17,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f163])).

cnf(c_1794,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_38,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1775,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_13944,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1775])).

cnf(c_47,negated_conjecture,
    ( r1_tarski(sK10,k3_subset_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_1767,plain,
    ( r1_tarski(sK10,k3_subset_1(sK9,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1773,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(sK9)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_1765,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_1772,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_16999,plain,
    ( k3_subset_1(sK9,k3_subset_1(sK9,sK11)) = sK11 ),
    inference(superposition,[status(thm)],[c_1765,c_1772])).

cnf(c_43,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_1770,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_17313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | m1_subset_1(k3_subset_1(sK9,sK11),k1_zfmisc_1(sK9)) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK9,sK11)) != iProver_top
    | r1_tarski(sK11,k3_subset_1(sK9,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16999,c_1770])).

cnf(c_17757,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(sK9)) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK9,sK11)) != iProver_top
    | r1_tarski(sK11,k3_subset_1(sK9,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_17313])).

cnf(c_50,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_19885,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK9,sK11)) != iProver_top
    | r1_tarski(sK11,k3_subset_1(sK9,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17757,c_50])).

cnf(c_19893,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top
    | r1_tarski(sK11,k3_subset_1(sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_19885])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1800,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_20168,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top
    | r1_tarski(k3_subset_1(sK9,sK10),X0) != iProver_top
    | r1_tarski(sK11,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19893,c_1800])).

cnf(c_46,negated_conjecture,
    ( k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_144,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_938,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1863,plain,
    ( sK10 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_1864,plain,
    ( sK10 != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_48,negated_conjecture,
    ( r1_tarski(sK10,sK11) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_1766,plain,
    ( r1_tarski(sK10,sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_20163,plain,
    ( r1_tarski(sK11,X0) != iProver_top
    | r1_tarski(sK10,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_1800])).

cnf(c_20378,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top
    | r1_tarski(sK10,k3_subset_1(sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19893,c_20163])).

cnf(c_45,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f161])).

cnf(c_1768,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_20778,plain,
    ( sK10 = k1_xboole_0
    | m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20378,c_1768])).

cnf(c_21331,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20168,c_46,c_9,c_144,c_1864,c_20778])).

cnf(c_59496,plain,
    ( r1_tarski(sK10,sK9) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13944,c_21331])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1774,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_10560,plain,
    ( r2_hidden(sK11,k1_zfmisc_1(sK9)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1774])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_1793,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10931,plain,
    ( r1_tarski(sK11,sK9) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10560,c_1793])).

cnf(c_20376,plain,
    ( r1_tarski(sK10,sK9) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10931,c_20163])).

cnf(c_59733,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_59496,c_20376])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1798,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_59740,plain,
    ( k1_zfmisc_1(sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_59733,c_1798])).

cnf(c_35,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_60159,plain,
    ( k3_tarski(k1_xboole_0) = sK9 ),
    inference(superposition,[status(thm)],[c_59740,c_35])).

cnf(c_30,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_60182,plain,
    ( sK9 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_60159,c_30])).

cnf(c_60189,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_60182,c_59740])).

cnf(c_3,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f156])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) ),
    inference(cnf_transformation,[],[f169])).

cnf(c_1780,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2609,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_14,c_13])).

cnf(c_3337,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_13,c_2609])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2608,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_13])).

cnf(c_3077,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_2608,c_13])).

cnf(c_3079,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_3077,c_2608])).

cnf(c_3338,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_2609])).

cnf(c_3351,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3338,c_7])).

cnf(c_3366,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(demodulation,[status(thm)],[c_3337,c_3079,c_3351])).

cnf(c_2611,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_14])).

cnf(c_3352,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_3351,c_2609])).

cnf(c_3483,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2611,c_3352])).

cnf(c_3491,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_3483,c_7])).

cnf(c_3573,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3491,c_3352])).

cnf(c_3579,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_3573])).

cnf(c_4361,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_3366,c_3579])).

cnf(c_4195,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_3366,c_3366])).

cnf(c_4402,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
    inference(demodulation,[status(thm)],[c_4361,c_3079,c_4195])).

cnf(c_3571,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_3352,c_3491])).

cnf(c_3826,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_3571,c_13])).

cnf(c_3568,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_13,c_3491])).

cnf(c_3642,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_3352,c_3568])).

cnf(c_6361,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2)) = k5_xboole_0(k5_xboole_0(X3,X1),X0) ),
    inference(superposition,[status(thm)],[c_3826,c_3642])).

cnf(c_3652,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_3568,c_3568])).

cnf(c_5995,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X3) ),
    inference(superposition,[status(thm)],[c_3579,c_3652])).

cnf(c_5491,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X3,X2),X0) ),
    inference(superposition,[status(thm)],[c_3642,c_3642])).

cnf(c_3574,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_3491,c_13])).

cnf(c_3581,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_3574,c_3079])).

cnf(c_5226,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3581,c_3579])).

cnf(c_5493,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5491,c_5226])).

cnf(c_3643,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_3491,c_3568])).

cnf(c_5560,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2)) = k5_xboole_0(X3,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3579,c_3643])).

cnf(c_6128,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2)) = k5_xboole_0(X1,k5_xboole_0(X3,X0)) ),
    inference(demodulation,[status(thm)],[c_5995,c_5493,c_5560])).

cnf(c_6380,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_6361,c_6128])).

cnf(c_40045,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1780,c_4402,c_6380])).

cnf(c_40051,plain,
    ( r2_hidden(X0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_40045])).

cnf(c_40052,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_40051,c_14])).

cnf(c_40057,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40052])).

cnf(c_939,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4440,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X2),X3)
    | X3 != X1
    | k1_zfmisc_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_4441,plain,
    ( X0 != X1
    | k1_zfmisc_1(X2) != X3
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4440])).

cnf(c_4443,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4441])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2170,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X2))
    | ~ r1_tarski(k1_zfmisc_1(X2),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2171,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X2)) != iProver_top
    | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2170])).

cnf(c_2173,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_146,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_148,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_124,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_126,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60189,c_40057,c_4443,c_2173,c_148,c_144,c_9,c_126])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:03:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.64/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.64/3.50  
% 23.64/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.64/3.50  
% 23.64/3.50  ------  iProver source info
% 23.64/3.50  
% 23.64/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.64/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.64/3.50  git: non_committed_changes: false
% 23.64/3.50  git: last_make_outside_of_git: false
% 23.64/3.50  
% 23.64/3.50  ------ 
% 23.64/3.50  
% 23.64/3.50  ------ Input Options
% 23.64/3.50  
% 23.64/3.50  --out_options                           all
% 23.64/3.50  --tptp_safe_out                         true
% 23.64/3.50  --problem_path                          ""
% 23.64/3.50  --include_path                          ""
% 23.64/3.50  --clausifier                            res/vclausify_rel
% 23.64/3.50  --clausifier_options                    ""
% 23.64/3.50  --stdin                                 false
% 23.64/3.50  --stats_out                             all
% 23.64/3.50  
% 23.64/3.50  ------ General Options
% 23.64/3.50  
% 23.64/3.50  --fof                                   false
% 23.64/3.50  --time_out_real                         305.
% 23.64/3.50  --time_out_virtual                      -1.
% 23.64/3.50  --symbol_type_check                     false
% 23.64/3.50  --clausify_out                          false
% 23.64/3.50  --sig_cnt_out                           false
% 23.64/3.50  --trig_cnt_out                          false
% 23.64/3.50  --trig_cnt_out_tolerance                1.
% 23.64/3.50  --trig_cnt_out_sk_spl                   false
% 23.64/3.50  --abstr_cl_out                          false
% 23.64/3.50  
% 23.64/3.50  ------ Global Options
% 23.64/3.50  
% 23.64/3.50  --schedule                              default
% 23.64/3.50  --add_important_lit                     false
% 23.64/3.50  --prop_solver_per_cl                    1000
% 23.64/3.50  --min_unsat_core                        false
% 23.64/3.50  --soft_assumptions                      false
% 23.64/3.50  --soft_lemma_size                       3
% 23.64/3.50  --prop_impl_unit_size                   0
% 23.64/3.50  --prop_impl_unit                        []
% 23.64/3.50  --share_sel_clauses                     true
% 23.64/3.50  --reset_solvers                         false
% 23.64/3.50  --bc_imp_inh                            [conj_cone]
% 23.64/3.50  --conj_cone_tolerance                   3.
% 23.64/3.50  --extra_neg_conj                        none
% 23.64/3.50  --large_theory_mode                     true
% 23.64/3.50  --prolific_symb_bound                   200
% 23.64/3.50  --lt_threshold                          2000
% 23.64/3.50  --clause_weak_htbl                      true
% 23.64/3.50  --gc_record_bc_elim                     false
% 23.64/3.50  
% 23.64/3.50  ------ Preprocessing Options
% 23.64/3.50  
% 23.64/3.50  --preprocessing_flag                    true
% 23.64/3.50  --time_out_prep_mult                    0.1
% 23.64/3.50  --splitting_mode                        input
% 23.64/3.50  --splitting_grd                         true
% 23.64/3.50  --splitting_cvd                         false
% 23.64/3.50  --splitting_cvd_svl                     false
% 23.64/3.50  --splitting_nvd                         32
% 23.64/3.50  --sub_typing                            true
% 23.64/3.50  --prep_gs_sim                           true
% 23.64/3.50  --prep_unflatten                        true
% 23.64/3.50  --prep_res_sim                          true
% 23.64/3.50  --prep_upred                            true
% 23.64/3.50  --prep_sem_filter                       exhaustive
% 23.64/3.50  --prep_sem_filter_out                   false
% 23.64/3.50  --pred_elim                             true
% 23.64/3.50  --res_sim_input                         true
% 23.64/3.50  --eq_ax_congr_red                       true
% 23.64/3.50  --pure_diseq_elim                       true
% 23.64/3.50  --brand_transform                       false
% 23.64/3.50  --non_eq_to_eq                          false
% 23.64/3.50  --prep_def_merge                        true
% 23.64/3.50  --prep_def_merge_prop_impl              false
% 23.64/3.50  --prep_def_merge_mbd                    true
% 23.64/3.50  --prep_def_merge_tr_red                 false
% 23.64/3.50  --prep_def_merge_tr_cl                  false
% 23.64/3.50  --smt_preprocessing                     true
% 23.64/3.50  --smt_ac_axioms                         fast
% 23.64/3.50  --preprocessed_out                      false
% 23.64/3.50  --preprocessed_stats                    false
% 23.64/3.50  
% 23.64/3.50  ------ Abstraction refinement Options
% 23.64/3.50  
% 23.64/3.50  --abstr_ref                             []
% 23.64/3.50  --abstr_ref_prep                        false
% 23.64/3.50  --abstr_ref_until_sat                   false
% 23.64/3.50  --abstr_ref_sig_restrict                funpre
% 23.64/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.64/3.50  --abstr_ref_under                       []
% 23.64/3.50  
% 23.64/3.50  ------ SAT Options
% 23.64/3.50  
% 23.64/3.50  --sat_mode                              false
% 23.64/3.50  --sat_fm_restart_options                ""
% 23.64/3.50  --sat_gr_def                            false
% 23.64/3.50  --sat_epr_types                         true
% 23.64/3.50  --sat_non_cyclic_types                  false
% 23.64/3.50  --sat_finite_models                     false
% 23.64/3.50  --sat_fm_lemmas                         false
% 23.64/3.50  --sat_fm_prep                           false
% 23.64/3.50  --sat_fm_uc_incr                        true
% 23.64/3.50  --sat_out_model                         small
% 23.64/3.50  --sat_out_clauses                       false
% 23.64/3.50  
% 23.64/3.50  ------ QBF Options
% 23.64/3.50  
% 23.64/3.50  --qbf_mode                              false
% 23.64/3.50  --qbf_elim_univ                         false
% 23.64/3.50  --qbf_dom_inst                          none
% 23.64/3.50  --qbf_dom_pre_inst                      false
% 23.64/3.50  --qbf_sk_in                             false
% 23.64/3.50  --qbf_pred_elim                         true
% 23.64/3.50  --qbf_split                             512
% 23.64/3.50  
% 23.64/3.50  ------ BMC1 Options
% 23.64/3.50  
% 23.64/3.50  --bmc1_incremental                      false
% 23.64/3.50  --bmc1_axioms                           reachable_all
% 23.64/3.50  --bmc1_min_bound                        0
% 23.64/3.50  --bmc1_max_bound                        -1
% 23.64/3.50  --bmc1_max_bound_default                -1
% 23.64/3.50  --bmc1_symbol_reachability              true
% 23.64/3.50  --bmc1_property_lemmas                  false
% 23.64/3.50  --bmc1_k_induction                      false
% 23.64/3.50  --bmc1_non_equiv_states                 false
% 23.64/3.50  --bmc1_deadlock                         false
% 23.64/3.50  --bmc1_ucm                              false
% 23.64/3.50  --bmc1_add_unsat_core                   none
% 23.64/3.50  --bmc1_unsat_core_children              false
% 23.64/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.64/3.50  --bmc1_out_stat                         full
% 23.64/3.50  --bmc1_ground_init                      false
% 23.64/3.50  --bmc1_pre_inst_next_state              false
% 23.64/3.50  --bmc1_pre_inst_state                   false
% 23.64/3.50  --bmc1_pre_inst_reach_state             false
% 23.64/3.50  --bmc1_out_unsat_core                   false
% 23.64/3.50  --bmc1_aig_witness_out                  false
% 23.64/3.50  --bmc1_verbose                          false
% 23.64/3.50  --bmc1_dump_clauses_tptp                false
% 23.64/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.64/3.50  --bmc1_dump_file                        -
% 23.64/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.64/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.64/3.50  --bmc1_ucm_extend_mode                  1
% 23.64/3.50  --bmc1_ucm_init_mode                    2
% 23.64/3.50  --bmc1_ucm_cone_mode                    none
% 23.64/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.64/3.50  --bmc1_ucm_relax_model                  4
% 23.64/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.64/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.64/3.50  --bmc1_ucm_layered_model                none
% 23.64/3.50  --bmc1_ucm_max_lemma_size               10
% 23.64/3.50  
% 23.64/3.50  ------ AIG Options
% 23.64/3.50  
% 23.64/3.50  --aig_mode                              false
% 23.64/3.50  
% 23.64/3.50  ------ Instantiation Options
% 23.64/3.50  
% 23.64/3.50  --instantiation_flag                    true
% 23.64/3.50  --inst_sos_flag                         true
% 23.64/3.50  --inst_sos_phase                        true
% 23.64/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.64/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.64/3.50  --inst_lit_sel_side                     num_symb
% 23.64/3.50  --inst_solver_per_active                1400
% 23.64/3.50  --inst_solver_calls_frac                1.
% 23.64/3.50  --inst_passive_queue_type               priority_queues
% 23.64/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.64/3.50  --inst_passive_queues_freq              [25;2]
% 23.64/3.50  --inst_dismatching                      true
% 23.64/3.50  --inst_eager_unprocessed_to_passive     true
% 23.64/3.50  --inst_prop_sim_given                   true
% 23.64/3.50  --inst_prop_sim_new                     false
% 23.64/3.50  --inst_subs_new                         false
% 23.64/3.50  --inst_eq_res_simp                      false
% 23.64/3.50  --inst_subs_given                       false
% 23.64/3.50  --inst_orphan_elimination               true
% 23.64/3.50  --inst_learning_loop_flag               true
% 23.64/3.50  --inst_learning_start                   3000
% 23.64/3.50  --inst_learning_factor                  2
% 23.64/3.50  --inst_start_prop_sim_after_learn       3
% 23.64/3.50  --inst_sel_renew                        solver
% 23.64/3.50  --inst_lit_activity_flag                true
% 23.64/3.50  --inst_restr_to_given                   false
% 23.64/3.50  --inst_activity_threshold               500
% 23.64/3.50  --inst_out_proof                        true
% 23.64/3.50  
% 23.64/3.50  ------ Resolution Options
% 23.64/3.50  
% 23.64/3.50  --resolution_flag                       true
% 23.64/3.50  --res_lit_sel                           adaptive
% 23.64/3.50  --res_lit_sel_side                      none
% 23.64/3.50  --res_ordering                          kbo
% 23.64/3.50  --res_to_prop_solver                    active
% 23.64/3.50  --res_prop_simpl_new                    false
% 23.64/3.50  --res_prop_simpl_given                  true
% 23.64/3.50  --res_passive_queue_type                priority_queues
% 23.64/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.64/3.50  --res_passive_queues_freq               [15;5]
% 23.64/3.50  --res_forward_subs                      full
% 23.64/3.50  --res_backward_subs                     full
% 23.64/3.50  --res_forward_subs_resolution           true
% 23.64/3.50  --res_backward_subs_resolution          true
% 23.64/3.50  --res_orphan_elimination                true
% 23.64/3.50  --res_time_limit                        2.
% 23.64/3.50  --res_out_proof                         true
% 23.64/3.50  
% 23.64/3.50  ------ Superposition Options
% 23.64/3.50  
% 23.64/3.50  --superposition_flag                    true
% 23.64/3.50  --sup_passive_queue_type                priority_queues
% 23.64/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.64/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.64/3.50  --demod_completeness_check              fast
% 23.64/3.50  --demod_use_ground                      true
% 23.64/3.50  --sup_to_prop_solver                    passive
% 23.64/3.50  --sup_prop_simpl_new                    true
% 23.64/3.50  --sup_prop_simpl_given                  true
% 23.64/3.50  --sup_fun_splitting                     true
% 23.64/3.50  --sup_smt_interval                      50000
% 23.64/3.50  
% 23.64/3.50  ------ Superposition Simplification Setup
% 23.64/3.50  
% 23.64/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.64/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.64/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.64/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.64/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.64/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.64/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.64/3.50  --sup_immed_triv                        [TrivRules]
% 23.64/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.64/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.64/3.50  --sup_immed_bw_main                     []
% 23.64/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.64/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.64/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.64/3.50  --sup_input_bw                          []
% 23.64/3.50  
% 23.64/3.50  ------ Combination Options
% 23.64/3.50  
% 23.64/3.50  --comb_res_mult                         3
% 23.64/3.50  --comb_sup_mult                         2
% 23.64/3.50  --comb_inst_mult                        10
% 23.64/3.50  
% 23.64/3.50  ------ Debug Options
% 23.64/3.50  
% 23.64/3.50  --dbg_backtrace                         false
% 23.64/3.50  --dbg_dump_prop_clauses                 false
% 23.64/3.50  --dbg_dump_prop_clauses_file            -
% 23.64/3.50  --dbg_out_stat                          false
% 23.64/3.50  ------ Parsing...
% 23.64/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.64/3.50  
% 23.64/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.64/3.50  
% 23.64/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.64/3.50  
% 23.64/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.64/3.50  ------ Proving...
% 23.64/3.50  ------ Problem Properties 
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  clauses                                 48
% 23.64/3.50  conjectures                             4
% 23.64/3.50  EPR                                     12
% 23.64/3.50  Horn                                    40
% 23.64/3.50  unary                                   13
% 23.64/3.50  binary                                  17
% 23.64/3.50  lits                                    105
% 23.64/3.50  lits eq                                 19
% 23.64/3.50  fd_pure                                 0
% 23.64/3.50  fd_pseudo                               0
% 23.64/3.50  fd_cond                                 3
% 23.64/3.50  fd_pseudo_cond                          7
% 23.64/3.50  AC symbols                              0
% 23.64/3.50  
% 23.64/3.50  ------ Schedule dynamic 5 is on 
% 23.64/3.50  
% 23.64/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  ------ 
% 23.64/3.50  Current options:
% 23.64/3.50  ------ 
% 23.64/3.50  
% 23.64/3.50  ------ Input Options
% 23.64/3.50  
% 23.64/3.50  --out_options                           all
% 23.64/3.50  --tptp_safe_out                         true
% 23.64/3.50  --problem_path                          ""
% 23.64/3.50  --include_path                          ""
% 23.64/3.50  --clausifier                            res/vclausify_rel
% 23.64/3.50  --clausifier_options                    ""
% 23.64/3.50  --stdin                                 false
% 23.64/3.50  --stats_out                             all
% 23.64/3.50  
% 23.64/3.50  ------ General Options
% 23.64/3.50  
% 23.64/3.50  --fof                                   false
% 23.64/3.50  --time_out_real                         305.
% 23.64/3.50  --time_out_virtual                      -1.
% 23.64/3.50  --symbol_type_check                     false
% 23.64/3.50  --clausify_out                          false
% 23.64/3.50  --sig_cnt_out                           false
% 23.64/3.50  --trig_cnt_out                          false
% 23.64/3.50  --trig_cnt_out_tolerance                1.
% 23.64/3.50  --trig_cnt_out_sk_spl                   false
% 23.64/3.50  --abstr_cl_out                          false
% 23.64/3.50  
% 23.64/3.50  ------ Global Options
% 23.64/3.50  
% 23.64/3.50  --schedule                              default
% 23.64/3.50  --add_important_lit                     false
% 23.64/3.50  --prop_solver_per_cl                    1000
% 23.64/3.50  --min_unsat_core                        false
% 23.64/3.50  --soft_assumptions                      false
% 23.64/3.50  --soft_lemma_size                       3
% 23.64/3.50  --prop_impl_unit_size                   0
% 23.64/3.50  --prop_impl_unit                        []
% 23.64/3.50  --share_sel_clauses                     true
% 23.64/3.50  --reset_solvers                         false
% 23.64/3.50  --bc_imp_inh                            [conj_cone]
% 23.64/3.50  --conj_cone_tolerance                   3.
% 23.64/3.50  --extra_neg_conj                        none
% 23.64/3.50  --large_theory_mode                     true
% 23.64/3.50  --prolific_symb_bound                   200
% 23.64/3.50  --lt_threshold                          2000
% 23.64/3.50  --clause_weak_htbl                      true
% 23.64/3.50  --gc_record_bc_elim                     false
% 23.64/3.50  
% 23.64/3.50  ------ Preprocessing Options
% 23.64/3.50  
% 23.64/3.50  --preprocessing_flag                    true
% 23.64/3.50  --time_out_prep_mult                    0.1
% 23.64/3.50  --splitting_mode                        input
% 23.64/3.50  --splitting_grd                         true
% 23.64/3.50  --splitting_cvd                         false
% 23.64/3.50  --splitting_cvd_svl                     false
% 23.64/3.50  --splitting_nvd                         32
% 23.64/3.50  --sub_typing                            true
% 23.64/3.50  --prep_gs_sim                           true
% 23.64/3.50  --prep_unflatten                        true
% 23.64/3.50  --prep_res_sim                          true
% 23.64/3.50  --prep_upred                            true
% 23.64/3.50  --prep_sem_filter                       exhaustive
% 23.64/3.50  --prep_sem_filter_out                   false
% 23.64/3.50  --pred_elim                             true
% 23.64/3.50  --res_sim_input                         true
% 23.64/3.50  --eq_ax_congr_red                       true
% 23.64/3.50  --pure_diseq_elim                       true
% 23.64/3.50  --brand_transform                       false
% 23.64/3.50  --non_eq_to_eq                          false
% 23.64/3.50  --prep_def_merge                        true
% 23.64/3.50  --prep_def_merge_prop_impl              false
% 23.64/3.50  --prep_def_merge_mbd                    true
% 23.64/3.50  --prep_def_merge_tr_red                 false
% 23.64/3.50  --prep_def_merge_tr_cl                  false
% 23.64/3.50  --smt_preprocessing                     true
% 23.64/3.50  --smt_ac_axioms                         fast
% 23.64/3.50  --preprocessed_out                      false
% 23.64/3.50  --preprocessed_stats                    false
% 23.64/3.50  
% 23.64/3.50  ------ Abstraction refinement Options
% 23.64/3.50  
% 23.64/3.50  --abstr_ref                             []
% 23.64/3.50  --abstr_ref_prep                        false
% 23.64/3.50  --abstr_ref_until_sat                   false
% 23.64/3.50  --abstr_ref_sig_restrict                funpre
% 23.64/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.64/3.50  --abstr_ref_under                       []
% 23.64/3.50  
% 23.64/3.50  ------ SAT Options
% 23.64/3.50  
% 23.64/3.50  --sat_mode                              false
% 23.64/3.50  --sat_fm_restart_options                ""
% 23.64/3.50  --sat_gr_def                            false
% 23.64/3.50  --sat_epr_types                         true
% 23.64/3.50  --sat_non_cyclic_types                  false
% 23.64/3.50  --sat_finite_models                     false
% 23.64/3.50  --sat_fm_lemmas                         false
% 23.64/3.50  --sat_fm_prep                           false
% 23.64/3.50  --sat_fm_uc_incr                        true
% 23.64/3.50  --sat_out_model                         small
% 23.64/3.50  --sat_out_clauses                       false
% 23.64/3.50  
% 23.64/3.50  ------ QBF Options
% 23.64/3.50  
% 23.64/3.50  --qbf_mode                              false
% 23.64/3.50  --qbf_elim_univ                         false
% 23.64/3.50  --qbf_dom_inst                          none
% 23.64/3.50  --qbf_dom_pre_inst                      false
% 23.64/3.50  --qbf_sk_in                             false
% 23.64/3.50  --qbf_pred_elim                         true
% 23.64/3.50  --qbf_split                             512
% 23.64/3.50  
% 23.64/3.50  ------ BMC1 Options
% 23.64/3.50  
% 23.64/3.50  --bmc1_incremental                      false
% 23.64/3.50  --bmc1_axioms                           reachable_all
% 23.64/3.50  --bmc1_min_bound                        0
% 23.64/3.50  --bmc1_max_bound                        -1
% 23.64/3.50  --bmc1_max_bound_default                -1
% 23.64/3.50  --bmc1_symbol_reachability              true
% 23.64/3.50  --bmc1_property_lemmas                  false
% 23.64/3.50  --bmc1_k_induction                      false
% 23.64/3.50  --bmc1_non_equiv_states                 false
% 23.64/3.50  --bmc1_deadlock                         false
% 23.64/3.50  --bmc1_ucm                              false
% 23.64/3.50  --bmc1_add_unsat_core                   none
% 23.64/3.50  --bmc1_unsat_core_children              false
% 23.64/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.64/3.50  --bmc1_out_stat                         full
% 23.64/3.50  --bmc1_ground_init                      false
% 23.64/3.50  --bmc1_pre_inst_next_state              false
% 23.64/3.50  --bmc1_pre_inst_state                   false
% 23.64/3.50  --bmc1_pre_inst_reach_state             false
% 23.64/3.50  --bmc1_out_unsat_core                   false
% 23.64/3.50  --bmc1_aig_witness_out                  false
% 23.64/3.50  --bmc1_verbose                          false
% 23.64/3.50  --bmc1_dump_clauses_tptp                false
% 23.64/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.64/3.50  --bmc1_dump_file                        -
% 23.64/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.64/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.64/3.50  --bmc1_ucm_extend_mode                  1
% 23.64/3.50  --bmc1_ucm_init_mode                    2
% 23.64/3.50  --bmc1_ucm_cone_mode                    none
% 23.64/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.64/3.50  --bmc1_ucm_relax_model                  4
% 23.64/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.64/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.64/3.50  --bmc1_ucm_layered_model                none
% 23.64/3.50  --bmc1_ucm_max_lemma_size               10
% 23.64/3.50  
% 23.64/3.50  ------ AIG Options
% 23.64/3.50  
% 23.64/3.50  --aig_mode                              false
% 23.64/3.50  
% 23.64/3.50  ------ Instantiation Options
% 23.64/3.50  
% 23.64/3.50  --instantiation_flag                    true
% 23.64/3.50  --inst_sos_flag                         true
% 23.64/3.50  --inst_sos_phase                        true
% 23.64/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.64/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.64/3.50  --inst_lit_sel_side                     none
% 23.64/3.50  --inst_solver_per_active                1400
% 23.64/3.50  --inst_solver_calls_frac                1.
% 23.64/3.50  --inst_passive_queue_type               priority_queues
% 23.64/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.64/3.50  --inst_passive_queues_freq              [25;2]
% 23.64/3.50  --inst_dismatching                      true
% 23.64/3.50  --inst_eager_unprocessed_to_passive     true
% 23.64/3.50  --inst_prop_sim_given                   true
% 23.64/3.50  --inst_prop_sim_new                     false
% 23.64/3.50  --inst_subs_new                         false
% 23.64/3.50  --inst_eq_res_simp                      false
% 23.64/3.50  --inst_subs_given                       false
% 23.64/3.50  --inst_orphan_elimination               true
% 23.64/3.50  --inst_learning_loop_flag               true
% 23.64/3.50  --inst_learning_start                   3000
% 23.64/3.50  --inst_learning_factor                  2
% 23.64/3.50  --inst_start_prop_sim_after_learn       3
% 23.64/3.50  --inst_sel_renew                        solver
% 23.64/3.50  --inst_lit_activity_flag                true
% 23.64/3.50  --inst_restr_to_given                   false
% 23.64/3.50  --inst_activity_threshold               500
% 23.64/3.50  --inst_out_proof                        true
% 23.64/3.50  
% 23.64/3.50  ------ Resolution Options
% 23.64/3.50  
% 23.64/3.50  --resolution_flag                       false
% 23.64/3.50  --res_lit_sel                           adaptive
% 23.64/3.50  --res_lit_sel_side                      none
% 23.64/3.50  --res_ordering                          kbo
% 23.64/3.50  --res_to_prop_solver                    active
% 23.64/3.50  --res_prop_simpl_new                    false
% 23.64/3.50  --res_prop_simpl_given                  true
% 23.64/3.50  --res_passive_queue_type                priority_queues
% 23.64/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.64/3.50  --res_passive_queues_freq               [15;5]
% 23.64/3.50  --res_forward_subs                      full
% 23.64/3.50  --res_backward_subs                     full
% 23.64/3.50  --res_forward_subs_resolution           true
% 23.64/3.50  --res_backward_subs_resolution          true
% 23.64/3.50  --res_orphan_elimination                true
% 23.64/3.50  --res_time_limit                        2.
% 23.64/3.50  --res_out_proof                         true
% 23.64/3.50  
% 23.64/3.50  ------ Superposition Options
% 23.64/3.50  
% 23.64/3.50  --superposition_flag                    true
% 23.64/3.50  --sup_passive_queue_type                priority_queues
% 23.64/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.64/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.64/3.50  --demod_completeness_check              fast
% 23.64/3.50  --demod_use_ground                      true
% 23.64/3.50  --sup_to_prop_solver                    passive
% 23.64/3.50  --sup_prop_simpl_new                    true
% 23.64/3.50  --sup_prop_simpl_given                  true
% 23.64/3.50  --sup_fun_splitting                     true
% 23.64/3.50  --sup_smt_interval                      50000
% 23.64/3.50  
% 23.64/3.50  ------ Superposition Simplification Setup
% 23.64/3.50  
% 23.64/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.64/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.64/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.64/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.64/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.64/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.64/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.64/3.50  --sup_immed_triv                        [TrivRules]
% 23.64/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.64/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.64/3.50  --sup_immed_bw_main                     []
% 23.64/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.64/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.64/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.64/3.50  --sup_input_bw                          []
% 23.64/3.50  
% 23.64/3.50  ------ Combination Options
% 23.64/3.50  
% 23.64/3.50  --comb_res_mult                         3
% 23.64/3.50  --comb_sup_mult                         2
% 23.64/3.50  --comb_inst_mult                        10
% 23.64/3.50  
% 23.64/3.50  ------ Debug Options
% 23.64/3.50  
% 23.64/3.50  --dbg_backtrace                         false
% 23.64/3.50  --dbg_dump_prop_clauses                 false
% 23.64/3.50  --dbg_dump_prop_clauses_file            -
% 23.64/3.50  --dbg_out_stat                          false
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  ------ Proving...
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  % SZS status Theorem for theBenchmark.p
% 23.64/3.50  
% 23.64/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.64/3.50  
% 23.64/3.50  fof(f22,axiom,(
% 23.64/3.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f62,plain,(
% 23.64/3.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.64/3.50    inference(nnf_transformation,[],[f22])).
% 23.64/3.50  
% 23.64/3.50  fof(f63,plain,(
% 23.64/3.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.64/3.50    inference(rectify,[],[f62])).
% 23.64/3.50  
% 23.64/3.50  fof(f64,plain,(
% 23.64/3.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 23.64/3.50    introduced(choice_axiom,[])).
% 23.64/3.50  
% 23.64/3.50  fof(f65,plain,(
% 23.64/3.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.64/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f63,f64])).
% 23.64/3.50  
% 23.64/3.50  fof(f111,plain,(
% 23.64/3.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 23.64/3.50    inference(cnf_transformation,[],[f65])).
% 23.64/3.50  
% 23.64/3.50  fof(f163,plain,(
% 23.64/3.50    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 23.64/3.50    inference(equality_resolution,[],[f111])).
% 23.64/3.50  
% 23.64/3.50  fof(f30,axiom,(
% 23.64/3.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f49,plain,(
% 23.64/3.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 23.64/3.50    inference(ennf_transformation,[],[f30])).
% 23.64/3.50  
% 23.64/3.50  fof(f81,plain,(
% 23.64/3.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 23.64/3.50    inference(nnf_transformation,[],[f49])).
% 23.64/3.50  
% 23.64/3.50  fof(f133,plain,(
% 23.64/3.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f81])).
% 23.64/3.50  
% 23.64/3.50  fof(f36,conjecture,(
% 23.64/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f37,negated_conjecture,(
% 23.64/3.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 23.64/3.50    inference(negated_conjecture,[],[f36])).
% 23.64/3.50  
% 23.64/3.50  fof(f54,plain,(
% 23.64/3.50    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 23.64/3.50    inference(ennf_transformation,[],[f37])).
% 23.64/3.50  
% 23.64/3.50  fof(f55,plain,(
% 23.64/3.50    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 23.64/3.50    inference(flattening,[],[f54])).
% 23.64/3.50  
% 23.64/3.50  fof(f84,plain,(
% 23.64/3.50    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK10 & r1_tarski(sK10,k3_subset_1(sK9,sK11)) & r1_tarski(sK10,sK11) & m1_subset_1(sK11,k1_zfmisc_1(sK9)))),
% 23.64/3.50    introduced(choice_axiom,[])).
% 23.64/3.50  
% 23.64/3.50  fof(f85,plain,(
% 23.64/3.50    k1_xboole_0 != sK10 & r1_tarski(sK10,k3_subset_1(sK9,sK11)) & r1_tarski(sK10,sK11) & m1_subset_1(sK11,k1_zfmisc_1(sK9))),
% 23.64/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f55,f84])).
% 23.64/3.50  
% 23.64/3.50  fof(f145,plain,(
% 23.64/3.50    r1_tarski(sK10,k3_subset_1(sK9,sK11))),
% 23.64/3.50    inference(cnf_transformation,[],[f85])).
% 23.64/3.50  
% 23.64/3.50  fof(f32,axiom,(
% 23.64/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f50,plain,(
% 23.64/3.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.64/3.50    inference(ennf_transformation,[],[f32])).
% 23.64/3.50  
% 23.64/3.50  fof(f137,plain,(
% 23.64/3.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f50])).
% 23.64/3.50  
% 23.64/3.50  fof(f143,plain,(
% 23.64/3.50    m1_subset_1(sK11,k1_zfmisc_1(sK9))),
% 23.64/3.50    inference(cnf_transformation,[],[f85])).
% 23.64/3.50  
% 23.64/3.50  fof(f33,axiom,(
% 23.64/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f51,plain,(
% 23.64/3.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.64/3.50    inference(ennf_transformation,[],[f33])).
% 23.64/3.50  
% 23.64/3.50  fof(f138,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f51])).
% 23.64/3.50  
% 23.64/3.50  fof(f34,axiom,(
% 23.64/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f52,plain,(
% 23.64/3.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.64/3.50    inference(ennf_transformation,[],[f34])).
% 23.64/3.50  
% 23.64/3.50  fof(f82,plain,(
% 23.64/3.50    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.64/3.50    inference(nnf_transformation,[],[f52])).
% 23.64/3.50  
% 23.64/3.50  fof(f139,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f82])).
% 23.64/3.50  
% 23.64/3.50  fof(f5,axiom,(
% 23.64/3.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f41,plain,(
% 23.64/3.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 23.64/3.50    inference(ennf_transformation,[],[f5])).
% 23.64/3.50  
% 23.64/3.50  fof(f42,plain,(
% 23.64/3.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 23.64/3.50    inference(flattening,[],[f41])).
% 23.64/3.50  
% 23.64/3.50  fof(f92,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f42])).
% 23.64/3.50  
% 23.64/3.50  fof(f146,plain,(
% 23.64/3.50    k1_xboole_0 != sK10),
% 23.64/3.50    inference(cnf_transformation,[],[f85])).
% 23.64/3.50  
% 23.64/3.50  fof(f8,axiom,(
% 23.64/3.50    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f43,plain,(
% 23.64/3.50    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 23.64/3.50    inference(ennf_transformation,[],[f8])).
% 23.64/3.50  
% 23.64/3.50  fof(f95,plain,(
% 23.64/3.50    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f43])).
% 23.64/3.50  
% 23.64/3.50  fof(f162,plain,(
% 23.64/3.50    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 23.64/3.50    inference(equality_resolution,[],[f95])).
% 23.64/3.50  
% 23.64/3.50  fof(f96,plain,(
% 23.64/3.50    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 23.64/3.50    inference(cnf_transformation,[],[f43])).
% 23.64/3.50  
% 23.64/3.50  fof(f144,plain,(
% 23.64/3.50    r1_tarski(sK10,sK11)),
% 23.64/3.50    inference(cnf_transformation,[],[f85])).
% 23.64/3.50  
% 23.64/3.50  fof(f35,axiom,(
% 23.64/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f53,plain,(
% 23.64/3.50    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.64/3.50    inference(ennf_transformation,[],[f35])).
% 23.64/3.50  
% 23.64/3.50  fof(f83,plain,(
% 23.64/3.50    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.64/3.50    inference(nnf_transformation,[],[f53])).
% 23.64/3.50  
% 23.64/3.50  fof(f141,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f83])).
% 23.64/3.50  
% 23.64/3.50  fof(f31,axiom,(
% 23.64/3.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f136,plain,(
% 23.64/3.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f31])).
% 23.64/3.50  
% 23.64/3.50  fof(f161,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.64/3.50    inference(definition_unfolding,[],[f141,f136])).
% 23.64/3.50  
% 23.64/3.50  fof(f132,plain,(
% 23.64/3.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f81])).
% 23.64/3.50  
% 23.64/3.50  fof(f110,plain,(
% 23.64/3.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 23.64/3.50    inference(cnf_transformation,[],[f65])).
% 23.64/3.50  
% 23.64/3.50  fof(f164,plain,(
% 23.64/3.50    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 23.64/3.50    inference(equality_resolution,[],[f110])).
% 23.64/3.50  
% 23.64/3.50  fof(f10,axiom,(
% 23.64/3.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f46,plain,(
% 23.64/3.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 23.64/3.50    inference(ennf_transformation,[],[f10])).
% 23.64/3.50  
% 23.64/3.50  fof(f98,plain,(
% 23.64/3.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f46])).
% 23.64/3.50  
% 23.64/3.50  fof(f29,axiom,(
% 23.64/3.50    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f131,plain,(
% 23.64/3.50    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 23.64/3.50    inference(cnf_transformation,[],[f29])).
% 23.64/3.50  
% 23.64/3.50  fof(f26,axiom,(
% 23.64/3.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f126,plain,(
% 23.64/3.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 23.64/3.50    inference(cnf_transformation,[],[f26])).
% 23.64/3.50  
% 23.64/3.50  fof(f2,axiom,(
% 23.64/3.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f38,plain,(
% 23.64/3.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 23.64/3.50    inference(rectify,[],[f2])).
% 23.64/3.50  
% 23.64/3.50  fof(f89,plain,(
% 23.64/3.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 23.64/3.50    inference(cnf_transformation,[],[f38])).
% 23.64/3.50  
% 23.64/3.50  fof(f24,axiom,(
% 23.64/3.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f120,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f24])).
% 23.64/3.50  
% 23.64/3.50  fof(f16,axiom,(
% 23.64/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f104,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f16])).
% 23.64/3.50  
% 23.64/3.50  fof(f17,axiom,(
% 23.64/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f105,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f17])).
% 23.64/3.50  
% 23.64/3.50  fof(f18,axiom,(
% 23.64/3.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f106,plain,(
% 23.64/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f18])).
% 23.64/3.50  
% 23.64/3.50  fof(f19,axiom,(
% 23.64/3.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f107,plain,(
% 23.64/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f19])).
% 23.64/3.50  
% 23.64/3.50  fof(f20,axiom,(
% 23.64/3.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f108,plain,(
% 23.64/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f20])).
% 23.64/3.50  
% 23.64/3.50  fof(f21,axiom,(
% 23.64/3.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f109,plain,(
% 23.64/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f21])).
% 23.64/3.50  
% 23.64/3.50  fof(f147,plain,(
% 23.64/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 23.64/3.50    inference(definition_unfolding,[],[f108,f109])).
% 23.64/3.50  
% 23.64/3.50  fof(f148,plain,(
% 23.64/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 23.64/3.50    inference(definition_unfolding,[],[f107,f147])).
% 23.64/3.50  
% 23.64/3.50  fof(f149,plain,(
% 23.64/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 23.64/3.50    inference(definition_unfolding,[],[f106,f148])).
% 23.64/3.50  
% 23.64/3.50  fof(f150,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 23.64/3.50    inference(definition_unfolding,[],[f105,f149])).
% 23.64/3.50  
% 23.64/3.50  fof(f151,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 23.64/3.50    inference(definition_unfolding,[],[f104,f150])).
% 23.64/3.50  
% 23.64/3.50  fof(f152,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 23.64/3.50    inference(definition_unfolding,[],[f120,f151])).
% 23.64/3.50  
% 23.64/3.50  fof(f156,plain,(
% 23.64/3.50    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 23.64/3.50    inference(definition_unfolding,[],[f89,f152])).
% 23.64/3.50  
% 23.64/3.50  fof(f27,axiom,(
% 23.64/3.50    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f79,plain,(
% 23.64/3.50    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 23.64/3.50    inference(nnf_transformation,[],[f27])).
% 23.64/3.50  
% 23.64/3.50  fof(f80,plain,(
% 23.64/3.50    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 23.64/3.50    inference(flattening,[],[f79])).
% 23.64/3.50  
% 23.64/3.50  fof(f128,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f80])).
% 23.64/3.50  
% 23.64/3.50  fof(f4,axiom,(
% 23.64/3.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f91,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f4])).
% 23.64/3.50  
% 23.64/3.50  fof(f14,axiom,(
% 23.64/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f102,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 23.64/3.50    inference(cnf_transformation,[],[f14])).
% 23.64/3.50  
% 23.64/3.50  fof(f153,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 23.64/3.50    inference(definition_unfolding,[],[f102,f152])).
% 23.64/3.50  
% 23.64/3.50  fof(f154,plain,(
% 23.64/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 23.64/3.50    inference(definition_unfolding,[],[f91,f153])).
% 23.64/3.50  
% 23.64/3.50  fof(f15,axiom,(
% 23.64/3.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f103,plain,(
% 23.64/3.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f15])).
% 23.64/3.50  
% 23.64/3.50  fof(f155,plain,(
% 23.64/3.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 23.64/3.50    inference(definition_unfolding,[],[f103,f151])).
% 23.64/3.50  
% 23.64/3.50  fof(f158,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 23.64/3.50    inference(definition_unfolding,[],[f128,f154,f155])).
% 23.64/3.50  
% 23.64/3.50  fof(f169,plain,(
% 23.64/3.50    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 23.64/3.50    inference(equality_resolution,[],[f158])).
% 23.64/3.50  
% 23.64/3.50  fof(f12,axiom,(
% 23.64/3.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f100,plain,(
% 23.64/3.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f12])).
% 23.64/3.50  
% 23.64/3.50  fof(f13,axiom,(
% 23.64/3.50    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f101,plain,(
% 23.64/3.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f13])).
% 23.64/3.50  
% 23.64/3.50  fof(f7,axiom,(
% 23.64/3.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f94,plain,(
% 23.64/3.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.64/3.50    inference(cnf_transformation,[],[f7])).
% 23.64/3.50  
% 23.64/3.50  fof(f1,axiom,(
% 23.64/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f39,plain,(
% 23.64/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.64/3.50    inference(ennf_transformation,[],[f1])).
% 23.64/3.50  
% 23.64/3.50  fof(f56,plain,(
% 23.64/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.64/3.50    inference(nnf_transformation,[],[f39])).
% 23.64/3.50  
% 23.64/3.50  fof(f57,plain,(
% 23.64/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.64/3.50    inference(rectify,[],[f56])).
% 23.64/3.50  
% 23.64/3.50  fof(f58,plain,(
% 23.64/3.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.64/3.50    introduced(choice_axiom,[])).
% 23.64/3.50  
% 23.64/3.50  fof(f59,plain,(
% 23.64/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.64/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).
% 23.64/3.50  
% 23.64/3.50  fof(f86,plain,(
% 23.64/3.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f59])).
% 23.64/3.50  
% 23.64/3.50  fof(f6,axiom,(
% 23.64/3.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.64/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.64/3.50  
% 23.64/3.50  fof(f93,plain,(
% 23.64/3.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.64/3.50    inference(cnf_transformation,[],[f6])).
% 23.64/3.50  
% 23.64/3.50  cnf(c_17,plain,
% 23.64/3.50      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.64/3.50      inference(cnf_transformation,[],[f163]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1794,plain,
% 23.64/3.50      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.64/3.50      | r1_tarski(X0,X1) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_38,plain,
% 23.64/3.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.64/3.50      inference(cnf_transformation,[],[f133]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1775,plain,
% 23.64/3.50      ( m1_subset_1(X0,X1) = iProver_top
% 23.64/3.50      | r2_hidden(X0,X1) != iProver_top
% 23.64/3.50      | v1_xboole_0(X1) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_13944,plain,
% 23.64/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.64/3.50      | r1_tarski(X0,X1) != iProver_top
% 23.64/3.50      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1794,c_1775]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_47,negated_conjecture,
% 23.64/3.50      ( r1_tarski(sK10,k3_subset_1(sK9,sK11)) ),
% 23.64/3.50      inference(cnf_transformation,[],[f145]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1767,plain,
% 23.64/3.50      ( r1_tarski(sK10,k3_subset_1(sK9,sK11)) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_40,plain,
% 23.64/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.64/3.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 23.64/3.50      inference(cnf_transformation,[],[f137]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1773,plain,
% 23.64/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.64/3.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_49,negated_conjecture,
% 23.64/3.50      ( m1_subset_1(sK11,k1_zfmisc_1(sK9)) ),
% 23.64/3.50      inference(cnf_transformation,[],[f143]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1765,plain,
% 23.64/3.50      ( m1_subset_1(sK11,k1_zfmisc_1(sK9)) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_41,plain,
% 23.64/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.64/3.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f138]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1772,plain,
% 23.64/3.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 23.64/3.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_16999,plain,
% 23.64/3.50      ( k3_subset_1(sK9,k3_subset_1(sK9,sK11)) = sK11 ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1765,c_1772]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_43,plain,
% 23.64/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.64/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.64/3.50      | ~ r1_tarski(X0,X2)
% 23.64/3.50      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 23.64/3.50      inference(cnf_transformation,[],[f139]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1770,plain,
% 23.64/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.64/3.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 23.64/3.50      | r1_tarski(X0,X2) != iProver_top
% 23.64/3.50      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_17313,plain,
% 23.64/3.50      ( m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
% 23.64/3.50      | m1_subset_1(k3_subset_1(sK9,sK11),k1_zfmisc_1(sK9)) != iProver_top
% 23.64/3.50      | r1_tarski(X0,k3_subset_1(sK9,sK11)) != iProver_top
% 23.64/3.50      | r1_tarski(sK11,k3_subset_1(sK9,X0)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_16999,c_1770]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_17757,plain,
% 23.64/3.50      ( m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
% 23.64/3.50      | m1_subset_1(sK11,k1_zfmisc_1(sK9)) != iProver_top
% 23.64/3.50      | r1_tarski(X0,k3_subset_1(sK9,sK11)) != iProver_top
% 23.64/3.50      | r1_tarski(sK11,k3_subset_1(sK9,X0)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1773,c_17313]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_50,plain,
% 23.64/3.50      ( m1_subset_1(sK11,k1_zfmisc_1(sK9)) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_19885,plain,
% 23.64/3.50      ( m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
% 23.64/3.50      | r1_tarski(X0,k3_subset_1(sK9,sK11)) != iProver_top
% 23.64/3.50      | r1_tarski(sK11,k3_subset_1(sK9,X0)) = iProver_top ),
% 23.64/3.50      inference(global_propositional_subsumption,
% 23.64/3.50                [status(thm)],
% 23.64/3.50                [c_17757,c_50]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_19893,plain,
% 23.64/3.50      ( m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top
% 23.64/3.50      | r1_tarski(sK11,k3_subset_1(sK9,sK10)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1767,c_19885]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_5,plain,
% 23.64/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 23.64/3.50      inference(cnf_transformation,[],[f92]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1800,plain,
% 23.64/3.50      ( r1_tarski(X0,X1) != iProver_top
% 23.64/3.50      | r1_tarski(X1,X2) != iProver_top
% 23.64/3.50      | r1_tarski(X0,X2) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_20168,plain,
% 23.64/3.50      ( m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top
% 23.64/3.50      | r1_tarski(k3_subset_1(sK9,sK10),X0) != iProver_top
% 23.64/3.50      | r1_tarski(sK11,X0) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_19893,c_1800]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_46,negated_conjecture,
% 23.64/3.50      ( k1_xboole_0 != sK10 ),
% 23.64/3.50      inference(cnf_transformation,[],[f146]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_9,plain,
% 23.64/3.50      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 23.64/3.50      inference(cnf_transformation,[],[f162]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_8,plain,
% 23.64/3.50      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f96]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_144,plain,
% 23.64/3.50      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 23.64/3.50      | k1_xboole_0 = k1_xboole_0 ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_8]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_938,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1863,plain,
% 23.64/3.50      ( sK10 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK10 ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_938]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1864,plain,
% 23.64/3.50      ( sK10 != k1_xboole_0
% 23.64/3.50      | k1_xboole_0 = sK10
% 23.64/3.50      | k1_xboole_0 != k1_xboole_0 ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_1863]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_48,negated_conjecture,
% 23.64/3.50      ( r1_tarski(sK10,sK11) ),
% 23.64/3.50      inference(cnf_transformation,[],[f144]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1766,plain,
% 23.64/3.50      ( r1_tarski(sK10,sK11) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_20163,plain,
% 23.64/3.50      ( r1_tarski(sK11,X0) != iProver_top
% 23.64/3.50      | r1_tarski(sK10,X0) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1766,c_1800]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_20378,plain,
% 23.64/3.50      ( m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top
% 23.64/3.50      | r1_tarski(sK10,k3_subset_1(sK9,sK10)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_19893,c_20163]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_45,plain,
% 23.64/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.64/3.50      | ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 23.64/3.50      | k1_xboole_0 = X0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f161]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1768,plain,
% 23.64/3.50      ( k1_xboole_0 = X0
% 23.64/3.50      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.64/3.50      | r1_tarski(X0,k3_subset_1(X1,X0)) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_20778,plain,
% 23.64/3.50      ( sK10 = k1_xboole_0
% 23.64/3.50      | m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_20378,c_1768]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_21331,plain,
% 23.64/3.50      ( m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top ),
% 23.64/3.50      inference(global_propositional_subsumption,
% 23.64/3.50                [status(thm)],
% 23.64/3.50                [c_20168,c_46,c_9,c_144,c_1864,c_20778]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_59496,plain,
% 23.64/3.50      ( r1_tarski(sK10,sK9) != iProver_top
% 23.64/3.50      | v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_13944,c_21331]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_39,plain,
% 23.64/3.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.64/3.50      inference(cnf_transformation,[],[f132]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1774,plain,
% 23.64/3.50      ( m1_subset_1(X0,X1) != iProver_top
% 23.64/3.50      | r2_hidden(X0,X1) = iProver_top
% 23.64/3.50      | v1_xboole_0(X1) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_10560,plain,
% 23.64/3.50      ( r2_hidden(sK11,k1_zfmisc_1(sK9)) = iProver_top
% 23.64/3.50      | v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_1765,c_1774]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_18,plain,
% 23.64/3.50      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.64/3.50      inference(cnf_transformation,[],[f164]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1793,plain,
% 23.64/3.50      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.64/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_10931,plain,
% 23.64/3.50      ( r1_tarski(sK11,sK9) = iProver_top
% 23.64/3.50      | v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_10560,c_1793]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_20376,plain,
% 23.64/3.50      ( r1_tarski(sK10,sK9) = iProver_top
% 23.64/3.50      | v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_10931,c_20163]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_59733,plain,
% 23.64/3.50      ( v1_xboole_0(k1_zfmisc_1(sK9)) = iProver_top ),
% 23.64/3.50      inference(global_propositional_subsumption,
% 23.64/3.50                [status(thm)],
% 23.64/3.50                [c_59496,c_20376]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_11,plain,
% 23.64/3.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f98]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1798,plain,
% 23.64/3.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_59740,plain,
% 23.64/3.50      ( k1_zfmisc_1(sK9) = k1_xboole_0 ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_59733,c_1798]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_35,plain,
% 23.64/3.50      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f131]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_60159,plain,
% 23.64/3.50      ( k3_tarski(k1_xboole_0) = sK9 ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_59740,c_35]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_30,plain,
% 23.64/3.50      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f126]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_60182,plain,
% 23.64/3.50      ( sK9 = k1_xboole_0 ),
% 23.64/3.50      inference(light_normalisation,[status(thm)],[c_60159,c_30]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_60189,plain,
% 23.64/3.50      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_60182,c_59740]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3,plain,
% 23.64/3.50      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f156]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_32,plain,
% 23.64/3.50      ( ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) ),
% 23.64/3.50      inference(cnf_transformation,[],[f169]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_1780,plain,
% 23.64/3.50      ( r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_13,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.64/3.50      inference(cnf_transformation,[],[f100]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_14,plain,
% 23.64/3.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f101]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2609,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_14,c_13]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3337,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_13,c_2609]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_7,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.64/3.50      inference(cnf_transformation,[],[f94]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2608,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_7,c_13]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3077,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_2608,c_13]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3079,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_3077,c_2608]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3338,plain,
% 23.64/3.50      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_14,c_2609]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3351,plain,
% 23.64/3.50      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 23.64/3.50      inference(light_normalisation,[status(thm)],[c_3338,c_7]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3366,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_3337,c_3079,c_3351]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2611,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_13,c_14]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3352,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_3351,c_2609]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3483,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_2611,c_3352]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3491,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_3483,c_7]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3573,plain,
% 23.64/3.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3491,c_3352]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3579,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_13,c_3573]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_4361,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = k5_xboole_0(X3,X2) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3366,c_3579]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_4195,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3366,c_3366]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_4402,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_4361,c_3079,c_4195]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3571,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3352,c_3491]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3826,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3571,c_13]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3568,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_13,c_3491]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3642,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,X0) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3352,c_3568]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_6361,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2)) = k5_xboole_0(k5_xboole_0(X3,X1),X0) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3826,c_3642]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3652,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X1,X2) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3568,c_3568]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_5995,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X3) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3579,c_3652]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_5491,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X3,X2),X0) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3642,c_3642]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3574,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3491,c_13]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3581,plain,
% 23.64/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_3574,c_3079]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_5226,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,X2)) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3581,c_3579]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_5493,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 23.64/3.50      inference(light_normalisation,[status(thm)],[c_5491,c_5226]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_3643,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X2,X1) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3491,c_3568]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_5560,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2)) = k5_xboole_0(X3,k5_xboole_0(X1,X0)) ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3579,c_3643]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_6128,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2)) = k5_xboole_0(X1,k5_xboole_0(X3,X0)) ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_5995,c_5493,c_5560]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_6380,plain,
% 23.64/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.64/3.50      inference(light_normalisation,[status(thm)],[c_6361,c_6128]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_40045,plain,
% 23.64/3.50      ( r2_hidden(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_1780,c_4402,c_6380]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_40051,plain,
% 23.64/3.50      ( r2_hidden(X0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 23.64/3.50      inference(superposition,[status(thm)],[c_3,c_40045]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_40052,plain,
% 23.64/3.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 23.64/3.50      inference(demodulation,[status(thm)],[c_40051,c_14]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_40057,plain,
% 23.64/3.50      ( r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_40052]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_939,plain,
% 23.64/3.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.64/3.50      theory(equality) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_4440,plain,
% 23.64/3.50      ( ~ r1_tarski(X0,X1)
% 23.64/3.50      | r1_tarski(k1_zfmisc_1(X2),X3)
% 23.64/3.50      | X3 != X1
% 23.64/3.50      | k1_zfmisc_1(X2) != X0 ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_939]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_4441,plain,
% 23.64/3.50      ( X0 != X1
% 23.64/3.50      | k1_zfmisc_1(X2) != X3
% 23.64/3.50      | r1_tarski(X3,X1) != iProver_top
% 23.64/3.50      | r1_tarski(k1_zfmisc_1(X2),X0) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_4440]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_4443,plain,
% 23.64/3.50      ( k1_zfmisc_1(k1_xboole_0) != k1_xboole_0
% 23.64/3.50      | k1_xboole_0 != k1_xboole_0
% 23.64/3.50      | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 23.64/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_4441]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2,plain,
% 23.64/3.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 23.64/3.50      inference(cnf_transformation,[],[f86]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2170,plain,
% 23.64/3.50      ( r2_hidden(X0,X1)
% 23.64/3.50      | ~ r2_hidden(X0,k1_zfmisc_1(X2))
% 23.64/3.50      | ~ r1_tarski(k1_zfmisc_1(X2),X1) ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2171,plain,
% 23.64/3.50      ( r2_hidden(X0,X1) = iProver_top
% 23.64/3.50      | r2_hidden(X0,k1_zfmisc_1(X2)) != iProver_top
% 23.64/3.50      | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_2170]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_2173,plain,
% 23.64/3.50      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.64/3.50      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
% 23.64/3.50      | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_2171]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_6,plain,
% 23.64/3.50      ( r1_tarski(k1_xboole_0,X0) ),
% 23.64/3.50      inference(cnf_transformation,[],[f93]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_146,plain,
% 23.64/3.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_148,plain,
% 23.64/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_146]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_124,plain,
% 23.64/3.50      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.64/3.50      | r1_tarski(X0,X1) != iProver_top ),
% 23.64/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(c_126,plain,
% 23.64/3.50      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 23.64/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.64/3.50      inference(instantiation,[status(thm)],[c_124]) ).
% 23.64/3.50  
% 23.64/3.50  cnf(contradiction,plain,
% 23.64/3.50      ( $false ),
% 23.64/3.50      inference(minisat,
% 23.64/3.50                [status(thm)],
% 23.64/3.50                [c_60189,c_40057,c_4443,c_2173,c_148,c_144,c_9,c_126]) ).
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.64/3.50  
% 23.64/3.50  ------                               Statistics
% 23.64/3.50  
% 23.64/3.50  ------ General
% 23.64/3.50  
% 23.64/3.50  abstr_ref_over_cycles:                  0
% 23.64/3.50  abstr_ref_under_cycles:                 0
% 23.64/3.50  gc_basic_clause_elim:                   0
% 23.64/3.50  forced_gc_time:                         0
% 23.64/3.50  parsing_time:                           0.014
% 23.64/3.50  unif_index_cands_time:                  0.
% 23.64/3.50  unif_index_add_time:                    0.
% 23.64/3.50  orderings_time:                         0.
% 23.64/3.50  out_proof_time:                         0.018
% 23.64/3.50  total_time:                             2.871
% 23.64/3.50  num_of_symbols:                         54
% 23.64/3.50  num_of_terms:                           85971
% 23.64/3.50  
% 23.64/3.50  ------ Preprocessing
% 23.64/3.50  
% 23.64/3.50  num_of_splits:                          0
% 23.64/3.50  num_of_split_atoms:                     0
% 23.64/3.50  num_of_reused_defs:                     0
% 23.64/3.50  num_eq_ax_congr_red:                    70
% 23.64/3.50  num_of_sem_filtered_clauses:            1
% 23.64/3.50  num_of_subtypes:                        0
% 23.64/3.50  monotx_restored_types:                  0
% 23.64/3.50  sat_num_of_epr_types:                   0
% 23.64/3.50  sat_num_of_non_cyclic_types:            0
% 23.64/3.50  sat_guarded_non_collapsed_types:        0
% 23.64/3.50  num_pure_diseq_elim:                    0
% 23.64/3.50  simp_replaced_by:                       0
% 23.64/3.50  res_preprocessed:                       217
% 23.64/3.50  prep_upred:                             0
% 23.64/3.50  prep_unflattend:                        3
% 23.64/3.50  smt_new_axioms:                         0
% 23.64/3.50  pred_elim_cands:                        4
% 23.64/3.50  pred_elim:                              1
% 23.64/3.50  pred_elim_cl:                           2
% 23.64/3.50  pred_elim_cycles:                       3
% 23.64/3.50  merged_defs:                            8
% 23.64/3.50  merged_defs_ncl:                        0
% 23.64/3.50  bin_hyper_res:                          8
% 23.64/3.50  prep_cycles:                            4
% 23.64/3.50  pred_elim_time:                         0.001
% 23.64/3.50  splitting_time:                         0.
% 23.64/3.50  sem_filter_time:                        0.
% 23.64/3.50  monotx_time:                            0.001
% 23.64/3.50  subtype_inf_time:                       0.
% 23.64/3.50  
% 23.64/3.50  ------ Problem properties
% 23.64/3.50  
% 23.64/3.50  clauses:                                48
% 23.64/3.50  conjectures:                            4
% 23.64/3.50  epr:                                    12
% 23.64/3.50  horn:                                   40
% 23.64/3.50  ground:                                 6
% 23.64/3.50  unary:                                  13
% 23.64/3.50  binary:                                 17
% 23.64/3.50  lits:                                   105
% 23.64/3.50  lits_eq:                                19
% 23.64/3.50  fd_pure:                                0
% 23.64/3.50  fd_pseudo:                              0
% 23.64/3.50  fd_cond:                                3
% 23.64/3.50  fd_pseudo_cond:                         7
% 23.64/3.50  ac_symbols:                             1
% 23.64/3.50  
% 23.64/3.50  ------ Propositional Solver
% 23.64/3.50  
% 23.64/3.50  prop_solver_calls:                      32
% 23.64/3.50  prop_fast_solver_calls:                 2245
% 23.64/3.50  smt_solver_calls:                       0
% 23.64/3.50  smt_fast_solver_calls:                  0
% 23.64/3.50  prop_num_of_clauses:                    19009
% 23.64/3.50  prop_preprocess_simplified:             37540
% 23.64/3.50  prop_fo_subsumed:                       59
% 23.64/3.50  prop_solver_time:                       0.
% 23.64/3.50  smt_solver_time:                        0.
% 23.64/3.50  smt_fast_solver_time:                   0.
% 23.64/3.50  prop_fast_solver_time:                  0.
% 23.64/3.50  prop_unsat_core_time:                   0.001
% 23.64/3.50  
% 23.64/3.50  ------ QBF
% 23.64/3.50  
% 23.64/3.50  qbf_q_res:                              0
% 23.64/3.50  qbf_num_tautologies:                    0
% 23.64/3.50  qbf_prep_cycles:                        0
% 23.64/3.50  
% 23.64/3.50  ------ BMC1
% 23.64/3.50  
% 23.64/3.50  bmc1_current_bound:                     -1
% 23.64/3.50  bmc1_last_solved_bound:                 -1
% 23.64/3.50  bmc1_unsat_core_size:                   -1
% 23.64/3.50  bmc1_unsat_core_parents_size:           -1
% 23.64/3.50  bmc1_merge_next_fun:                    0
% 23.64/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.64/3.50  
% 23.64/3.50  ------ Instantiation
% 23.64/3.50  
% 23.64/3.50  inst_num_of_clauses:                    4414
% 23.64/3.50  inst_num_in_passive:                    2805
% 23.64/3.50  inst_num_in_active:                     979
% 23.64/3.50  inst_num_in_unprocessed:                632
% 23.64/3.50  inst_num_of_loops:                      1680
% 23.64/3.50  inst_num_of_learning_restarts:          0
% 23.64/3.50  inst_num_moves_active_passive:          701
% 23.64/3.50  inst_lit_activity:                      0
% 23.64/3.50  inst_lit_activity_moves:                1
% 23.64/3.50  inst_num_tautologies:                   0
% 23.64/3.50  inst_num_prop_implied:                  0
% 23.64/3.50  inst_num_existing_simplified:           0
% 23.64/3.50  inst_num_eq_res_simplified:             0
% 23.64/3.50  inst_num_child_elim:                    0
% 23.64/3.50  inst_num_of_dismatching_blockings:      5491
% 23.64/3.50  inst_num_of_non_proper_insts:           5041
% 23.64/3.50  inst_num_of_duplicates:                 0
% 23.64/3.50  inst_inst_num_from_inst_to_res:         0
% 23.64/3.50  inst_dismatching_checking_time:         0.
% 23.64/3.50  
% 23.64/3.50  ------ Resolution
% 23.64/3.50  
% 23.64/3.50  res_num_of_clauses:                     0
% 23.64/3.50  res_num_in_passive:                     0
% 23.64/3.50  res_num_in_active:                      0
% 23.64/3.50  res_num_of_loops:                       221
% 23.64/3.50  res_forward_subset_subsumed:            361
% 23.64/3.50  res_backward_subset_subsumed:           4
% 23.64/3.50  res_forward_subsumed:                   0
% 23.64/3.50  res_backward_subsumed:                  0
% 23.64/3.50  res_forward_subsumption_resolution:     0
% 23.64/3.50  res_backward_subsumption_resolution:    0
% 23.64/3.50  res_clause_to_clause_subsumption:       54182
% 23.64/3.50  res_orphan_elimination:                 0
% 23.64/3.50  res_tautology_del:                      181
% 23.64/3.50  res_num_eq_res_simplified:              0
% 23.64/3.50  res_num_sel_changes:                    0
% 23.64/3.50  res_moves_from_active_to_pass:          0
% 23.64/3.50  
% 23.64/3.50  ------ Superposition
% 23.64/3.50  
% 23.64/3.50  sup_time_total:                         0.
% 23.64/3.50  sup_time_generating:                    0.
% 23.64/3.50  sup_time_sim_full:                      0.
% 23.64/3.50  sup_time_sim_immed:                     0.
% 23.64/3.50  
% 23.64/3.50  sup_num_of_clauses:                     1653
% 23.64/3.50  sup_num_in_active:                      166
% 23.64/3.50  sup_num_in_passive:                     1487
% 23.64/3.50  sup_num_of_loops:                       335
% 23.64/3.50  sup_fw_superposition:                   7255
% 23.64/3.50  sup_bw_superposition:                   4868
% 23.64/3.50  sup_immediate_simplified:               5839
% 23.64/3.50  sup_given_eliminated:                   8
% 23.64/3.50  comparisons_done:                       0
% 23.64/3.50  comparisons_avoided:                    7
% 23.64/3.50  
% 23.64/3.50  ------ Simplifications
% 23.64/3.50  
% 23.64/3.50  
% 23.64/3.50  sim_fw_subset_subsumed:                 60
% 23.64/3.50  sim_bw_subset_subsumed:                 40
% 23.64/3.50  sim_fw_subsumed:                        300
% 23.64/3.50  sim_bw_subsumed:                        120
% 23.64/3.50  sim_fw_subsumption_res:                 0
% 23.64/3.50  sim_bw_subsumption_res:                 0
% 23.64/3.50  sim_tautology_del:                      49
% 23.64/3.50  sim_eq_tautology_del:                   915
% 23.64/3.50  sim_eq_res_simp:                        0
% 23.64/3.50  sim_fw_demodulated:                     5781
% 23.64/3.50  sim_bw_demodulated:                     98
% 23.64/3.50  sim_light_normalised:                   1191
% 23.64/3.50  sim_joinable_taut:                      329
% 23.64/3.50  sim_joinable_simp:                      0
% 23.64/3.50  sim_ac_normalised:                      0
% 23.64/3.50  sim_smt_subsumption:                    0
% 23.64/3.50  
%------------------------------------------------------------------------------
