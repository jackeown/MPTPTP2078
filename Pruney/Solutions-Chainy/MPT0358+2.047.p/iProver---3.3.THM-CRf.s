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
% DateTime   : Thu Dec  3 11:39:56 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 254 expanded)
%              Number of clauses        :   68 (  83 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  416 (1026 expanded)
%              Number of equality atoms :  143 ( 270 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f28])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK4) != sK5
        | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
      & ( k1_subset_1(sK4) = sK5
        | r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_subset_1(sK4) != sK5
      | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
    & ( k1_subset_1(sK4) = sK5
      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) )
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f37])).

fof(f63,plain,
    ( k1_subset_1(sK4) = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f63,f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
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

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f49])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f62,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,
    ( k1_subset_1(sK4) != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,
    ( k1_xboole_0 != sK5
    | ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) ),
    inference(definition_unfolding,[],[f64,f59])).

cnf(c_1296,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2405,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2
    | sK5 != X2
    | sK5 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_4635,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | sK5 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2405])).

cnf(c_4637,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) != k1_xboole_0
    | sK5 = k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4635])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1961,plain,
    ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),X0)
    | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4010,plain,
    ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5)
    | ~ r1_tarski(sK5,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_1961])).

cnf(c_4014,plain,
    ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)))
    | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5)
    | ~ r1_tarski(sK5,k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_4010])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1757,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1750,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_327,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_338,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_328,c_20])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_794,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_795,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_794])).

cnf(c_840,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_338,c_795])).

cnf(c_1748,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_2077,plain,
    ( k5_xboole_0(k3_subset_1(sK4,sK5),k3_xboole_0(k3_subset_1(sK4,sK5),sK5)) = k3_subset_1(k3_subset_1(sK4,sK5),sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1750,c_1748])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1759,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2957,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k3_subset_1(k3_subset_1(sK4,sK5),sK5)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2077,c_1759])).

cnf(c_193,plain,
    ( r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_614,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k3_subset_1(sK4,sK5) != X2
    | sK5 != X1
    | sK5 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_193])).

cnf(c_615,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,sK5))
    | ~ r2_hidden(X0,sK5)
    | sK5 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_616,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k3_subset_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_360,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_361,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK5)) = k3_subset_1(X0,sK5)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_1912,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
    inference(equality_resolution,[status(thm)],[c_361])).

cnf(c_2958,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,sK5)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_1759])).

cnf(c_3842,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2957,c_616,c_2958])).

cnf(c_3851,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1757,c_3842])).

cnf(c_2263,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) = X0 ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_3297,plain,
    ( X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X0
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_2263])).

cnf(c_3298,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) != k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))
    | k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) = sK5
    | sK5 != k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_3297])).

cnf(c_2955,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK2(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1759])).

cnf(c_3007,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) = k1_xboole_0
    | r2_hidden(sK2(k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2955])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1758,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2729,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK2(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1758])).

cnf(c_2761,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) = k1_xboole_0
    | r2_hidden(sK2(k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2729])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1765,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1766,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2323,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1766])).

cnf(c_2331,plain,
    ( r1_tarski(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2323])).

cnf(c_2333,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2331])).

cnf(c_1295,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2259,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_2262,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) = k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_1297,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2138,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_2140,plain,
    ( r1_tarski(sK5,k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)))
    | ~ r1_tarski(sK5,sK5)
    | k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) != sK5
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_1959,plain,
    ( ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),k5_xboole_0(X0,k3_xboole_0(X0,sK5)))
    | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1969,plain,
    ( ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)))
    | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5) ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_1310,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_191,plain,
    ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5))
    | k1_xboole_0 != sK5 ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_558,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_subset_1(sK4,sK5) != X1
    | sK5 != X0
    | sK5 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_191])).

cnf(c_559,plain,
    ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5)
    | sK5 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4637,c_4014,c_3851,c_3298,c_3007,c_2761,c_2333,c_2262,c_2140,c_1969,c_1310,c_559])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  % Running in FOF mode
% 2.37/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.01  
% 2.37/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.37/1.01  
% 2.37/1.01  ------  iProver source info
% 2.37/1.01  
% 2.37/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.37/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.37/1.01  git: non_committed_changes: false
% 2.37/1.01  git: last_make_outside_of_git: false
% 2.37/1.01  
% 2.37/1.01  ------ 
% 2.37/1.01  
% 2.37/1.01  ------ Input Options
% 2.37/1.01  
% 2.37/1.01  --out_options                           all
% 2.37/1.01  --tptp_safe_out                         true
% 2.37/1.01  --problem_path                          ""
% 2.37/1.01  --include_path                          ""
% 2.37/1.01  --clausifier                            res/vclausify_rel
% 2.37/1.01  --clausifier_options                    --mode clausify
% 2.37/1.01  --stdin                                 false
% 2.37/1.01  --stats_out                             all
% 2.37/1.01  
% 2.37/1.01  ------ General Options
% 2.37/1.01  
% 2.37/1.01  --fof                                   false
% 2.37/1.01  --time_out_real                         305.
% 2.37/1.01  --time_out_virtual                      -1.
% 2.37/1.01  --symbol_type_check                     false
% 2.37/1.01  --clausify_out                          false
% 2.37/1.01  --sig_cnt_out                           false
% 2.37/1.01  --trig_cnt_out                          false
% 2.37/1.01  --trig_cnt_out_tolerance                1.
% 2.37/1.01  --trig_cnt_out_sk_spl                   false
% 2.37/1.01  --abstr_cl_out                          false
% 2.37/1.01  
% 2.37/1.01  ------ Global Options
% 2.37/1.01  
% 2.37/1.01  --schedule                              default
% 2.37/1.01  --add_important_lit                     false
% 2.37/1.01  --prop_solver_per_cl                    1000
% 2.37/1.01  --min_unsat_core                        false
% 2.37/1.01  --soft_assumptions                      false
% 2.37/1.01  --soft_lemma_size                       3
% 2.37/1.01  --prop_impl_unit_size                   0
% 2.37/1.01  --prop_impl_unit                        []
% 2.37/1.01  --share_sel_clauses                     true
% 2.37/1.01  --reset_solvers                         false
% 2.37/1.01  --bc_imp_inh                            [conj_cone]
% 2.37/1.01  --conj_cone_tolerance                   3.
% 2.37/1.01  --extra_neg_conj                        none
% 2.37/1.01  --large_theory_mode                     true
% 2.37/1.01  --prolific_symb_bound                   200
% 2.37/1.01  --lt_threshold                          2000
% 2.37/1.01  --clause_weak_htbl                      true
% 2.37/1.01  --gc_record_bc_elim                     false
% 2.37/1.01  
% 2.37/1.01  ------ Preprocessing Options
% 2.37/1.01  
% 2.37/1.01  --preprocessing_flag                    true
% 2.37/1.01  --time_out_prep_mult                    0.1
% 2.37/1.01  --splitting_mode                        input
% 2.37/1.01  --splitting_grd                         true
% 2.37/1.01  --splitting_cvd                         false
% 2.37/1.01  --splitting_cvd_svl                     false
% 2.37/1.01  --splitting_nvd                         32
% 2.37/1.01  --sub_typing                            true
% 2.37/1.01  --prep_gs_sim                           true
% 2.37/1.01  --prep_unflatten                        true
% 2.37/1.01  --prep_res_sim                          true
% 2.37/1.01  --prep_upred                            true
% 2.37/1.01  --prep_sem_filter                       exhaustive
% 2.37/1.01  --prep_sem_filter_out                   false
% 2.37/1.01  --pred_elim                             true
% 2.37/1.01  --res_sim_input                         true
% 2.37/1.01  --eq_ax_congr_red                       true
% 2.37/1.01  --pure_diseq_elim                       true
% 2.37/1.01  --brand_transform                       false
% 2.37/1.01  --non_eq_to_eq                          false
% 2.37/1.01  --prep_def_merge                        true
% 2.37/1.01  --prep_def_merge_prop_impl              false
% 2.37/1.01  --prep_def_merge_mbd                    true
% 2.37/1.01  --prep_def_merge_tr_red                 false
% 2.37/1.01  --prep_def_merge_tr_cl                  false
% 2.37/1.01  --smt_preprocessing                     true
% 2.37/1.01  --smt_ac_axioms                         fast
% 2.37/1.01  --preprocessed_out                      false
% 2.37/1.01  --preprocessed_stats                    false
% 2.37/1.01  
% 2.37/1.01  ------ Abstraction refinement Options
% 2.37/1.01  
% 2.37/1.01  --abstr_ref                             []
% 2.37/1.01  --abstr_ref_prep                        false
% 2.37/1.01  --abstr_ref_until_sat                   false
% 2.37/1.01  --abstr_ref_sig_restrict                funpre
% 2.37/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/1.01  --abstr_ref_under                       []
% 2.37/1.01  
% 2.37/1.01  ------ SAT Options
% 2.37/1.01  
% 2.37/1.01  --sat_mode                              false
% 2.37/1.01  --sat_fm_restart_options                ""
% 2.37/1.01  --sat_gr_def                            false
% 2.37/1.01  --sat_epr_types                         true
% 2.37/1.01  --sat_non_cyclic_types                  false
% 2.37/1.01  --sat_finite_models                     false
% 2.37/1.01  --sat_fm_lemmas                         false
% 2.37/1.01  --sat_fm_prep                           false
% 2.37/1.01  --sat_fm_uc_incr                        true
% 2.37/1.01  --sat_out_model                         small
% 2.37/1.01  --sat_out_clauses                       false
% 2.37/1.01  
% 2.37/1.01  ------ QBF Options
% 2.37/1.01  
% 2.37/1.01  --qbf_mode                              false
% 2.37/1.01  --qbf_elim_univ                         false
% 2.37/1.01  --qbf_dom_inst                          none
% 2.37/1.01  --qbf_dom_pre_inst                      false
% 2.37/1.01  --qbf_sk_in                             false
% 2.37/1.01  --qbf_pred_elim                         true
% 2.37/1.01  --qbf_split                             512
% 2.37/1.01  
% 2.37/1.01  ------ BMC1 Options
% 2.37/1.01  
% 2.37/1.01  --bmc1_incremental                      false
% 2.37/1.01  --bmc1_axioms                           reachable_all
% 2.37/1.01  --bmc1_min_bound                        0
% 2.37/1.01  --bmc1_max_bound                        -1
% 2.37/1.01  --bmc1_max_bound_default                -1
% 2.37/1.01  --bmc1_symbol_reachability              true
% 2.37/1.01  --bmc1_property_lemmas                  false
% 2.37/1.01  --bmc1_k_induction                      false
% 2.37/1.01  --bmc1_non_equiv_states                 false
% 2.37/1.01  --bmc1_deadlock                         false
% 2.37/1.01  --bmc1_ucm                              false
% 2.37/1.01  --bmc1_add_unsat_core                   none
% 2.37/1.01  --bmc1_unsat_core_children              false
% 2.37/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/1.01  --bmc1_out_stat                         full
% 2.37/1.01  --bmc1_ground_init                      false
% 2.37/1.01  --bmc1_pre_inst_next_state              false
% 2.37/1.01  --bmc1_pre_inst_state                   false
% 2.37/1.01  --bmc1_pre_inst_reach_state             false
% 2.37/1.01  --bmc1_out_unsat_core                   false
% 2.37/1.01  --bmc1_aig_witness_out                  false
% 2.37/1.01  --bmc1_verbose                          false
% 2.37/1.01  --bmc1_dump_clauses_tptp                false
% 2.37/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.37/1.01  --bmc1_dump_file                        -
% 2.37/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.37/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.37/1.01  --bmc1_ucm_extend_mode                  1
% 2.37/1.01  --bmc1_ucm_init_mode                    2
% 2.37/1.01  --bmc1_ucm_cone_mode                    none
% 2.37/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.37/1.01  --bmc1_ucm_relax_model                  4
% 2.37/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.37/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/1.01  --bmc1_ucm_layered_model                none
% 2.37/1.01  --bmc1_ucm_max_lemma_size               10
% 2.37/1.01  
% 2.37/1.01  ------ AIG Options
% 2.37/1.01  
% 2.37/1.01  --aig_mode                              false
% 2.37/1.01  
% 2.37/1.01  ------ Instantiation Options
% 2.37/1.01  
% 2.37/1.01  --instantiation_flag                    true
% 2.37/1.01  --inst_sos_flag                         false
% 2.37/1.01  --inst_sos_phase                        true
% 2.37/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/1.01  --inst_lit_sel_side                     num_symb
% 2.37/1.01  --inst_solver_per_active                1400
% 2.37/1.01  --inst_solver_calls_frac                1.
% 2.37/1.01  --inst_passive_queue_type               priority_queues
% 2.37/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/1.01  --inst_passive_queues_freq              [25;2]
% 2.37/1.01  --inst_dismatching                      true
% 2.37/1.01  --inst_eager_unprocessed_to_passive     true
% 2.37/1.01  --inst_prop_sim_given                   true
% 2.37/1.01  --inst_prop_sim_new                     false
% 2.37/1.01  --inst_subs_new                         false
% 2.37/1.01  --inst_eq_res_simp                      false
% 2.37/1.01  --inst_subs_given                       false
% 2.37/1.01  --inst_orphan_elimination               true
% 2.37/1.01  --inst_learning_loop_flag               true
% 2.37/1.01  --inst_learning_start                   3000
% 2.37/1.01  --inst_learning_factor                  2
% 2.37/1.01  --inst_start_prop_sim_after_learn       3
% 2.37/1.01  --inst_sel_renew                        solver
% 2.37/1.01  --inst_lit_activity_flag                true
% 2.37/1.01  --inst_restr_to_given                   false
% 2.37/1.01  --inst_activity_threshold               500
% 2.37/1.01  --inst_out_proof                        true
% 2.37/1.01  
% 2.37/1.01  ------ Resolution Options
% 2.37/1.01  
% 2.37/1.01  --resolution_flag                       true
% 2.37/1.01  --res_lit_sel                           adaptive
% 2.37/1.01  --res_lit_sel_side                      none
% 2.37/1.01  --res_ordering                          kbo
% 2.37/1.01  --res_to_prop_solver                    active
% 2.37/1.01  --res_prop_simpl_new                    false
% 2.37/1.01  --res_prop_simpl_given                  true
% 2.37/1.01  --res_passive_queue_type                priority_queues
% 2.37/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/1.01  --res_passive_queues_freq               [15;5]
% 2.37/1.01  --res_forward_subs                      full
% 2.37/1.01  --res_backward_subs                     full
% 2.37/1.01  --res_forward_subs_resolution           true
% 2.37/1.01  --res_backward_subs_resolution          true
% 2.37/1.01  --res_orphan_elimination                true
% 2.37/1.01  --res_time_limit                        2.
% 2.37/1.01  --res_out_proof                         true
% 2.37/1.01  
% 2.37/1.01  ------ Superposition Options
% 2.37/1.01  
% 2.37/1.01  --superposition_flag                    true
% 2.37/1.01  --sup_passive_queue_type                priority_queues
% 2.37/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.37/1.01  --demod_completeness_check              fast
% 2.37/1.01  --demod_use_ground                      true
% 2.37/1.01  --sup_to_prop_solver                    passive
% 2.37/1.01  --sup_prop_simpl_new                    true
% 2.37/1.01  --sup_prop_simpl_given                  true
% 2.37/1.01  --sup_fun_splitting                     false
% 2.37/1.01  --sup_smt_interval                      50000
% 2.37/1.01  
% 2.37/1.01  ------ Superposition Simplification Setup
% 2.37/1.01  
% 2.37/1.01  --sup_indices_passive                   []
% 2.37/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.01  --sup_full_bw                           [BwDemod]
% 2.37/1.01  --sup_immed_triv                        [TrivRules]
% 2.37/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.01  --sup_immed_bw_main                     []
% 2.37/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.01  
% 2.37/1.01  ------ Combination Options
% 2.37/1.01  
% 2.37/1.01  --comb_res_mult                         3
% 2.37/1.01  --comb_sup_mult                         2
% 2.37/1.01  --comb_inst_mult                        10
% 2.37/1.01  
% 2.37/1.01  ------ Debug Options
% 2.37/1.01  
% 2.37/1.01  --dbg_backtrace                         false
% 2.37/1.01  --dbg_dump_prop_clauses                 false
% 2.37/1.01  --dbg_dump_prop_clauses_file            -
% 2.37/1.01  --dbg_out_stat                          false
% 2.37/1.01  ------ Parsing...
% 2.37/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.37/1.01  
% 2.37/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.37/1.01  
% 2.37/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.37/1.01  
% 2.37/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.37/1.01  ------ Proving...
% 2.37/1.01  ------ Problem Properties 
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  clauses                                 20
% 2.37/1.01  conjectures                             2
% 2.37/1.01  EPR                                     1
% 2.37/1.01  Horn                                    12
% 2.37/1.01  unary                                   1
% 2.37/1.01  binary                                  12
% 2.37/1.01  lits                                    47
% 2.37/1.01  lits eq                                 12
% 2.37/1.01  fd_pure                                 0
% 2.37/1.01  fd_pseudo                               0
% 2.37/1.01  fd_cond                                 1
% 2.37/1.01  fd_pseudo_cond                          5
% 2.37/1.01  AC symbols                              0
% 2.37/1.01  
% 2.37/1.01  ------ Schedule dynamic 5 is on 
% 2.37/1.01  
% 2.37/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  ------ 
% 2.37/1.01  Current options:
% 2.37/1.01  ------ 
% 2.37/1.01  
% 2.37/1.01  ------ Input Options
% 2.37/1.01  
% 2.37/1.01  --out_options                           all
% 2.37/1.01  --tptp_safe_out                         true
% 2.37/1.01  --problem_path                          ""
% 2.37/1.01  --include_path                          ""
% 2.37/1.01  --clausifier                            res/vclausify_rel
% 2.37/1.01  --clausifier_options                    --mode clausify
% 2.37/1.01  --stdin                                 false
% 2.37/1.01  --stats_out                             all
% 2.37/1.01  
% 2.37/1.01  ------ General Options
% 2.37/1.01  
% 2.37/1.01  --fof                                   false
% 2.37/1.01  --time_out_real                         305.
% 2.37/1.01  --time_out_virtual                      -1.
% 2.37/1.01  --symbol_type_check                     false
% 2.37/1.01  --clausify_out                          false
% 2.37/1.01  --sig_cnt_out                           false
% 2.37/1.01  --trig_cnt_out                          false
% 2.37/1.01  --trig_cnt_out_tolerance                1.
% 2.37/1.01  --trig_cnt_out_sk_spl                   false
% 2.37/1.01  --abstr_cl_out                          false
% 2.37/1.01  
% 2.37/1.01  ------ Global Options
% 2.37/1.01  
% 2.37/1.01  --schedule                              default
% 2.37/1.01  --add_important_lit                     false
% 2.37/1.01  --prop_solver_per_cl                    1000
% 2.37/1.01  --min_unsat_core                        false
% 2.37/1.01  --soft_assumptions                      false
% 2.37/1.01  --soft_lemma_size                       3
% 2.37/1.01  --prop_impl_unit_size                   0
% 2.37/1.01  --prop_impl_unit                        []
% 2.37/1.01  --share_sel_clauses                     true
% 2.37/1.01  --reset_solvers                         false
% 2.37/1.01  --bc_imp_inh                            [conj_cone]
% 2.37/1.01  --conj_cone_tolerance                   3.
% 2.37/1.01  --extra_neg_conj                        none
% 2.37/1.01  --large_theory_mode                     true
% 2.37/1.01  --prolific_symb_bound                   200
% 2.37/1.01  --lt_threshold                          2000
% 2.37/1.01  --clause_weak_htbl                      true
% 2.37/1.01  --gc_record_bc_elim                     false
% 2.37/1.01  
% 2.37/1.01  ------ Preprocessing Options
% 2.37/1.01  
% 2.37/1.01  --preprocessing_flag                    true
% 2.37/1.01  --time_out_prep_mult                    0.1
% 2.37/1.01  --splitting_mode                        input
% 2.37/1.01  --splitting_grd                         true
% 2.37/1.01  --splitting_cvd                         false
% 2.37/1.01  --splitting_cvd_svl                     false
% 2.37/1.01  --splitting_nvd                         32
% 2.37/1.01  --sub_typing                            true
% 2.37/1.01  --prep_gs_sim                           true
% 2.37/1.01  --prep_unflatten                        true
% 2.37/1.01  --prep_res_sim                          true
% 2.37/1.01  --prep_upred                            true
% 2.37/1.01  --prep_sem_filter                       exhaustive
% 2.37/1.01  --prep_sem_filter_out                   false
% 2.37/1.01  --pred_elim                             true
% 2.37/1.01  --res_sim_input                         true
% 2.37/1.01  --eq_ax_congr_red                       true
% 2.37/1.01  --pure_diseq_elim                       true
% 2.37/1.01  --brand_transform                       false
% 2.37/1.01  --non_eq_to_eq                          false
% 2.37/1.01  --prep_def_merge                        true
% 2.37/1.01  --prep_def_merge_prop_impl              false
% 2.37/1.01  --prep_def_merge_mbd                    true
% 2.37/1.01  --prep_def_merge_tr_red                 false
% 2.37/1.01  --prep_def_merge_tr_cl                  false
% 2.37/1.01  --smt_preprocessing                     true
% 2.37/1.01  --smt_ac_axioms                         fast
% 2.37/1.01  --preprocessed_out                      false
% 2.37/1.01  --preprocessed_stats                    false
% 2.37/1.01  
% 2.37/1.01  ------ Abstraction refinement Options
% 2.37/1.01  
% 2.37/1.01  --abstr_ref                             []
% 2.37/1.01  --abstr_ref_prep                        false
% 2.37/1.01  --abstr_ref_until_sat                   false
% 2.37/1.01  --abstr_ref_sig_restrict                funpre
% 2.37/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/1.01  --abstr_ref_under                       []
% 2.37/1.01  
% 2.37/1.01  ------ SAT Options
% 2.37/1.01  
% 2.37/1.01  --sat_mode                              false
% 2.37/1.01  --sat_fm_restart_options                ""
% 2.37/1.01  --sat_gr_def                            false
% 2.37/1.01  --sat_epr_types                         true
% 2.37/1.01  --sat_non_cyclic_types                  false
% 2.37/1.01  --sat_finite_models                     false
% 2.37/1.01  --sat_fm_lemmas                         false
% 2.37/1.01  --sat_fm_prep                           false
% 2.37/1.01  --sat_fm_uc_incr                        true
% 2.37/1.01  --sat_out_model                         small
% 2.37/1.01  --sat_out_clauses                       false
% 2.37/1.01  
% 2.37/1.01  ------ QBF Options
% 2.37/1.01  
% 2.37/1.01  --qbf_mode                              false
% 2.37/1.01  --qbf_elim_univ                         false
% 2.37/1.01  --qbf_dom_inst                          none
% 2.37/1.01  --qbf_dom_pre_inst                      false
% 2.37/1.01  --qbf_sk_in                             false
% 2.37/1.01  --qbf_pred_elim                         true
% 2.37/1.01  --qbf_split                             512
% 2.37/1.01  
% 2.37/1.01  ------ BMC1 Options
% 2.37/1.01  
% 2.37/1.01  --bmc1_incremental                      false
% 2.37/1.01  --bmc1_axioms                           reachable_all
% 2.37/1.01  --bmc1_min_bound                        0
% 2.37/1.01  --bmc1_max_bound                        -1
% 2.37/1.01  --bmc1_max_bound_default                -1
% 2.37/1.01  --bmc1_symbol_reachability              true
% 2.37/1.01  --bmc1_property_lemmas                  false
% 2.37/1.01  --bmc1_k_induction                      false
% 2.37/1.01  --bmc1_non_equiv_states                 false
% 2.37/1.01  --bmc1_deadlock                         false
% 2.37/1.01  --bmc1_ucm                              false
% 2.37/1.01  --bmc1_add_unsat_core                   none
% 2.37/1.01  --bmc1_unsat_core_children              false
% 2.37/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/1.01  --bmc1_out_stat                         full
% 2.37/1.01  --bmc1_ground_init                      false
% 2.37/1.01  --bmc1_pre_inst_next_state              false
% 2.37/1.01  --bmc1_pre_inst_state                   false
% 2.37/1.01  --bmc1_pre_inst_reach_state             false
% 2.37/1.01  --bmc1_out_unsat_core                   false
% 2.37/1.01  --bmc1_aig_witness_out                  false
% 2.37/1.01  --bmc1_verbose                          false
% 2.37/1.01  --bmc1_dump_clauses_tptp                false
% 2.37/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.37/1.01  --bmc1_dump_file                        -
% 2.37/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.37/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.37/1.01  --bmc1_ucm_extend_mode                  1
% 2.37/1.01  --bmc1_ucm_init_mode                    2
% 2.37/1.01  --bmc1_ucm_cone_mode                    none
% 2.37/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.37/1.01  --bmc1_ucm_relax_model                  4
% 2.37/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.37/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/1.01  --bmc1_ucm_layered_model                none
% 2.37/1.01  --bmc1_ucm_max_lemma_size               10
% 2.37/1.01  
% 2.37/1.01  ------ AIG Options
% 2.37/1.01  
% 2.37/1.01  --aig_mode                              false
% 2.37/1.01  
% 2.37/1.01  ------ Instantiation Options
% 2.37/1.01  
% 2.37/1.01  --instantiation_flag                    true
% 2.37/1.01  --inst_sos_flag                         false
% 2.37/1.01  --inst_sos_phase                        true
% 2.37/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/1.01  --inst_lit_sel_side                     none
% 2.37/1.01  --inst_solver_per_active                1400
% 2.37/1.01  --inst_solver_calls_frac                1.
% 2.37/1.01  --inst_passive_queue_type               priority_queues
% 2.37/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/1.01  --inst_passive_queues_freq              [25;2]
% 2.37/1.01  --inst_dismatching                      true
% 2.37/1.01  --inst_eager_unprocessed_to_passive     true
% 2.37/1.01  --inst_prop_sim_given                   true
% 2.37/1.01  --inst_prop_sim_new                     false
% 2.37/1.01  --inst_subs_new                         false
% 2.37/1.01  --inst_eq_res_simp                      false
% 2.37/1.01  --inst_subs_given                       false
% 2.37/1.01  --inst_orphan_elimination               true
% 2.37/1.01  --inst_learning_loop_flag               true
% 2.37/1.01  --inst_learning_start                   3000
% 2.37/1.01  --inst_learning_factor                  2
% 2.37/1.01  --inst_start_prop_sim_after_learn       3
% 2.37/1.01  --inst_sel_renew                        solver
% 2.37/1.01  --inst_lit_activity_flag                true
% 2.37/1.01  --inst_restr_to_given                   false
% 2.37/1.01  --inst_activity_threshold               500
% 2.37/1.01  --inst_out_proof                        true
% 2.37/1.01  
% 2.37/1.01  ------ Resolution Options
% 2.37/1.01  
% 2.37/1.01  --resolution_flag                       false
% 2.37/1.01  --res_lit_sel                           adaptive
% 2.37/1.01  --res_lit_sel_side                      none
% 2.37/1.01  --res_ordering                          kbo
% 2.37/1.01  --res_to_prop_solver                    active
% 2.37/1.01  --res_prop_simpl_new                    false
% 2.37/1.01  --res_prop_simpl_given                  true
% 2.37/1.01  --res_passive_queue_type                priority_queues
% 2.37/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/1.01  --res_passive_queues_freq               [15;5]
% 2.37/1.01  --res_forward_subs                      full
% 2.37/1.01  --res_backward_subs                     full
% 2.37/1.01  --res_forward_subs_resolution           true
% 2.37/1.01  --res_backward_subs_resolution          true
% 2.37/1.01  --res_orphan_elimination                true
% 2.37/1.01  --res_time_limit                        2.
% 2.37/1.01  --res_out_proof                         true
% 2.37/1.01  
% 2.37/1.01  ------ Superposition Options
% 2.37/1.01  
% 2.37/1.01  --superposition_flag                    true
% 2.37/1.01  --sup_passive_queue_type                priority_queues
% 2.37/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.37/1.01  --demod_completeness_check              fast
% 2.37/1.01  --demod_use_ground                      true
% 2.37/1.01  --sup_to_prop_solver                    passive
% 2.37/1.01  --sup_prop_simpl_new                    true
% 2.37/1.01  --sup_prop_simpl_given                  true
% 2.37/1.01  --sup_fun_splitting                     false
% 2.37/1.01  --sup_smt_interval                      50000
% 2.37/1.01  
% 2.37/1.01  ------ Superposition Simplification Setup
% 2.37/1.01  
% 2.37/1.01  --sup_indices_passive                   []
% 2.37/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.01  --sup_full_bw                           [BwDemod]
% 2.37/1.01  --sup_immed_triv                        [TrivRules]
% 2.37/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.01  --sup_immed_bw_main                     []
% 2.37/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.01  
% 2.37/1.01  ------ Combination Options
% 2.37/1.01  
% 2.37/1.01  --comb_res_mult                         3
% 2.37/1.01  --comb_sup_mult                         2
% 2.37/1.01  --comb_inst_mult                        10
% 2.37/1.01  
% 2.37/1.01  ------ Debug Options
% 2.37/1.01  
% 2.37/1.01  --dbg_backtrace                         false
% 2.37/1.01  --dbg_dump_prop_clauses                 false
% 2.37/1.01  --dbg_dump_prop_clauses_file            -
% 2.37/1.01  --dbg_out_stat                          false
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  ------ Proving...
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  % SZS status Theorem for theBenchmark.p
% 2.37/1.01  
% 2.37/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.37/1.01  
% 2.37/1.01  fof(f1,axiom,(
% 2.37/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f13,plain,(
% 2.37/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.37/1.01    inference(ennf_transformation,[],[f1])).
% 2.37/1.01  
% 2.37/1.01  fof(f19,plain,(
% 2.37/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.37/1.01    inference(nnf_transformation,[],[f13])).
% 2.37/1.01  
% 2.37/1.01  fof(f20,plain,(
% 2.37/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.37/1.01    inference(rectify,[],[f19])).
% 2.37/1.01  
% 2.37/1.01  fof(f21,plain,(
% 2.37/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.37/1.01    introduced(choice_axiom,[])).
% 2.37/1.01  
% 2.37/1.01  fof(f22,plain,(
% 2.37/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 2.37/1.01  
% 2.37/1.01  fof(f39,plain,(
% 2.37/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.37/1.01    inference(cnf_transformation,[],[f22])).
% 2.37/1.01  
% 2.37/1.01  fof(f3,axiom,(
% 2.37/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f14,plain,(
% 2.37/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.37/1.01    inference(ennf_transformation,[],[f3])).
% 2.37/1.01  
% 2.37/1.01  fof(f28,plain,(
% 2.37/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.37/1.01    introduced(choice_axiom,[])).
% 2.37/1.01  
% 2.37/1.01  fof(f29,plain,(
% 2.37/1.01    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f28])).
% 2.37/1.01  
% 2.37/1.01  fof(f48,plain,(
% 2.37/1.01    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.37/1.01    inference(cnf_transformation,[],[f29])).
% 2.37/1.01  
% 2.37/1.01  fof(f11,conjecture,(
% 2.37/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f12,negated_conjecture,(
% 2.37/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 2.37/1.01    inference(negated_conjecture,[],[f11])).
% 2.37/1.01  
% 2.37/1.01  fof(f18,plain,(
% 2.37/1.01    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.37/1.01    inference(ennf_transformation,[],[f12])).
% 2.37/1.01  
% 2.37/1.01  fof(f35,plain,(
% 2.37/1.01    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.37/1.01    inference(nnf_transformation,[],[f18])).
% 2.37/1.01  
% 2.37/1.01  fof(f36,plain,(
% 2.37/1.01    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.37/1.01    inference(flattening,[],[f35])).
% 2.37/1.01  
% 2.37/1.01  fof(f37,plain,(
% 2.37/1.01    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 2.37/1.01    introduced(choice_axiom,[])).
% 2.37/1.01  
% 2.37/1.01  fof(f38,plain,(
% 2.37/1.01    (k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))) & (k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 2.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f37])).
% 2.37/1.01  
% 2.37/1.01  fof(f63,plain,(
% 2.37/1.01    k1_subset_1(sK4) = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 2.37/1.01    inference(cnf_transformation,[],[f38])).
% 2.37/1.01  
% 2.37/1.01  fof(f8,axiom,(
% 2.37/1.01    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f59,plain,(
% 2.37/1.01    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.37/1.01    inference(cnf_transformation,[],[f8])).
% 2.37/1.01  
% 2.37/1.01  fof(f73,plain,(
% 2.37/1.01    k1_xboole_0 = sK5 | r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 2.37/1.01    inference(definition_unfolding,[],[f63,f59])).
% 2.37/1.01  
% 2.37/1.01  fof(f7,axiom,(
% 2.37/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f16,plain,(
% 2.37/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.37/1.01    inference(ennf_transformation,[],[f7])).
% 2.37/1.01  
% 2.37/1.01  fof(f34,plain,(
% 2.37/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.37/1.01    inference(nnf_transformation,[],[f16])).
% 2.37/1.01  
% 2.37/1.01  fof(f56,plain,(
% 2.37/1.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.37/1.01    inference(cnf_transformation,[],[f34])).
% 2.37/1.01  
% 2.37/1.01  fof(f9,axiom,(
% 2.37/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f17,plain,(
% 2.37/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.37/1.01    inference(ennf_transformation,[],[f9])).
% 2.37/1.01  
% 2.37/1.01  fof(f60,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.37/1.01    inference(cnf_transformation,[],[f17])).
% 2.37/1.01  
% 2.37/1.01  fof(f4,axiom,(
% 2.37/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f49,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.37/1.01    inference(cnf_transformation,[],[f4])).
% 2.37/1.01  
% 2.37/1.01  fof(f71,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.37/1.01    inference(definition_unfolding,[],[f60,f49])).
% 2.37/1.01  
% 2.37/1.01  fof(f10,axiom,(
% 2.37/1.01    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f61,plain,(
% 2.37/1.01    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.37/1.01    inference(cnf_transformation,[],[f10])).
% 2.37/1.01  
% 2.37/1.01  fof(f6,axiom,(
% 2.37/1.01    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f30,plain,(
% 2.37/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.37/1.01    inference(nnf_transformation,[],[f6])).
% 2.37/1.01  
% 2.37/1.01  fof(f31,plain,(
% 2.37/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.37/1.01    inference(rectify,[],[f30])).
% 2.37/1.01  
% 2.37/1.01  fof(f32,plain,(
% 2.37/1.01    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.37/1.01    introduced(choice_axiom,[])).
% 2.37/1.01  
% 2.37/1.01  fof(f33,plain,(
% 2.37/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 2.37/1.01  
% 2.37/1.01  fof(f52,plain,(
% 2.37/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.37/1.01    inference(cnf_transformation,[],[f33])).
% 2.37/1.01  
% 2.37/1.01  fof(f77,plain,(
% 2.37/1.01    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.37/1.01    inference(equality_resolution,[],[f52])).
% 2.37/1.01  
% 2.37/1.01  fof(f2,axiom,(
% 2.37/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f23,plain,(
% 2.37/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.37/1.01    inference(nnf_transformation,[],[f2])).
% 2.37/1.01  
% 2.37/1.01  fof(f24,plain,(
% 2.37/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.37/1.01    inference(flattening,[],[f23])).
% 2.37/1.01  
% 2.37/1.01  fof(f25,plain,(
% 2.37/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.37/1.01    inference(rectify,[],[f24])).
% 2.37/1.01  
% 2.37/1.01  fof(f26,plain,(
% 2.37/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.37/1.01    introduced(choice_axiom,[])).
% 2.37/1.01  
% 2.37/1.01  fof(f27,plain,(
% 2.37/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 2.37/1.01  
% 2.37/1.01  fof(f43,plain,(
% 2.37/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.37/1.01    inference(cnf_transformation,[],[f27])).
% 2.37/1.01  
% 2.37/1.01  fof(f69,plain,(
% 2.37/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.37/1.01    inference(definition_unfolding,[],[f43,f49])).
% 2.37/1.01  
% 2.37/1.01  fof(f75,plain,(
% 2.37/1.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.37/1.01    inference(equality_resolution,[],[f69])).
% 2.37/1.01  
% 2.37/1.01  fof(f62,plain,(
% 2.37/1.01    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 2.37/1.01    inference(cnf_transformation,[],[f38])).
% 2.37/1.01  
% 2.37/1.01  fof(f42,plain,(
% 2.37/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.37/1.01    inference(cnf_transformation,[],[f27])).
% 2.37/1.01  
% 2.37/1.01  fof(f70,plain,(
% 2.37/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.37/1.01    inference(definition_unfolding,[],[f42,f49])).
% 2.37/1.01  
% 2.37/1.01  fof(f76,plain,(
% 2.37/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.37/1.01    inference(equality_resolution,[],[f70])).
% 2.37/1.01  
% 2.37/1.01  fof(f40,plain,(
% 2.37/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.37/1.01    inference(cnf_transformation,[],[f22])).
% 2.37/1.01  
% 2.37/1.01  fof(f41,plain,(
% 2.37/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.37/1.01    inference(cnf_transformation,[],[f22])).
% 2.37/1.01  
% 2.37/1.01  fof(f64,plain,(
% 2.37/1.01    k1_subset_1(sK4) != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 2.37/1.01    inference(cnf_transformation,[],[f38])).
% 2.37/1.01  
% 2.37/1.01  fof(f72,plain,(
% 2.37/1.01    k1_xboole_0 != sK5 | ~r1_tarski(sK5,k3_subset_1(sK4,sK5))),
% 2.37/1.01    inference(definition_unfolding,[],[f64,f59])).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1296,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2405,plain,
% 2.37/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2
% 2.37/1.01      | sK5 != X2
% 2.37/1.01      | sK5 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_1296]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_4635,plain,
% 2.37/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 2.37/1.01      | sK5 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 2.37/1.01      | sK5 != k1_xboole_0 ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_2405]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_4637,plain,
% 2.37/1.01      ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) != k1_xboole_0
% 2.37/1.01      | sK5 = k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))
% 2.37/1.01      | sK5 != k1_xboole_0 ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_4635]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2,plain,
% 2.37/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.37/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1961,plain,
% 2.37/1.01      ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),X0)
% 2.37/1.01      | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5)
% 2.37/1.01      | ~ r1_tarski(sK5,X0) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_4010,plain,
% 2.37/1.01      ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))
% 2.37/1.01      | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5)
% 2.37/1.01      | ~ r1_tarski(sK5,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_1961]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_4014,plain,
% 2.37/1.01      ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)))
% 2.37/1.01      | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5)
% 2.37/1.01      | ~ r1_tarski(sK5,k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_4010]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_9,plain,
% 2.37/1.01      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.37/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1757,plain,
% 2.37/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.37/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_22,negated_conjecture,
% 2.37/1.01      ( r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 = sK5 ),
% 2.37/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1750,plain,
% 2.37/1.01      ( k1_xboole_0 = sK5
% 2.37/1.01      | r1_tarski(sK5,k3_subset_1(sK4,sK5)) = iProver_top ),
% 2.37/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_17,plain,
% 2.37/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.37/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_19,plain,
% 2.37/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.37/1.01      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.37/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_327,plain,
% 2.37/1.01      ( ~ r2_hidden(X0,X1)
% 2.37/1.01      | v1_xboole_0(X1)
% 2.37/1.01      | X2 != X0
% 2.37/1.01      | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
% 2.37/1.01      | k1_zfmisc_1(X3) != X1 ),
% 2.37/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_328,plain,
% 2.37/1.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 2.37/1.01      | v1_xboole_0(k1_zfmisc_1(X1))
% 2.37/1.01      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.37/1.01      inference(unflattening,[status(thm)],[c_327]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_20,plain,
% 2.37/1.01      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.37/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_338,plain,
% 2.37/1.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 2.37/1.01      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.37/1.01      inference(forward_subsumption_resolution,
% 2.37/1.01                [status(thm)],
% 2.37/1.01                [c_328,c_20]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_13,plain,
% 2.37/1.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.37/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_794,plain,
% 2.37/1.01      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.37/1.01      inference(prop_impl,[status(thm)],[c_13]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_795,plain,
% 2.37/1.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.37/1.01      inference(renaming,[status(thm)],[c_794]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_840,plain,
% 2.37/1.01      ( ~ r1_tarski(X0,X1)
% 2.37/1.01      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.37/1.01      inference(bin_hyper_res,[status(thm)],[c_338,c_795]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1748,plain,
% 2.37/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.37/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.37/1.01      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2077,plain,
% 2.37/1.01      ( k5_xboole_0(k3_subset_1(sK4,sK5),k3_xboole_0(k3_subset_1(sK4,sK5),sK5)) = k3_subset_1(k3_subset_1(sK4,sK5),sK5)
% 2.37/1.01      | sK5 = k1_xboole_0 ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_1750,c_1748]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_7,plain,
% 2.37/1.01      ( ~ r2_hidden(X0,X1)
% 2.37/1.01      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 2.37/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1759,plain,
% 2.37/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.37/1.01      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 2.37/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2957,plain,
% 2.37/1.01      ( sK5 = k1_xboole_0
% 2.37/1.01      | r2_hidden(X0,k3_subset_1(k3_subset_1(sK4,sK5),sK5)) != iProver_top
% 2.37/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_2077,c_1759]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_193,plain,
% 2.37/1.01      ( r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 = sK5 ),
% 2.37/1.01      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_614,plain,
% 2.37/1.01      ( ~ r2_hidden(X0,X1)
% 2.37/1.01      | r2_hidden(X0,X2)
% 2.37/1.01      | k3_subset_1(sK4,sK5) != X2
% 2.37/1.01      | sK5 != X1
% 2.37/1.01      | sK5 = k1_xboole_0 ),
% 2.37/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_193]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_615,plain,
% 2.37/1.01      ( r2_hidden(X0,k3_subset_1(sK4,sK5))
% 2.37/1.01      | ~ r2_hidden(X0,sK5)
% 2.37/1.01      | sK5 = k1_xboole_0 ),
% 2.37/1.01      inference(unflattening,[status(thm)],[c_614]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_616,plain,
% 2.37/1.01      ( sK5 = k1_xboole_0
% 2.37/1.01      | r2_hidden(X0,k3_subset_1(sK4,sK5)) = iProver_top
% 2.37/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 2.37/1.01      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_23,negated_conjecture,
% 2.37/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 2.37/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_360,plain,
% 2.37/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.37/1.01      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
% 2.37/1.01      | sK5 != X1 ),
% 2.37/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_361,plain,
% 2.37/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,sK5)) = k3_subset_1(X0,sK5)
% 2.37/1.01      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
% 2.37/1.01      inference(unflattening,[status(thm)],[c_360]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1912,plain,
% 2.37/1.01      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
% 2.37/1.01      inference(equality_resolution,[status(thm)],[c_361]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2958,plain,
% 2.37/1.01      ( r2_hidden(X0,k3_subset_1(sK4,sK5)) != iProver_top
% 2.37/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_1912,c_1759]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_3842,plain,
% 2.37/1.01      ( sK5 = k1_xboole_0 | r2_hidden(X0,sK5) != iProver_top ),
% 2.37/1.01      inference(global_propositional_subsumption,
% 2.37/1.01                [status(thm)],
% 2.37/1.01                [c_2957,c_616,c_2958]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_3851,plain,
% 2.37/1.01      ( sK5 = k1_xboole_0 ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_1757,c_3842]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2263,plain,
% 2.37/1.01      ( X0 != X1
% 2.37/1.01      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1
% 2.37/1.01      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) = X0 ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_1296]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_3297,plain,
% 2.37/1.01      ( X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
% 2.37/1.01      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X0
% 2.37/1.01      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_2263]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_3298,plain,
% 2.37/1.01      ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) != k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))
% 2.37/1.01      | k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) = sK5
% 2.37/1.01      | sK5 != k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_3297]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2955,plain,
% 2.37/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 2.37/1.01      | r2_hidden(sK2(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_1757,c_1759]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_3007,plain,
% 2.37/1.01      ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) = k1_xboole_0
% 2.37/1.01      | r2_hidden(sK2(k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))),sK5) != iProver_top ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_2955]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_8,plain,
% 2.37/1.01      ( r2_hidden(X0,X1)
% 2.37/1.01      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 2.37/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1758,plain,
% 2.37/1.01      ( r2_hidden(X0,X1) = iProver_top
% 2.37/1.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 2.37/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2729,plain,
% 2.37/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 2.37/1.01      | r2_hidden(sK2(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) = iProver_top ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_1757,c_1758]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2761,plain,
% 2.37/1.01      ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) = k1_xboole_0
% 2.37/1.01      | r2_hidden(sK2(k5_xboole_0(sK5,k3_xboole_0(sK5,sK5))),sK5) = iProver_top ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_2729]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1,plain,
% 2.37/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.37/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1765,plain,
% 2.37/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.37/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.37/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_0,plain,
% 2.37/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.37/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1766,plain,
% 2.37/1.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.37/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.37/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2323,plain,
% 2.37/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_1765,c_1766]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2331,plain,
% 2.37/1.01      ( r1_tarski(X0,X0) ),
% 2.37/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2323]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2333,plain,
% 2.37/1.01      ( r1_tarski(sK5,sK5) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_2331]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1295,plain,( X0 = X0 ),theory(equality) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2259,plain,
% 2.37/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_1295]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2262,plain,
% 2.37/1.01      ( k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) = k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_2259]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1297,plain,
% 2.37/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.37/1.01      theory(equality) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2138,plain,
% 2.37/1.01      ( ~ r1_tarski(X0,X1)
% 2.37/1.01      | r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
% 2.37/1.01      | X2 != X0
% 2.37/1.01      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_1297]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2140,plain,
% 2.37/1.01      ( r1_tarski(sK5,k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)))
% 2.37/1.01      | ~ r1_tarski(sK5,sK5)
% 2.37/1.01      | k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)) != sK5
% 2.37/1.01      | sK5 != sK5 ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_2138]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1959,plain,
% 2.37/1.01      ( ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),k5_xboole_0(X0,k3_xboole_0(X0,sK5)))
% 2.37/1.01      | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1969,plain,
% 2.37/1.01      ( ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),k5_xboole_0(sK5,k3_xboole_0(sK5,sK5)))
% 2.37/1.01      | ~ r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5) ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_1959]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1310,plain,
% 2.37/1.01      ( sK5 = sK5 ),
% 2.37/1.01      inference(instantiation,[status(thm)],[c_1295]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_21,negated_conjecture,
% 2.37/1.01      ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 != sK5 ),
% 2.37/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_191,plain,
% 2.37/1.01      ( ~ r1_tarski(sK5,k3_subset_1(sK4,sK5)) | k1_xboole_0 != sK5 ),
% 2.37/1.01      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_558,plain,
% 2.37/1.01      ( r2_hidden(sK0(X0,X1),X0)
% 2.37/1.01      | k3_subset_1(sK4,sK5) != X1
% 2.37/1.01      | sK5 != X0
% 2.37/1.01      | sK5 != k1_xboole_0 ),
% 2.37/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_191]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_559,plain,
% 2.37/1.01      ( r2_hidden(sK0(sK5,k3_subset_1(sK4,sK5)),sK5)
% 2.37/1.01      | sK5 != k1_xboole_0 ),
% 2.37/1.01      inference(unflattening,[status(thm)],[c_558]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(contradiction,plain,
% 2.37/1.01      ( $false ),
% 2.37/1.01      inference(minisat,
% 2.37/1.01                [status(thm)],
% 2.37/1.01                [c_4637,c_4014,c_3851,c_3298,c_3007,c_2761,c_2333,c_2262,
% 2.37/1.01                 c_2140,c_1969,c_1310,c_559]) ).
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.37/1.01  
% 2.37/1.01  ------                               Statistics
% 2.37/1.01  
% 2.37/1.01  ------ General
% 2.37/1.01  
% 2.37/1.01  abstr_ref_over_cycles:                  0
% 2.37/1.01  abstr_ref_under_cycles:                 0
% 2.37/1.01  gc_basic_clause_elim:                   0
% 2.37/1.01  forced_gc_time:                         0
% 2.37/1.01  parsing_time:                           0.009
% 2.37/1.01  unif_index_cands_time:                  0.
% 2.37/1.01  unif_index_add_time:                    0.
% 2.37/1.01  orderings_time:                         0.
% 2.37/1.01  out_proof_time:                         0.01
% 2.37/1.01  total_time:                             0.182
% 2.37/1.01  num_of_symbols:                         46
% 2.37/1.01  num_of_terms:                           4574
% 2.37/1.01  
% 2.37/1.01  ------ Preprocessing
% 2.37/1.01  
% 2.37/1.01  num_of_splits:                          0
% 2.37/1.01  num_of_split_atoms:                     0
% 2.37/1.01  num_of_reused_defs:                     0
% 2.37/1.01  num_eq_ax_congr_red:                    31
% 2.37/1.01  num_of_sem_filtered_clauses:            1
% 2.37/1.01  num_of_subtypes:                        0
% 2.37/1.01  monotx_restored_types:                  0
% 2.37/1.01  sat_num_of_epr_types:                   0
% 2.37/1.01  sat_num_of_non_cyclic_types:            0
% 2.37/1.01  sat_guarded_non_collapsed_types:        0
% 2.37/1.01  num_pure_diseq_elim:                    0
% 2.37/1.01  simp_replaced_by:                       0
% 2.37/1.01  res_preprocessed:                       101
% 2.37/1.01  prep_upred:                             0
% 2.37/1.01  prep_unflattend:                        77
% 2.37/1.01  smt_new_axioms:                         0
% 2.37/1.01  pred_elim_cands:                        2
% 2.37/1.01  pred_elim:                              2
% 2.37/1.01  pred_elim_cl:                           4
% 2.37/1.01  pred_elim_cycles:                       4
% 2.37/1.01  merged_defs:                            16
% 2.37/1.01  merged_defs_ncl:                        0
% 2.37/1.01  bin_hyper_res:                          17
% 2.37/1.01  prep_cycles:                            4
% 2.37/1.01  pred_elim_time:                         0.011
% 2.37/1.01  splitting_time:                         0.
% 2.37/1.01  sem_filter_time:                        0.
% 2.37/1.01  monotx_time:                            0.
% 2.37/1.01  subtype_inf_time:                       0.
% 2.37/1.01  
% 2.37/1.01  ------ Problem properties
% 2.37/1.01  
% 2.37/1.01  clauses:                                20
% 2.37/1.01  conjectures:                            2
% 2.37/1.01  epr:                                    1
% 2.37/1.01  horn:                                   12
% 2.37/1.01  ground:                                 3
% 2.37/1.01  unary:                                  1
% 2.37/1.01  binary:                                 12
% 2.37/1.01  lits:                                   47
% 2.37/1.01  lits_eq:                                12
% 2.37/1.01  fd_pure:                                0
% 2.37/1.01  fd_pseudo:                              0
% 2.37/1.01  fd_cond:                                1
% 2.37/1.01  fd_pseudo_cond:                         5
% 2.37/1.01  ac_symbols:                             0
% 2.37/1.01  
% 2.37/1.01  ------ Propositional Solver
% 2.37/1.01  
% 2.37/1.01  prop_solver_calls:                      27
% 2.37/1.01  prop_fast_solver_calls:                 697
% 2.37/1.01  smt_solver_calls:                       0
% 2.37/1.01  smt_fast_solver_calls:                  0
% 2.37/1.01  prop_num_of_clauses:                    1537
% 2.37/1.01  prop_preprocess_simplified:             4948
% 2.37/1.01  prop_fo_subsumed:                       1
% 2.37/1.01  prop_solver_time:                       0.
% 2.37/1.01  smt_solver_time:                        0.
% 2.37/1.01  smt_fast_solver_time:                   0.
% 2.37/1.01  prop_fast_solver_time:                  0.
% 2.37/1.01  prop_unsat_core_time:                   0.
% 2.37/1.01  
% 2.37/1.01  ------ QBF
% 2.37/1.01  
% 2.37/1.01  qbf_q_res:                              0
% 2.37/1.01  qbf_num_tautologies:                    0
% 2.37/1.01  qbf_prep_cycles:                        0
% 2.37/1.01  
% 2.37/1.01  ------ BMC1
% 2.37/1.01  
% 2.37/1.01  bmc1_current_bound:                     -1
% 2.37/1.01  bmc1_last_solved_bound:                 -1
% 2.37/1.01  bmc1_unsat_core_size:                   -1
% 2.37/1.01  bmc1_unsat_core_parents_size:           -1
% 2.37/1.01  bmc1_merge_next_fun:                    0
% 2.37/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.37/1.01  
% 2.37/1.01  ------ Instantiation
% 2.37/1.01  
% 2.37/1.01  inst_num_of_clauses:                    366
% 2.37/1.01  inst_num_in_passive:                    124
% 2.37/1.01  inst_num_in_active:                     132
% 2.37/1.01  inst_num_in_unprocessed:                109
% 2.37/1.01  inst_num_of_loops:                      175
% 2.37/1.01  inst_num_of_learning_restarts:          0
% 2.37/1.01  inst_num_moves_active_passive:          39
% 2.37/1.01  inst_lit_activity:                      0
% 2.37/1.01  inst_lit_activity_moves:                0
% 2.37/1.01  inst_num_tautologies:                   0
% 2.37/1.01  inst_num_prop_implied:                  0
% 2.37/1.01  inst_num_existing_simplified:           0
% 2.37/1.01  inst_num_eq_res_simplified:             0
% 2.37/1.01  inst_num_child_elim:                    0
% 2.37/1.01  inst_num_of_dismatching_blockings:      159
% 2.37/1.01  inst_num_of_non_proper_insts:           276
% 2.37/1.01  inst_num_of_duplicates:                 0
% 2.37/1.01  inst_inst_num_from_inst_to_res:         0
% 2.37/1.01  inst_dismatching_checking_time:         0.
% 2.37/1.01  
% 2.37/1.01  ------ Resolution
% 2.37/1.01  
% 2.37/1.01  res_num_of_clauses:                     0
% 2.37/1.01  res_num_in_passive:                     0
% 2.37/1.01  res_num_in_active:                      0
% 2.37/1.01  res_num_of_loops:                       105
% 2.37/1.01  res_forward_subset_subsumed:            8
% 2.37/1.01  res_backward_subset_subsumed:           0
% 2.37/1.01  res_forward_subsumed:                   2
% 2.37/1.01  res_backward_subsumed:                  0
% 2.37/1.01  res_forward_subsumption_resolution:     2
% 2.37/1.01  res_backward_subsumption_resolution:    0
% 2.37/1.01  res_clause_to_clause_subsumption:       316
% 2.37/1.01  res_orphan_elimination:                 0
% 2.37/1.01  res_tautology_del:                      53
% 2.37/1.01  res_num_eq_res_simplified:              0
% 2.37/1.01  res_num_sel_changes:                    0
% 2.37/1.01  res_moves_from_active_to_pass:          0
% 2.37/1.01  
% 2.37/1.01  ------ Superposition
% 2.37/1.01  
% 2.37/1.01  sup_time_total:                         0.
% 2.37/1.01  sup_time_generating:                    0.
% 2.37/1.01  sup_time_sim_full:                      0.
% 2.37/1.01  sup_time_sim_immed:                     0.
% 2.37/1.01  
% 2.37/1.01  sup_num_of_clauses:                     86
% 2.37/1.01  sup_num_in_active:                      21
% 2.37/1.01  sup_num_in_passive:                     65
% 2.37/1.01  sup_num_of_loops:                       34
% 2.37/1.01  sup_fw_superposition:                   51
% 2.37/1.01  sup_bw_superposition:                   35
% 2.37/1.01  sup_immediate_simplified:               8
% 2.37/1.01  sup_given_eliminated:                   0
% 2.37/1.01  comparisons_done:                       0
% 2.37/1.01  comparisons_avoided:                    3
% 2.37/1.01  
% 2.37/1.01  ------ Simplifications
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  sim_fw_subset_subsumed:                 1
% 2.37/1.01  sim_bw_subset_subsumed:                 6
% 2.37/1.01  sim_fw_subsumed:                        3
% 2.37/1.01  sim_bw_subsumed:                        0
% 2.37/1.01  sim_fw_subsumption_res:                 0
% 2.37/1.01  sim_bw_subsumption_res:                 0
% 2.37/1.01  sim_tautology_del:                      9
% 2.37/1.01  sim_eq_tautology_del:                   4
% 2.37/1.01  sim_eq_res_simp:                        2
% 2.37/1.01  sim_fw_demodulated:                     0
% 2.37/1.01  sim_bw_demodulated:                     14
% 2.37/1.01  sim_light_normalised:                   1
% 2.37/1.01  sim_joinable_taut:                      0
% 2.37/1.01  sim_joinable_simp:                      0
% 2.37/1.01  sim_ac_normalised:                      0
% 2.37/1.01  sim_smt_subsumption:                    0
% 2.37/1.01  
%------------------------------------------------------------------------------
