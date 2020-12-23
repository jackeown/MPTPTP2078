%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:16 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 285 expanded)
%              Number of clauses        :   53 ( 101 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  356 ( 798 expanded)
%              Number of equality atoms :  112 ( 256 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f43])).

fof(f74,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f60])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f59,f76,f57])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f73,f76])).

fof(f75,plain,(
    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1141,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1145,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2262,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1145])).

cnf(c_24,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_34,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2820,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_34])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1148,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2827,plain,
    ( r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2820,c_1148])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1152,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3032,plain,
    ( k3_xboole_0(sK5,sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_2827,c_1152])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1449,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_13])).

cnf(c_3209,plain,
    ( k3_tarski(k1_enumset1(sK5,sK5,k5_xboole_0(sK4,sK5))) = sK4 ),
    inference(superposition,[status(thm)],[c_3032,c_1449])).

cnf(c_3215,plain,
    ( k3_xboole_0(sK4,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_3032,c_0])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1144,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2589,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1141,c_1144])).

cnf(c_3892,plain,
    ( k3_subset_1(sK4,sK5) = k5_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3215,c_2589])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1160,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1153,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2809,plain,
    ( r2_hidden(X0,k3_subset_1(sK4,sK5)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_1153])).

cnf(c_3193,plain,
    ( r1_tarski(k3_subset_1(sK4,sK5),X0) = iProver_top
    | r2_hidden(sK1(k3_subset_1(sK4,sK5),X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_2809])).

cnf(c_4359,plain,
    ( r1_tarski(k5_xboole_0(sK4,sK5),X0) = iProver_top
    | r2_hidden(sK1(k5_xboole_0(sK4,sK5),X0),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3892,c_3193])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1161,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4921,plain,
    ( r1_tarski(k5_xboole_0(sK4,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4359,c_1161])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1149,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_145,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_2])).

cnf(c_146,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_1140,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_1547,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_1140])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k1_enumset1(X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1142,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1444,plain,
    ( k3_tarski(k1_enumset1(sK5,sK5,X0)) = k4_subset_1(sK4,sK5,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1142])).

cnf(c_1702,plain,
    ( k3_tarski(k1_enumset1(sK5,sK5,X0)) = k4_subset_1(sK4,sK5,X0)
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1444])).

cnf(c_4944,plain,
    ( k3_tarski(k1_enumset1(sK5,sK5,k5_xboole_0(sK4,sK5))) = k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_4921,c_1702])).

cnf(c_5219,plain,
    ( k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_3209,c_4944])).

cnf(c_26,negated_conjecture,
    ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1172,plain,
    ( k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) != sK4 ),
    inference(demodulation,[status(thm)],[c_26,c_22])).

cnf(c_4362,plain,
    ( k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) != sK4 ),
    inference(demodulation,[status(thm)],[c_3892,c_1172])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5219,c_4362])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.97/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/1.00  
% 2.97/1.00  ------  iProver source info
% 2.97/1.00  
% 2.97/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.97/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/1.00  git: non_committed_changes: false
% 2.97/1.00  git: last_make_outside_of_git: false
% 2.97/1.00  
% 2.97/1.00  ------ 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options
% 2.97/1.00  
% 2.97/1.00  --out_options                           all
% 2.97/1.00  --tptp_safe_out                         true
% 2.97/1.00  --problem_path                          ""
% 2.97/1.00  --include_path                          ""
% 2.97/1.00  --clausifier                            res/vclausify_rel
% 2.97/1.00  --clausifier_options                    --mode clausify
% 2.97/1.00  --stdin                                 false
% 2.97/1.00  --stats_out                             all
% 2.97/1.00  
% 2.97/1.00  ------ General Options
% 2.97/1.00  
% 2.97/1.00  --fof                                   false
% 2.97/1.00  --time_out_real                         305.
% 2.97/1.00  --time_out_virtual                      -1.
% 2.97/1.00  --symbol_type_check                     false
% 2.97/1.00  --clausify_out                          false
% 2.97/1.00  --sig_cnt_out                           false
% 2.97/1.00  --trig_cnt_out                          false
% 2.97/1.00  --trig_cnt_out_tolerance                1.
% 2.97/1.00  --trig_cnt_out_sk_spl                   false
% 2.97/1.00  --abstr_cl_out                          false
% 2.97/1.00  
% 2.97/1.00  ------ Global Options
% 2.97/1.00  
% 2.97/1.00  --schedule                              default
% 2.97/1.00  --add_important_lit                     false
% 2.97/1.00  --prop_solver_per_cl                    1000
% 2.97/1.00  --min_unsat_core                        false
% 2.97/1.00  --soft_assumptions                      false
% 2.97/1.00  --soft_lemma_size                       3
% 2.97/1.00  --prop_impl_unit_size                   0
% 2.97/1.00  --prop_impl_unit                        []
% 2.97/1.00  --share_sel_clauses                     true
% 2.97/1.00  --reset_solvers                         false
% 2.97/1.00  --bc_imp_inh                            [conj_cone]
% 2.97/1.00  --conj_cone_tolerance                   3.
% 2.97/1.00  --extra_neg_conj                        none
% 2.97/1.00  --large_theory_mode                     true
% 2.97/1.00  --prolific_symb_bound                   200
% 2.97/1.00  --lt_threshold                          2000
% 2.97/1.00  --clause_weak_htbl                      true
% 2.97/1.00  --gc_record_bc_elim                     false
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing Options
% 2.97/1.00  
% 2.97/1.00  --preprocessing_flag                    true
% 2.97/1.00  --time_out_prep_mult                    0.1
% 2.97/1.00  --splitting_mode                        input
% 2.97/1.00  --splitting_grd                         true
% 2.97/1.00  --splitting_cvd                         false
% 2.97/1.00  --splitting_cvd_svl                     false
% 2.97/1.00  --splitting_nvd                         32
% 2.97/1.00  --sub_typing                            true
% 2.97/1.00  --prep_gs_sim                           true
% 2.97/1.00  --prep_unflatten                        true
% 2.97/1.00  --prep_res_sim                          true
% 2.97/1.00  --prep_upred                            true
% 2.97/1.00  --prep_sem_filter                       exhaustive
% 2.97/1.00  --prep_sem_filter_out                   false
% 2.97/1.00  --pred_elim                             true
% 2.97/1.00  --res_sim_input                         true
% 2.97/1.00  --eq_ax_congr_red                       true
% 2.97/1.00  --pure_diseq_elim                       true
% 2.97/1.00  --brand_transform                       false
% 2.97/1.00  --non_eq_to_eq                          false
% 2.97/1.00  --prep_def_merge                        true
% 2.97/1.00  --prep_def_merge_prop_impl              false
% 2.97/1.00  --prep_def_merge_mbd                    true
% 2.97/1.00  --prep_def_merge_tr_red                 false
% 2.97/1.00  --prep_def_merge_tr_cl                  false
% 2.97/1.00  --smt_preprocessing                     true
% 2.97/1.00  --smt_ac_axioms                         fast
% 2.97/1.00  --preprocessed_out                      false
% 2.97/1.00  --preprocessed_stats                    false
% 2.97/1.00  
% 2.97/1.00  ------ Abstraction refinement Options
% 2.97/1.00  
% 2.97/1.00  --abstr_ref                             []
% 2.97/1.00  --abstr_ref_prep                        false
% 2.97/1.00  --abstr_ref_until_sat                   false
% 2.97/1.00  --abstr_ref_sig_restrict                funpre
% 2.97/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.00  --abstr_ref_under                       []
% 2.97/1.00  
% 2.97/1.00  ------ SAT Options
% 2.97/1.00  
% 2.97/1.00  --sat_mode                              false
% 2.97/1.00  --sat_fm_restart_options                ""
% 2.97/1.00  --sat_gr_def                            false
% 2.97/1.00  --sat_epr_types                         true
% 2.97/1.00  --sat_non_cyclic_types                  false
% 2.97/1.00  --sat_finite_models                     false
% 2.97/1.00  --sat_fm_lemmas                         false
% 2.97/1.00  --sat_fm_prep                           false
% 2.97/1.00  --sat_fm_uc_incr                        true
% 2.97/1.00  --sat_out_model                         small
% 2.97/1.00  --sat_out_clauses                       false
% 2.97/1.00  
% 2.97/1.00  ------ QBF Options
% 2.97/1.00  
% 2.97/1.00  --qbf_mode                              false
% 2.97/1.00  --qbf_elim_univ                         false
% 2.97/1.00  --qbf_dom_inst                          none
% 2.97/1.00  --qbf_dom_pre_inst                      false
% 2.97/1.00  --qbf_sk_in                             false
% 2.97/1.00  --qbf_pred_elim                         true
% 2.97/1.00  --qbf_split                             512
% 2.97/1.00  
% 2.97/1.00  ------ BMC1 Options
% 2.97/1.00  
% 2.97/1.00  --bmc1_incremental                      false
% 2.97/1.00  --bmc1_axioms                           reachable_all
% 2.97/1.00  --bmc1_min_bound                        0
% 2.97/1.00  --bmc1_max_bound                        -1
% 2.97/1.00  --bmc1_max_bound_default                -1
% 2.97/1.00  --bmc1_symbol_reachability              true
% 2.97/1.00  --bmc1_property_lemmas                  false
% 2.97/1.00  --bmc1_k_induction                      false
% 2.97/1.00  --bmc1_non_equiv_states                 false
% 2.97/1.00  --bmc1_deadlock                         false
% 2.97/1.00  --bmc1_ucm                              false
% 2.97/1.00  --bmc1_add_unsat_core                   none
% 2.97/1.00  --bmc1_unsat_core_children              false
% 2.97/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.00  --bmc1_out_stat                         full
% 2.97/1.00  --bmc1_ground_init                      false
% 2.97/1.00  --bmc1_pre_inst_next_state              false
% 2.97/1.00  --bmc1_pre_inst_state                   false
% 2.97/1.00  --bmc1_pre_inst_reach_state             false
% 2.97/1.00  --bmc1_out_unsat_core                   false
% 2.97/1.00  --bmc1_aig_witness_out                  false
% 2.97/1.00  --bmc1_verbose                          false
% 2.97/1.00  --bmc1_dump_clauses_tptp                false
% 2.97/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.00  --bmc1_dump_file                        -
% 2.97/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.00  --bmc1_ucm_extend_mode                  1
% 2.97/1.00  --bmc1_ucm_init_mode                    2
% 2.97/1.00  --bmc1_ucm_cone_mode                    none
% 2.97/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.00  --bmc1_ucm_relax_model                  4
% 2.97/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.00  --bmc1_ucm_layered_model                none
% 2.97/1.00  --bmc1_ucm_max_lemma_size               10
% 2.97/1.00  
% 2.97/1.00  ------ AIG Options
% 2.97/1.00  
% 2.97/1.00  --aig_mode                              false
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation Options
% 2.97/1.00  
% 2.97/1.00  --instantiation_flag                    true
% 2.97/1.00  --inst_sos_flag                         false
% 2.97/1.00  --inst_sos_phase                        true
% 2.97/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel_side                     num_symb
% 2.97/1.00  --inst_solver_per_active                1400
% 2.97/1.00  --inst_solver_calls_frac                1.
% 2.97/1.00  --inst_passive_queue_type               priority_queues
% 2.97/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.00  --inst_passive_queues_freq              [25;2]
% 2.97/1.00  --inst_dismatching                      true
% 2.97/1.00  --inst_eager_unprocessed_to_passive     true
% 2.97/1.00  --inst_prop_sim_given                   true
% 2.97/1.00  --inst_prop_sim_new                     false
% 2.97/1.00  --inst_subs_new                         false
% 2.97/1.00  --inst_eq_res_simp                      false
% 2.97/1.00  --inst_subs_given                       false
% 2.97/1.00  --inst_orphan_elimination               true
% 2.97/1.00  --inst_learning_loop_flag               true
% 2.97/1.00  --inst_learning_start                   3000
% 2.97/1.00  --inst_learning_factor                  2
% 2.97/1.00  --inst_start_prop_sim_after_learn       3
% 2.97/1.00  --inst_sel_renew                        solver
% 2.97/1.00  --inst_lit_activity_flag                true
% 2.97/1.00  --inst_restr_to_given                   false
% 2.97/1.00  --inst_activity_threshold               500
% 2.97/1.00  --inst_out_proof                        true
% 2.97/1.00  
% 2.97/1.00  ------ Resolution Options
% 2.97/1.00  
% 2.97/1.00  --resolution_flag                       true
% 2.97/1.00  --res_lit_sel                           adaptive
% 2.97/1.00  --res_lit_sel_side                      none
% 2.97/1.00  --res_ordering                          kbo
% 2.97/1.00  --res_to_prop_solver                    active
% 2.97/1.00  --res_prop_simpl_new                    false
% 2.97/1.00  --res_prop_simpl_given                  true
% 2.97/1.00  --res_passive_queue_type                priority_queues
% 2.97/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.00  --res_passive_queues_freq               [15;5]
% 2.97/1.00  --res_forward_subs                      full
% 2.97/1.00  --res_backward_subs                     full
% 2.97/1.00  --res_forward_subs_resolution           true
% 2.97/1.00  --res_backward_subs_resolution          true
% 2.97/1.00  --res_orphan_elimination                true
% 2.97/1.00  --res_time_limit                        2.
% 2.97/1.00  --res_out_proof                         true
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Options
% 2.97/1.00  
% 2.97/1.00  --superposition_flag                    true
% 2.97/1.00  --sup_passive_queue_type                priority_queues
% 2.97/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.00  --demod_completeness_check              fast
% 2.97/1.00  --demod_use_ground                      true
% 2.97/1.00  --sup_to_prop_solver                    passive
% 2.97/1.00  --sup_prop_simpl_new                    true
% 2.97/1.00  --sup_prop_simpl_given                  true
% 2.97/1.00  --sup_fun_splitting                     false
% 2.97/1.00  --sup_smt_interval                      50000
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Simplification Setup
% 2.97/1.00  
% 2.97/1.00  --sup_indices_passive                   []
% 2.97/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_full_bw                           [BwDemod]
% 2.97/1.00  --sup_immed_triv                        [TrivRules]
% 2.97/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_immed_bw_main                     []
% 2.97/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  
% 2.97/1.00  ------ Combination Options
% 2.97/1.00  
% 2.97/1.00  --comb_res_mult                         3
% 2.97/1.00  --comb_sup_mult                         2
% 2.97/1.00  --comb_inst_mult                        10
% 2.97/1.00  
% 2.97/1.00  ------ Debug Options
% 2.97/1.00  
% 2.97/1.00  --dbg_backtrace                         false
% 2.97/1.00  --dbg_dump_prop_clauses                 false
% 2.97/1.00  --dbg_dump_prop_clauses_file            -
% 2.97/1.00  --dbg_out_stat                          false
% 2.97/1.00  ------ Parsing...
% 2.97/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/1.00  ------ Proving...
% 2.97/1.00  ------ Problem Properties 
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  clauses                                 28
% 2.97/1.00  conjectures                             2
% 2.97/1.00  EPR                                     6
% 2.97/1.00  Horn                                    20
% 2.97/1.00  unary                                   6
% 2.97/1.00  binary                                  11
% 2.97/1.00  lits                                    62
% 2.97/1.00  lits eq                                 12
% 2.97/1.00  fd_pure                                 0
% 2.97/1.00  fd_pseudo                               0
% 2.97/1.00  fd_cond                                 0
% 2.97/1.00  fd_pseudo_cond                          5
% 2.97/1.00  AC symbols                              0
% 2.97/1.00  
% 2.97/1.00  ------ Schedule dynamic 5 is on 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  ------ 
% 2.97/1.00  Current options:
% 2.97/1.00  ------ 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options
% 2.97/1.00  
% 2.97/1.00  --out_options                           all
% 2.97/1.00  --tptp_safe_out                         true
% 2.97/1.00  --problem_path                          ""
% 2.97/1.00  --include_path                          ""
% 2.97/1.00  --clausifier                            res/vclausify_rel
% 2.97/1.00  --clausifier_options                    --mode clausify
% 2.97/1.00  --stdin                                 false
% 2.97/1.00  --stats_out                             all
% 2.97/1.00  
% 2.97/1.00  ------ General Options
% 2.97/1.00  
% 2.97/1.00  --fof                                   false
% 2.97/1.00  --time_out_real                         305.
% 2.97/1.00  --time_out_virtual                      -1.
% 2.97/1.00  --symbol_type_check                     false
% 2.97/1.00  --clausify_out                          false
% 2.97/1.00  --sig_cnt_out                           false
% 2.97/1.00  --trig_cnt_out                          false
% 2.97/1.00  --trig_cnt_out_tolerance                1.
% 2.97/1.00  --trig_cnt_out_sk_spl                   false
% 2.97/1.00  --abstr_cl_out                          false
% 2.97/1.00  
% 2.97/1.00  ------ Global Options
% 2.97/1.00  
% 2.97/1.00  --schedule                              default
% 2.97/1.00  --add_important_lit                     false
% 2.97/1.00  --prop_solver_per_cl                    1000
% 2.97/1.00  --min_unsat_core                        false
% 2.97/1.00  --soft_assumptions                      false
% 2.97/1.00  --soft_lemma_size                       3
% 2.97/1.00  --prop_impl_unit_size                   0
% 2.97/1.00  --prop_impl_unit                        []
% 2.97/1.00  --share_sel_clauses                     true
% 2.97/1.00  --reset_solvers                         false
% 2.97/1.00  --bc_imp_inh                            [conj_cone]
% 2.97/1.00  --conj_cone_tolerance                   3.
% 2.97/1.00  --extra_neg_conj                        none
% 2.97/1.00  --large_theory_mode                     true
% 2.97/1.00  --prolific_symb_bound                   200
% 2.97/1.00  --lt_threshold                          2000
% 2.97/1.00  --clause_weak_htbl                      true
% 2.97/1.00  --gc_record_bc_elim                     false
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing Options
% 2.97/1.00  
% 2.97/1.00  --preprocessing_flag                    true
% 2.97/1.00  --time_out_prep_mult                    0.1
% 2.97/1.00  --splitting_mode                        input
% 2.97/1.00  --splitting_grd                         true
% 2.97/1.00  --splitting_cvd                         false
% 2.97/1.00  --splitting_cvd_svl                     false
% 2.97/1.00  --splitting_nvd                         32
% 2.97/1.00  --sub_typing                            true
% 2.97/1.00  --prep_gs_sim                           true
% 2.97/1.00  --prep_unflatten                        true
% 2.97/1.00  --prep_res_sim                          true
% 2.97/1.00  --prep_upred                            true
% 2.97/1.00  --prep_sem_filter                       exhaustive
% 2.97/1.00  --prep_sem_filter_out                   false
% 2.97/1.00  --pred_elim                             true
% 2.97/1.00  --res_sim_input                         true
% 2.97/1.00  --eq_ax_congr_red                       true
% 2.97/1.00  --pure_diseq_elim                       true
% 2.97/1.00  --brand_transform                       false
% 2.97/1.00  --non_eq_to_eq                          false
% 2.97/1.00  --prep_def_merge                        true
% 2.97/1.00  --prep_def_merge_prop_impl              false
% 2.97/1.00  --prep_def_merge_mbd                    true
% 2.97/1.00  --prep_def_merge_tr_red                 false
% 2.97/1.00  --prep_def_merge_tr_cl                  false
% 2.97/1.00  --smt_preprocessing                     true
% 2.97/1.00  --smt_ac_axioms                         fast
% 2.97/1.00  --preprocessed_out                      false
% 2.97/1.00  --preprocessed_stats                    false
% 2.97/1.00  
% 2.97/1.00  ------ Abstraction refinement Options
% 2.97/1.00  
% 2.97/1.00  --abstr_ref                             []
% 2.97/1.00  --abstr_ref_prep                        false
% 2.97/1.00  --abstr_ref_until_sat                   false
% 2.97/1.00  --abstr_ref_sig_restrict                funpre
% 2.97/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.00  --abstr_ref_under                       []
% 2.97/1.00  
% 2.97/1.00  ------ SAT Options
% 2.97/1.00  
% 2.97/1.00  --sat_mode                              false
% 2.97/1.00  --sat_fm_restart_options                ""
% 2.97/1.00  --sat_gr_def                            false
% 2.97/1.00  --sat_epr_types                         true
% 2.97/1.00  --sat_non_cyclic_types                  false
% 2.97/1.00  --sat_finite_models                     false
% 2.97/1.00  --sat_fm_lemmas                         false
% 2.97/1.00  --sat_fm_prep                           false
% 2.97/1.00  --sat_fm_uc_incr                        true
% 2.97/1.00  --sat_out_model                         small
% 2.97/1.00  --sat_out_clauses                       false
% 2.97/1.00  
% 2.97/1.00  ------ QBF Options
% 2.97/1.00  
% 2.97/1.00  --qbf_mode                              false
% 2.97/1.00  --qbf_elim_univ                         false
% 2.97/1.00  --qbf_dom_inst                          none
% 2.97/1.00  --qbf_dom_pre_inst                      false
% 2.97/1.00  --qbf_sk_in                             false
% 2.97/1.00  --qbf_pred_elim                         true
% 2.97/1.00  --qbf_split                             512
% 2.97/1.00  
% 2.97/1.00  ------ BMC1 Options
% 2.97/1.00  
% 2.97/1.00  --bmc1_incremental                      false
% 2.97/1.00  --bmc1_axioms                           reachable_all
% 2.97/1.00  --bmc1_min_bound                        0
% 2.97/1.00  --bmc1_max_bound                        -1
% 2.97/1.00  --bmc1_max_bound_default                -1
% 2.97/1.00  --bmc1_symbol_reachability              true
% 2.97/1.00  --bmc1_property_lemmas                  false
% 2.97/1.00  --bmc1_k_induction                      false
% 2.97/1.00  --bmc1_non_equiv_states                 false
% 2.97/1.00  --bmc1_deadlock                         false
% 2.97/1.00  --bmc1_ucm                              false
% 2.97/1.00  --bmc1_add_unsat_core                   none
% 2.97/1.00  --bmc1_unsat_core_children              false
% 2.97/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.00  --bmc1_out_stat                         full
% 2.97/1.00  --bmc1_ground_init                      false
% 2.97/1.00  --bmc1_pre_inst_next_state              false
% 2.97/1.00  --bmc1_pre_inst_state                   false
% 2.97/1.00  --bmc1_pre_inst_reach_state             false
% 2.97/1.00  --bmc1_out_unsat_core                   false
% 2.97/1.00  --bmc1_aig_witness_out                  false
% 2.97/1.00  --bmc1_verbose                          false
% 2.97/1.00  --bmc1_dump_clauses_tptp                false
% 2.97/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.00  --bmc1_dump_file                        -
% 2.97/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.00  --bmc1_ucm_extend_mode                  1
% 2.97/1.00  --bmc1_ucm_init_mode                    2
% 2.97/1.00  --bmc1_ucm_cone_mode                    none
% 2.97/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.00  --bmc1_ucm_relax_model                  4
% 2.97/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.00  --bmc1_ucm_layered_model                none
% 2.97/1.00  --bmc1_ucm_max_lemma_size               10
% 2.97/1.00  
% 2.97/1.00  ------ AIG Options
% 2.97/1.00  
% 2.97/1.00  --aig_mode                              false
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation Options
% 2.97/1.00  
% 2.97/1.00  --instantiation_flag                    true
% 2.97/1.00  --inst_sos_flag                         false
% 2.97/1.00  --inst_sos_phase                        true
% 2.97/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel_side                     none
% 2.97/1.00  --inst_solver_per_active                1400
% 2.97/1.00  --inst_solver_calls_frac                1.
% 2.97/1.00  --inst_passive_queue_type               priority_queues
% 2.97/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.00  --inst_passive_queues_freq              [25;2]
% 2.97/1.00  --inst_dismatching                      true
% 2.97/1.00  --inst_eager_unprocessed_to_passive     true
% 2.97/1.00  --inst_prop_sim_given                   true
% 2.97/1.00  --inst_prop_sim_new                     false
% 2.97/1.00  --inst_subs_new                         false
% 2.97/1.00  --inst_eq_res_simp                      false
% 2.97/1.00  --inst_subs_given                       false
% 2.97/1.00  --inst_orphan_elimination               true
% 2.97/1.00  --inst_learning_loop_flag               true
% 2.97/1.00  --inst_learning_start                   3000
% 2.97/1.00  --inst_learning_factor                  2
% 2.97/1.00  --inst_start_prop_sim_after_learn       3
% 2.97/1.00  --inst_sel_renew                        solver
% 2.97/1.00  --inst_lit_activity_flag                true
% 2.97/1.00  --inst_restr_to_given                   false
% 2.97/1.00  --inst_activity_threshold               500
% 2.97/1.00  --inst_out_proof                        true
% 2.97/1.00  
% 2.97/1.00  ------ Resolution Options
% 2.97/1.00  
% 2.97/1.00  --resolution_flag                       false
% 2.97/1.00  --res_lit_sel                           adaptive
% 2.97/1.00  --res_lit_sel_side                      none
% 2.97/1.00  --res_ordering                          kbo
% 2.97/1.00  --res_to_prop_solver                    active
% 2.97/1.00  --res_prop_simpl_new                    false
% 2.97/1.00  --res_prop_simpl_given                  true
% 2.97/1.00  --res_passive_queue_type                priority_queues
% 2.97/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.00  --res_passive_queues_freq               [15;5]
% 2.97/1.00  --res_forward_subs                      full
% 2.97/1.00  --res_backward_subs                     full
% 2.97/1.00  --res_forward_subs_resolution           true
% 2.97/1.00  --res_backward_subs_resolution          true
% 2.97/1.00  --res_orphan_elimination                true
% 2.97/1.00  --res_time_limit                        2.
% 2.97/1.00  --res_out_proof                         true
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Options
% 2.97/1.00  
% 2.97/1.00  --superposition_flag                    true
% 2.97/1.00  --sup_passive_queue_type                priority_queues
% 2.97/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.00  --demod_completeness_check              fast
% 2.97/1.00  --demod_use_ground                      true
% 2.97/1.00  --sup_to_prop_solver                    passive
% 2.97/1.00  --sup_prop_simpl_new                    true
% 2.97/1.00  --sup_prop_simpl_given                  true
% 2.97/1.00  --sup_fun_splitting                     false
% 2.97/1.00  --sup_smt_interval                      50000
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Simplification Setup
% 2.97/1.00  
% 2.97/1.00  --sup_indices_passive                   []
% 2.97/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_full_bw                           [BwDemod]
% 2.97/1.00  --sup_immed_triv                        [TrivRules]
% 2.97/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_immed_bw_main                     []
% 2.97/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  
% 2.97/1.00  ------ Combination Options
% 2.97/1.00  
% 2.97/1.00  --comb_res_mult                         3
% 2.97/1.00  --comb_sup_mult                         2
% 2.97/1.00  --comb_inst_mult                        10
% 2.97/1.00  
% 2.97/1.00  ------ Debug Options
% 2.97/1.00  
% 2.97/1.00  --dbg_backtrace                         false
% 2.97/1.00  --dbg_dump_prop_clauses                 false
% 2.97/1.00  --dbg_dump_prop_clauses_file            -
% 2.97/1.00  --dbg_out_stat                          false
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  ------ Proving...
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS status Theorem for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  fof(f16,conjecture,(
% 2.97/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f17,negated_conjecture,(
% 2.97/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.97/1.00    inference(negated_conjecture,[],[f16])).
% 2.97/1.00  
% 2.97/1.00  fof(f24,plain,(
% 2.97/1.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f17])).
% 2.97/1.00  
% 2.97/1.00  fof(f43,plain,(
% 2.97/1.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK4)))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f44,plain,(
% 2.97/1.00    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f43])).
% 2.97/1.00  
% 2.97/1.00  fof(f74,plain,(
% 2.97/1.00    m1_subset_1(sK5,k1_zfmisc_1(sK4))),
% 2.97/1.00    inference(cnf_transformation,[],[f44])).
% 2.97/1.00  
% 2.97/1.00  fof(f11,axiom,(
% 2.97/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f20,plain,(
% 2.97/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f11])).
% 2.97/1.00  
% 2.97/1.00  fof(f42,plain,(
% 2.97/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.97/1.00    inference(nnf_transformation,[],[f20])).
% 2.97/1.00  
% 2.97/1.00  fof(f66,plain,(
% 2.97/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f42])).
% 2.97/1.00  
% 2.97/1.00  fof(f14,axiom,(
% 2.97/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f72,plain,(
% 2.97/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f14])).
% 2.97/1.00  
% 2.97/1.00  fof(f9,axiom,(
% 2.97/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f38,plain,(
% 2.97/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.97/1.00    inference(nnf_transformation,[],[f9])).
% 2.97/1.00  
% 2.97/1.00  fof(f39,plain,(
% 2.97/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.97/1.00    inference(rectify,[],[f38])).
% 2.97/1.00  
% 2.97/1.00  fof(f40,plain,(
% 2.97/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f41,plain,(
% 2.97/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 2.97/1.00  
% 2.97/1.00  fof(f61,plain,(
% 2.97/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.97/1.00    inference(cnf_transformation,[],[f41])).
% 2.97/1.00  
% 2.97/1.00  fof(f90,plain,(
% 2.97/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.97/1.00    inference(equality_resolution,[],[f61])).
% 2.97/1.00  
% 2.97/1.00  fof(f6,axiom,(
% 2.97/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f19,plain,(
% 2.97/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.97/1.00    inference(ennf_transformation,[],[f6])).
% 2.97/1.00  
% 2.97/1.00  fof(f58,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f19])).
% 2.97/1.00  
% 2.97/1.00  fof(f1,axiom,(
% 2.97/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f45,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f1])).
% 2.97/1.00  
% 2.97/1.00  fof(f7,axiom,(
% 2.97/1.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f59,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.97/1.00    inference(cnf_transformation,[],[f7])).
% 2.97/1.00  
% 2.97/1.00  fof(f10,axiom,(
% 2.97/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f65,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f10])).
% 2.97/1.00  
% 2.97/1.00  fof(f8,axiom,(
% 2.97/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f60,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f8])).
% 2.97/1.00  
% 2.97/1.00  fof(f76,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.97/1.00    inference(definition_unfolding,[],[f65,f60])).
% 2.97/1.00  
% 2.97/1.00  fof(f5,axiom,(
% 2.97/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f57,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f5])).
% 2.97/1.00  
% 2.97/1.00  fof(f83,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 2.97/1.00    inference(definition_unfolding,[],[f59,f76,f57])).
% 2.97/1.00  
% 2.97/1.00  fof(f13,axiom,(
% 2.97/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f21,plain,(
% 2.97/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f13])).
% 2.97/1.00  
% 2.97/1.00  fof(f71,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f21])).
% 2.97/1.00  
% 2.97/1.00  fof(f84,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/1.00    inference(definition_unfolding,[],[f71,f57])).
% 2.97/1.00  
% 2.97/1.00  fof(f3,axiom,(
% 2.97/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f18,plain,(
% 2.97/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f3])).
% 2.97/1.00  
% 2.97/1.00  fof(f29,plain,(
% 2.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/1.00    inference(nnf_transformation,[],[f18])).
% 2.97/1.00  
% 2.97/1.00  fof(f30,plain,(
% 2.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/1.00    inference(rectify,[],[f29])).
% 2.97/1.00  
% 2.97/1.00  fof(f31,plain,(
% 2.97/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f32,plain,(
% 2.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 2.97/1.00  
% 2.97/1.00  fof(f49,plain,(
% 2.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f32])).
% 2.97/1.00  
% 2.97/1.00  fof(f4,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f33,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.97/1.00    inference(nnf_transformation,[],[f4])).
% 2.97/1.00  
% 2.97/1.00  fof(f34,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.97/1.00    inference(flattening,[],[f33])).
% 2.97/1.00  
% 2.97/1.00  fof(f35,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.97/1.00    inference(rectify,[],[f34])).
% 2.97/1.00  
% 2.97/1.00  fof(f36,plain,(
% 2.97/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f37,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 2.97/1.00  
% 2.97/1.00  fof(f51,plain,(
% 2.97/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.97/1.00    inference(cnf_transformation,[],[f37])).
% 2.97/1.00  
% 2.97/1.00  fof(f82,plain,(
% 2.97/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.97/1.00    inference(definition_unfolding,[],[f51,f57])).
% 2.97/1.00  
% 2.97/1.00  fof(f88,plain,(
% 2.97/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.97/1.00    inference(equality_resolution,[],[f82])).
% 2.97/1.00  
% 2.97/1.00  fof(f50,plain,(
% 2.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f32])).
% 2.97/1.00  
% 2.97/1.00  fof(f62,plain,(
% 2.97/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.97/1.00    inference(cnf_transformation,[],[f41])).
% 2.97/1.00  
% 2.97/1.00  fof(f89,plain,(
% 2.97/1.00    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.97/1.00    inference(equality_resolution,[],[f62])).
% 2.97/1.00  
% 2.97/1.00  fof(f67,plain,(
% 2.97/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f42])).
% 2.97/1.00  
% 2.97/1.00  fof(f2,axiom,(
% 2.97/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f25,plain,(
% 2.97/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.97/1.00    inference(nnf_transformation,[],[f2])).
% 2.97/1.00  
% 2.97/1.00  fof(f26,plain,(
% 2.97/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.97/1.00    inference(rectify,[],[f25])).
% 2.97/1.00  
% 2.97/1.00  fof(f27,plain,(
% 2.97/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f28,plain,(
% 2.97/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.97/1.00  
% 2.97/1.00  fof(f46,plain,(
% 2.97/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  fof(f15,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f22,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.97/1.00    inference(ennf_transformation,[],[f15])).
% 2.97/1.00  
% 2.97/1.00  fof(f23,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/1.00    inference(flattening,[],[f22])).
% 2.97/1.00  
% 2.97/1.00  fof(f73,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f23])).
% 2.97/1.00  
% 2.97/1.00  fof(f85,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/1.00    inference(definition_unfolding,[],[f73,f76])).
% 2.97/1.00  
% 2.97/1.00  fof(f75,plain,(
% 2.97/1.00    k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5))),
% 2.97/1.00    inference(cnf_transformation,[],[f44])).
% 2.97/1.00  
% 2.97/1.00  fof(f12,axiom,(
% 2.97/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f70,plain,(
% 2.97/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.97/1.00    inference(cnf_transformation,[],[f12])).
% 2.97/1.00  
% 2.97/1.00  cnf(c_27,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1141,plain,
% 2.97/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_21,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1145,plain,
% 2.97/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.97/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.97/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2262,plain,
% 2.97/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top
% 2.97/1.00      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1141,c_1145]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_24,plain,
% 2.97/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_32,plain,
% 2.97/1.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_34,plain,
% 2.97/1.00      ( v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2820,plain,
% 2.97/1.00      ( r2_hidden(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_2262,c_34]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_17,plain,
% 2.97/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1148,plain,
% 2.97/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.97/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2827,plain,
% 2.97/1.00      ( r1_tarski(sK5,sK4) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2820,c_1148]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_12,plain,
% 2.97/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1152,plain,
% 2.97/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3032,plain,
% 2.97/1.00      ( k3_xboole_0(sK5,sK4) = sK5 ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2827,c_1152]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_0,plain,
% 2.97/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_13,plain,
% 2.97/1.00      ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1449,plain,
% 2.97/1.00      ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1 ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_0,c_13]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3209,plain,
% 2.97/1.00      ( k3_tarski(k1_enumset1(sK5,sK5,k5_xboole_0(sK4,sK5))) = sK4 ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3032,c_1449]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3215,plain,
% 2.97/1.00      ( k3_xboole_0(sK4,sK5) = sK5 ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3032,c_0]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_23,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1144,plain,
% 2.97/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.97/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2589,plain,
% 2.97/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK5)) = k3_subset_1(sK4,sK5) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1141,c_1144]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3892,plain,
% 2.97/1.00      ( k3_subset_1(sK4,sK5) = k5_xboole_0(sK4,sK5) ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_3215,c_2589]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4,plain,
% 2.97/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1160,plain,
% 2.97/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.97/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_11,plain,
% 2.97/1.00      ( r2_hidden(X0,X1)
% 2.97/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 2.97/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1153,plain,
% 2.97/1.01      ( r2_hidden(X0,X1) = iProver_top
% 2.97/1.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2809,plain,
% 2.97/1.01      ( r2_hidden(X0,k3_subset_1(sK4,sK5)) != iProver_top
% 2.97/1.01      | r2_hidden(X0,sK4) = iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2589,c_1153]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3193,plain,
% 2.97/1.01      ( r1_tarski(k3_subset_1(sK4,sK5),X0) = iProver_top
% 2.97/1.01      | r2_hidden(sK1(k3_subset_1(sK4,sK5),X0),sK4) = iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_1160,c_2809]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4359,plain,
% 2.97/1.01      ( r1_tarski(k5_xboole_0(sK4,sK5),X0) = iProver_top
% 2.97/1.01      | r2_hidden(sK1(k5_xboole_0(sK4,sK5),X0),sK4) = iProver_top ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_3892,c_3193]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3,plain,
% 2.97/1.01      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1161,plain,
% 2.97/1.01      ( r1_tarski(X0,X1) = iProver_top
% 2.97/1.01      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4921,plain,
% 2.97/1.01      ( r1_tarski(k5_xboole_0(sK4,sK5),sK4) = iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_4359,c_1161]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_16,plain,
% 2.97/1.01      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1149,plain,
% 2.97/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.97/1.01      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_20,plain,
% 2.97/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2,plain,
% 2.97/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_145,plain,
% 2.97/1.01      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_20,c_2]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_146,plain,
% 2.97/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.97/1.01      inference(renaming,[status(thm)],[c_145]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1140,plain,
% 2.97/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.97/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_146]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1547,plain,
% 2.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.97/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_1149,c_1140]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_25,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.97/1.01      | k3_tarski(k1_enumset1(X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 2.97/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1142,plain,
% 2.97/1.01      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 2.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 2.97/1.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1444,plain,
% 2.97/1.01      ( k3_tarski(k1_enumset1(sK5,sK5,X0)) = k4_subset_1(sK4,sK5,X0)
% 2.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_1141,c_1142]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1702,plain,
% 2.97/1.01      ( k3_tarski(k1_enumset1(sK5,sK5,X0)) = k4_subset_1(sK4,sK5,X0)
% 2.97/1.01      | r1_tarski(X0,sK4) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_1547,c_1444]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4944,plain,
% 2.97/1.01      ( k3_tarski(k1_enumset1(sK5,sK5,k5_xboole_0(sK4,sK5))) = k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_4921,c_1702]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5219,plain,
% 2.97/1.01      ( k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) = sK4 ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_3209,c_4944]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_26,negated_conjecture,
% 2.97/1.01      ( k2_subset_1(sK4) != k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_22,plain,
% 2.97/1.01      ( k2_subset_1(X0) = X0 ),
% 2.97/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1172,plain,
% 2.97/1.01      ( k4_subset_1(sK4,sK5,k3_subset_1(sK4,sK5)) != sK4 ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_26,c_22]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4362,plain,
% 2.97/1.01      ( k4_subset_1(sK4,sK5,k5_xboole_0(sK4,sK5)) != sK4 ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_3892,c_1172]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(contradiction,plain,
% 2.97/1.01      ( $false ),
% 2.97/1.01      inference(minisat,[status(thm)],[c_5219,c_4362]) ).
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  ------                               Statistics
% 2.97/1.01  
% 2.97/1.01  ------ General
% 2.97/1.01  
% 2.97/1.01  abstr_ref_over_cycles:                  0
% 2.97/1.01  abstr_ref_under_cycles:                 0
% 2.97/1.01  gc_basic_clause_elim:                   0
% 2.97/1.01  forced_gc_time:                         0
% 2.97/1.01  parsing_time:                           0.017
% 2.97/1.01  unif_index_cands_time:                  0.
% 2.97/1.01  unif_index_add_time:                    0.
% 2.97/1.01  orderings_time:                         0.
% 2.97/1.01  out_proof_time:                         0.011
% 2.97/1.01  total_time:                             0.255
% 2.97/1.01  num_of_symbols:                         49
% 2.97/1.01  num_of_terms:                           7399
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing
% 2.97/1.01  
% 2.97/1.01  num_of_splits:                          0
% 2.97/1.01  num_of_split_atoms:                     0
% 2.97/1.01  num_of_reused_defs:                     0
% 2.97/1.01  num_eq_ax_congr_red:                    24
% 2.97/1.01  num_of_sem_filtered_clauses:            1
% 2.97/1.01  num_of_subtypes:                        0
% 2.97/1.01  monotx_restored_types:                  0
% 2.97/1.01  sat_num_of_epr_types:                   0
% 2.97/1.01  sat_num_of_non_cyclic_types:            0
% 2.97/1.01  sat_guarded_non_collapsed_types:        0
% 2.97/1.01  num_pure_diseq_elim:                    0
% 2.97/1.01  simp_replaced_by:                       0
% 2.97/1.01  res_preprocessed:                       111
% 2.97/1.01  prep_upred:                             0
% 2.97/1.01  prep_unflattend:                        12
% 2.97/1.01  smt_new_axioms:                         0
% 2.97/1.01  pred_elim_cands:                        4
% 2.97/1.01  pred_elim:                              0
% 2.97/1.01  pred_elim_cl:                           0
% 2.97/1.01  pred_elim_cycles:                       1
% 2.97/1.01  merged_defs:                            6
% 2.97/1.01  merged_defs_ncl:                        0
% 2.97/1.01  bin_hyper_res:                          6
% 2.97/1.01  prep_cycles:                            3
% 2.97/1.01  pred_elim_time:                         0.003
% 2.97/1.01  splitting_time:                         0.
% 2.97/1.01  sem_filter_time:                        0.
% 2.97/1.01  monotx_time:                            0.
% 2.97/1.01  subtype_inf_time:                       0.
% 2.97/1.01  
% 2.97/1.01  ------ Problem properties
% 2.97/1.01  
% 2.97/1.01  clauses:                                28
% 2.97/1.01  conjectures:                            2
% 2.97/1.01  epr:                                    6
% 2.97/1.01  horn:                                   20
% 2.97/1.01  ground:                                 2
% 2.97/1.01  unary:                                  6
% 2.97/1.01  binary:                                 11
% 2.97/1.01  lits:                                   62
% 2.97/1.01  lits_eq:                                12
% 2.97/1.01  fd_pure:                                0
% 2.97/1.01  fd_pseudo:                              0
% 2.97/1.01  fd_cond:                                0
% 2.97/1.01  fd_pseudo_cond:                         5
% 2.97/1.01  ac_symbols:                             0
% 2.97/1.01  
% 2.97/1.01  ------ Propositional Solver
% 2.97/1.01  
% 2.97/1.01  prop_solver_calls:                      23
% 2.97/1.01  prop_fast_solver_calls:                 642
% 2.97/1.01  smt_solver_calls:                       0
% 2.97/1.01  smt_fast_solver_calls:                  0
% 2.97/1.01  prop_num_of_clauses:                    2415
% 2.97/1.01  prop_preprocess_simplified:             6556
% 2.97/1.01  prop_fo_subsumed:                       2
% 2.97/1.01  prop_solver_time:                       0.
% 2.97/1.01  smt_solver_time:                        0.
% 2.97/1.01  smt_fast_solver_time:                   0.
% 2.97/1.01  prop_fast_solver_time:                  0.
% 2.97/1.01  prop_unsat_core_time:                   0.
% 2.97/1.01  
% 2.97/1.01  ------ QBF
% 2.97/1.01  
% 2.97/1.01  qbf_q_res:                              0
% 2.97/1.01  qbf_num_tautologies:                    0
% 2.97/1.01  qbf_prep_cycles:                        0
% 2.97/1.01  
% 2.97/1.01  ------ BMC1
% 2.97/1.01  
% 2.97/1.01  bmc1_current_bound:                     -1
% 2.97/1.01  bmc1_last_solved_bound:                 -1
% 2.97/1.01  bmc1_unsat_core_size:                   -1
% 2.97/1.01  bmc1_unsat_core_parents_size:           -1
% 2.97/1.01  bmc1_merge_next_fun:                    0
% 2.97/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.01  
% 2.97/1.01  ------ Instantiation
% 2.97/1.01  
% 2.97/1.01  inst_num_of_clauses:                    707
% 2.97/1.01  inst_num_in_passive:                    170
% 2.97/1.01  inst_num_in_active:                     206
% 2.97/1.01  inst_num_in_unprocessed:                331
% 2.97/1.01  inst_num_of_loops:                      230
% 2.97/1.01  inst_num_of_learning_restarts:          0
% 2.97/1.01  inst_num_moves_active_passive:          22
% 2.97/1.01  inst_lit_activity:                      0
% 2.97/1.01  inst_lit_activity_moves:                0
% 2.97/1.01  inst_num_tautologies:                   0
% 2.97/1.01  inst_num_prop_implied:                  0
% 2.97/1.01  inst_num_existing_simplified:           0
% 2.97/1.01  inst_num_eq_res_simplified:             0
% 2.97/1.01  inst_num_child_elim:                    0
% 2.97/1.01  inst_num_of_dismatching_blockings:      132
% 2.97/1.01  inst_num_of_non_proper_insts:           398
% 2.97/1.01  inst_num_of_duplicates:                 0
% 2.97/1.01  inst_inst_num_from_inst_to_res:         0
% 2.97/1.01  inst_dismatching_checking_time:         0.
% 2.97/1.01  
% 2.97/1.01  ------ Resolution
% 2.97/1.01  
% 2.97/1.01  res_num_of_clauses:                     0
% 2.97/1.01  res_num_in_passive:                     0
% 2.97/1.01  res_num_in_active:                      0
% 2.97/1.01  res_num_of_loops:                       114
% 2.97/1.01  res_forward_subset_subsumed:            40
% 2.97/1.01  res_backward_subset_subsumed:           0
% 2.97/1.01  res_forward_subsumed:                   0
% 2.97/1.01  res_backward_subsumed:                  0
% 2.97/1.01  res_forward_subsumption_resolution:     0
% 2.97/1.01  res_backward_subsumption_resolution:    0
% 2.97/1.01  res_clause_to_clause_subsumption:       158
% 2.97/1.01  res_orphan_elimination:                 0
% 2.97/1.01  res_tautology_del:                      47
% 2.97/1.01  res_num_eq_res_simplified:              0
% 2.97/1.01  res_num_sel_changes:                    0
% 2.97/1.01  res_moves_from_active_to_pass:          0
% 2.97/1.01  
% 2.97/1.01  ------ Superposition
% 2.97/1.01  
% 2.97/1.01  sup_time_total:                         0.
% 2.97/1.01  sup_time_generating:                    0.
% 2.97/1.01  sup_time_sim_full:                      0.
% 2.97/1.01  sup_time_sim_immed:                     0.
% 2.97/1.01  
% 2.97/1.01  sup_num_of_clauses:                     77
% 2.97/1.01  sup_num_in_active:                      38
% 2.97/1.01  sup_num_in_passive:                     39
% 2.97/1.01  sup_num_of_loops:                       45
% 2.97/1.01  sup_fw_superposition:                   45
% 2.97/1.01  sup_bw_superposition:                   54
% 2.97/1.01  sup_immediate_simplified:               9
% 2.97/1.01  sup_given_eliminated:                   0
% 2.97/1.01  comparisons_done:                       0
% 2.97/1.01  comparisons_avoided:                    0
% 2.97/1.01  
% 2.97/1.01  ------ Simplifications
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  sim_fw_subset_subsumed:                 2
% 2.97/1.01  sim_bw_subset_subsumed:                 0
% 2.97/1.01  sim_fw_subsumed:                        6
% 2.97/1.01  sim_bw_subsumed:                        0
% 2.97/1.01  sim_fw_subsumption_res:                 0
% 2.97/1.01  sim_bw_subsumption_res:                 0
% 2.97/1.01  sim_tautology_del:                      4
% 2.97/1.01  sim_eq_tautology_del:                   0
% 2.97/1.01  sim_eq_res_simp:                        0
% 2.97/1.01  sim_fw_demodulated:                     1
% 2.97/1.01  sim_bw_demodulated:                     7
% 2.97/1.01  sim_light_normalised:                   2
% 2.97/1.01  sim_joinable_taut:                      0
% 2.97/1.01  sim_joinable_simp:                      0
% 2.97/1.01  sim_ac_normalised:                      0
% 2.97/1.01  sim_smt_subsumption:                    0
% 2.97/1.01  
%------------------------------------------------------------------------------
