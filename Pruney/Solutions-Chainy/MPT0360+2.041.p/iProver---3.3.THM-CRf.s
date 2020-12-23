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
% DateTime   : Thu Dec  3 11:40:20 EST 2020

% Result     : Theorem 19.43s
% Output     : CNFRefutation 19.43s
% Verified   : 
% Statistics : Number of formulae       :  179 (10214 expanded)
%              Number of clauses        :  108 (3487 expanded)
%              Number of leaves         :   19 (2192 expanded)
%              Depth                    :   23
%              Number of atoms          :  482 (32658 expanded)
%              Number of equality atoms :  199 (9383 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f47,f43,f43])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK3
      & r1_tarski(sK3,k3_subset_1(sK2,sK4))
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_xboole_0 != sK3
    & r1_tarski(sK3,k3_subset_1(sK2,sK4))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f35])).

fof(f63,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

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
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(nnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    r1_tarski(sK3,k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f65,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_858,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1083,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_1194,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1083,c_9])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_856,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2732,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1083,c_856])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_855,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2236,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_855])).

cnf(c_9921,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2732,c_2236])).

cnf(c_9927,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_9921])).

cnf(c_9989,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_9927])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_837,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_847,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_843,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1976,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_843])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_839,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8307,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1976,c_839])).

cnf(c_28422,plain,
    ( k3_subset_1(sK4,k3_subset_1(sK4,sK3)) = sK3
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_837,c_8307])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_294,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_311,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_1051,plain,
    ( ~ r1_tarski(sK3,sK4)
    | r2_hidden(sK3,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1052,plain,
    ( r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(sK3,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k3_subset_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1175,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK3,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1176,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top
    | r2_hidden(sK3,k1_zfmisc_1(sK4)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1246,plain,
    ( r1_xboole_0(sK3,sK4)
    | k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) != sK3 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1247,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) != sK3
    | r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(c_1392,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK4))
    | k3_subset_1(sK4,k3_subset_1(sK4,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1396,plain,
    ( k3_subset_1(sK4,k3_subset_1(sK4,sK3)) = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1422,plain,
    ( ~ r1_xboole_0(sK3,sK4)
    | k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1547,plain,
    ( ~ r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK3) ),
    inference(resolution,[status(thm)],[c_10,c_26])).

cnf(c_1548,plain,
    ( r1_xboole_0(sK3,sK4) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1547])).

cnf(c_299,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1138,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,k3_subset_1(sK2,sK4))
    | X1 != k3_subset_1(sK2,sK4)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_1271,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(sK3,k3_subset_1(sK2,sK4))
    | X0 != sK3
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k3_subset_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_2076,plain,
    ( r1_tarski(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)))
    | ~ r1_tarski(sK3,k3_subset_1(sK2,sK4))
    | X0 != sK3
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) != k3_subset_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_2078,plain,
    ( ~ r1_tarski(sK3,k3_subset_1(sK2,sK4))
    | r1_tarski(sK3,k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)))
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) != k3_subset_1(sK2,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2142,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)))
    | r1_xboole_0(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2144,plain,
    ( ~ r1_tarski(sK3,k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)))
    | r1_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2142])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3809,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1726])).

cnf(c_3810,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3809])).

cnf(c_3812,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3810])).

cnf(c_28913,plain,
    ( k3_subset_1(sK4,k3_subset_1(sK4,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28422,c_27,c_29,c_25,c_311,c_1052,c_1107,c_1176,c_1247,c_1396,c_1422,c_1548,c_2078,c_2144,c_3812])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_840,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28918,plain,
    ( m1_subset_1(k3_subset_1(sK4,sK3),k1_zfmisc_1(sK4)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28913,c_840])).

cnf(c_28932,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28918,c_27,c_29,c_25,c_311,c_1052,c_1107,c_1176,c_1247,c_1422,c_1548,c_2078,c_2144,c_3812])).

cnf(c_841,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_28940,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK3)) = k3_subset_1(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_28932,c_841])).

cnf(c_1084,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_1882,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1084,c_0])).

cnf(c_29155,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3)))) = k3_xboole_0(sK4,k3_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_28940,c_1882])).

cnf(c_32280,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,sK3))))) = k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3)))) ),
    inference(superposition,[status(thm)],[c_29155,c_1882])).

cnf(c_2518,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,X1))) = k3_subset_1(X0,k3_subset_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_841])).

cnf(c_52768,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3))) = k3_subset_1(sK4,k3_subset_1(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_28932,c_2518])).

cnf(c_29157,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3))) = k3_xboole_0(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_28940,c_0])).

cnf(c_52786,plain,
    ( k3_xboole_0(sK4,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_52768,c_28913,c_29157])).

cnf(c_72572,plain,
    ( k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3)))) = k5_xboole_0(sK4,sK3) ),
    inference(light_normalisation,[status(thm)],[c_32280,c_52786])).

cnf(c_72635,plain,
    ( r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(sK4,sK3))) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_72572,c_855])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_857,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_52934,plain,
    ( r2_hidden(X0,k5_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_52786,c_857])).

cnf(c_52937,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_52786,c_2236])).

cnf(c_838,plain,
    ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_836,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2519,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k3_subset_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_836,c_841])).

cnf(c_854,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5493,plain,
    ( r1_tarski(X0,k3_subset_1(sK2,sK4)) != iProver_top
    | r1_xboole_0(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2519,c_854])).

cnf(c_8158,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_838,c_5493])).

cnf(c_850,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8298,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_8158,c_850])).

cnf(c_8612,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK3)) = k3_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_8298,c_0])).

cnf(c_8638,plain,
    ( k3_xboole_0(sK3,sK4) = k3_xboole_0(sK3,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8612,c_1083])).

cnf(c_8662,plain,
    ( r2_hidden(X0,k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8638,c_856])).

cnf(c_8665,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8662,c_9])).

cnf(c_54534,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52937,c_8665])).

cnf(c_2729,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_856])).

cnf(c_72632,plain,
    ( r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(sK4,sK3))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_72572,c_2729])).

cnf(c_72693,plain,
    ( r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(sK4,sK3))) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK4,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72632,c_72572])).

cnf(c_73452,plain,
    ( r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(sK4,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72635,c_8665,c_52934,c_52937,c_72693])).

cnf(c_73475,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,sK3)),k3_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,sK3)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9989,c_73452])).

cnf(c_54542,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK3
    | r2_hidden(sK0(X0,X1,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_54534])).

cnf(c_73487,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,sK3)),k3_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,sK3)),X0)) = sK3 ),
    inference(superposition,[status(thm)],[c_54542,c_73452])).

cnf(c_73535,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_73475,c_73487])).

cnf(c_1269,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_295,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1106,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_1268,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73535,c_1269,c_1268,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:32:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.43/3.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.43/3.01  
% 19.43/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.43/3.01  
% 19.43/3.01  ------  iProver source info
% 19.43/3.01  
% 19.43/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.43/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.43/3.01  git: non_committed_changes: false
% 19.43/3.01  git: last_make_outside_of_git: false
% 19.43/3.01  
% 19.43/3.01  ------ 
% 19.43/3.01  
% 19.43/3.01  ------ Input Options
% 19.43/3.01  
% 19.43/3.01  --out_options                           all
% 19.43/3.01  --tptp_safe_out                         true
% 19.43/3.01  --problem_path                          ""
% 19.43/3.01  --include_path                          ""
% 19.43/3.01  --clausifier                            res/vclausify_rel
% 19.43/3.01  --clausifier_options                    --mode clausify
% 19.43/3.01  --stdin                                 false
% 19.43/3.01  --stats_out                             sel
% 19.43/3.01  
% 19.43/3.01  ------ General Options
% 19.43/3.01  
% 19.43/3.01  --fof                                   false
% 19.43/3.01  --time_out_real                         604.99
% 19.43/3.01  --time_out_virtual                      -1.
% 19.43/3.01  --symbol_type_check                     false
% 19.43/3.01  --clausify_out                          false
% 19.43/3.01  --sig_cnt_out                           false
% 19.43/3.01  --trig_cnt_out                          false
% 19.43/3.01  --trig_cnt_out_tolerance                1.
% 19.43/3.01  --trig_cnt_out_sk_spl                   false
% 19.43/3.01  --abstr_cl_out                          false
% 19.43/3.01  
% 19.43/3.01  ------ Global Options
% 19.43/3.01  
% 19.43/3.01  --schedule                              none
% 19.43/3.01  --add_important_lit                     false
% 19.43/3.01  --prop_solver_per_cl                    1000
% 19.43/3.01  --min_unsat_core                        false
% 19.43/3.01  --soft_assumptions                      false
% 19.43/3.01  --soft_lemma_size                       3
% 19.43/3.01  --prop_impl_unit_size                   0
% 19.43/3.01  --prop_impl_unit                        []
% 19.43/3.01  --share_sel_clauses                     true
% 19.43/3.01  --reset_solvers                         false
% 19.43/3.01  --bc_imp_inh                            [conj_cone]
% 19.43/3.01  --conj_cone_tolerance                   3.
% 19.43/3.01  --extra_neg_conj                        none
% 19.43/3.01  --large_theory_mode                     true
% 19.43/3.01  --prolific_symb_bound                   200
% 19.43/3.01  --lt_threshold                          2000
% 19.43/3.01  --clause_weak_htbl                      true
% 19.43/3.01  --gc_record_bc_elim                     false
% 19.43/3.01  
% 19.43/3.01  ------ Preprocessing Options
% 19.43/3.01  
% 19.43/3.01  --preprocessing_flag                    true
% 19.43/3.01  --time_out_prep_mult                    0.1
% 19.43/3.01  --splitting_mode                        input
% 19.43/3.01  --splitting_grd                         true
% 19.43/3.01  --splitting_cvd                         false
% 19.43/3.01  --splitting_cvd_svl                     false
% 19.43/3.01  --splitting_nvd                         32
% 19.43/3.01  --sub_typing                            true
% 19.43/3.01  --prep_gs_sim                           false
% 19.43/3.01  --prep_unflatten                        true
% 19.43/3.01  --prep_res_sim                          true
% 19.43/3.01  --prep_upred                            true
% 19.43/3.01  --prep_sem_filter                       exhaustive
% 19.43/3.01  --prep_sem_filter_out                   false
% 19.43/3.01  --pred_elim                             false
% 19.43/3.01  --res_sim_input                         true
% 19.43/3.01  --eq_ax_congr_red                       true
% 19.43/3.01  --pure_diseq_elim                       true
% 19.43/3.01  --brand_transform                       false
% 19.43/3.01  --non_eq_to_eq                          false
% 19.43/3.01  --prep_def_merge                        true
% 19.43/3.01  --prep_def_merge_prop_impl              false
% 19.43/3.01  --prep_def_merge_mbd                    true
% 19.43/3.01  --prep_def_merge_tr_red                 false
% 19.43/3.01  --prep_def_merge_tr_cl                  false
% 19.43/3.01  --smt_preprocessing                     true
% 19.43/3.01  --smt_ac_axioms                         fast
% 19.43/3.01  --preprocessed_out                      false
% 19.43/3.01  --preprocessed_stats                    false
% 19.43/3.01  
% 19.43/3.01  ------ Abstraction refinement Options
% 19.43/3.01  
% 19.43/3.01  --abstr_ref                             []
% 19.43/3.01  --abstr_ref_prep                        false
% 19.43/3.01  --abstr_ref_until_sat                   false
% 19.43/3.01  --abstr_ref_sig_restrict                funpre
% 19.43/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.43/3.01  --abstr_ref_under                       []
% 19.43/3.01  
% 19.43/3.01  ------ SAT Options
% 19.43/3.01  
% 19.43/3.01  --sat_mode                              false
% 19.43/3.01  --sat_fm_restart_options                ""
% 19.43/3.01  --sat_gr_def                            false
% 19.43/3.01  --sat_epr_types                         true
% 19.43/3.01  --sat_non_cyclic_types                  false
% 19.43/3.01  --sat_finite_models                     false
% 19.43/3.01  --sat_fm_lemmas                         false
% 19.43/3.01  --sat_fm_prep                           false
% 19.43/3.01  --sat_fm_uc_incr                        true
% 19.43/3.01  --sat_out_model                         small
% 19.43/3.01  --sat_out_clauses                       false
% 19.43/3.01  
% 19.43/3.01  ------ QBF Options
% 19.43/3.01  
% 19.43/3.01  --qbf_mode                              false
% 19.43/3.01  --qbf_elim_univ                         false
% 19.43/3.01  --qbf_dom_inst                          none
% 19.43/3.01  --qbf_dom_pre_inst                      false
% 19.43/3.01  --qbf_sk_in                             false
% 19.43/3.01  --qbf_pred_elim                         true
% 19.43/3.01  --qbf_split                             512
% 19.43/3.01  
% 19.43/3.01  ------ BMC1 Options
% 19.43/3.01  
% 19.43/3.01  --bmc1_incremental                      false
% 19.43/3.01  --bmc1_axioms                           reachable_all
% 19.43/3.01  --bmc1_min_bound                        0
% 19.43/3.01  --bmc1_max_bound                        -1
% 19.43/3.01  --bmc1_max_bound_default                -1
% 19.43/3.01  --bmc1_symbol_reachability              true
% 19.43/3.01  --bmc1_property_lemmas                  false
% 19.43/3.01  --bmc1_k_induction                      false
% 19.43/3.01  --bmc1_non_equiv_states                 false
% 19.43/3.01  --bmc1_deadlock                         false
% 19.43/3.01  --bmc1_ucm                              false
% 19.43/3.01  --bmc1_add_unsat_core                   none
% 19.43/3.01  --bmc1_unsat_core_children              false
% 19.43/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.43/3.01  --bmc1_out_stat                         full
% 19.43/3.01  --bmc1_ground_init                      false
% 19.43/3.01  --bmc1_pre_inst_next_state              false
% 19.43/3.01  --bmc1_pre_inst_state                   false
% 19.43/3.01  --bmc1_pre_inst_reach_state             false
% 19.43/3.01  --bmc1_out_unsat_core                   false
% 19.43/3.01  --bmc1_aig_witness_out                  false
% 19.43/3.01  --bmc1_verbose                          false
% 19.43/3.01  --bmc1_dump_clauses_tptp                false
% 19.43/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.43/3.01  --bmc1_dump_file                        -
% 19.43/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.43/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.43/3.01  --bmc1_ucm_extend_mode                  1
% 19.43/3.01  --bmc1_ucm_init_mode                    2
% 19.43/3.01  --bmc1_ucm_cone_mode                    none
% 19.43/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.43/3.01  --bmc1_ucm_relax_model                  4
% 19.43/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.43/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.43/3.01  --bmc1_ucm_layered_model                none
% 19.43/3.01  --bmc1_ucm_max_lemma_size               10
% 19.43/3.01  
% 19.43/3.01  ------ AIG Options
% 19.43/3.01  
% 19.43/3.01  --aig_mode                              false
% 19.43/3.01  
% 19.43/3.01  ------ Instantiation Options
% 19.43/3.01  
% 19.43/3.01  --instantiation_flag                    true
% 19.43/3.01  --inst_sos_flag                         false
% 19.43/3.01  --inst_sos_phase                        true
% 19.43/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.43/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.43/3.01  --inst_lit_sel_side                     num_symb
% 19.43/3.01  --inst_solver_per_active                1400
% 19.43/3.01  --inst_solver_calls_frac                1.
% 19.43/3.01  --inst_passive_queue_type               priority_queues
% 19.43/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.43/3.01  --inst_passive_queues_freq              [25;2]
% 19.43/3.01  --inst_dismatching                      true
% 19.43/3.01  --inst_eager_unprocessed_to_passive     true
% 19.43/3.01  --inst_prop_sim_given                   true
% 19.43/3.01  --inst_prop_sim_new                     false
% 19.43/3.01  --inst_subs_new                         false
% 19.43/3.01  --inst_eq_res_simp                      false
% 19.43/3.01  --inst_subs_given                       false
% 19.43/3.01  --inst_orphan_elimination               true
% 19.43/3.01  --inst_learning_loop_flag               true
% 19.43/3.01  --inst_learning_start                   3000
% 19.43/3.01  --inst_learning_factor                  2
% 19.43/3.01  --inst_start_prop_sim_after_learn       3
% 19.43/3.01  --inst_sel_renew                        solver
% 19.43/3.01  --inst_lit_activity_flag                true
% 19.43/3.01  --inst_restr_to_given                   false
% 19.43/3.01  --inst_activity_threshold               500
% 19.43/3.01  --inst_out_proof                        true
% 19.43/3.01  
% 19.43/3.01  ------ Resolution Options
% 19.43/3.01  
% 19.43/3.01  --resolution_flag                       true
% 19.43/3.01  --res_lit_sel                           adaptive
% 19.43/3.01  --res_lit_sel_side                      none
% 19.43/3.01  --res_ordering                          kbo
% 19.43/3.01  --res_to_prop_solver                    active
% 19.43/3.01  --res_prop_simpl_new                    false
% 19.43/3.01  --res_prop_simpl_given                  true
% 19.43/3.01  --res_passive_queue_type                priority_queues
% 19.43/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.43/3.01  --res_passive_queues_freq               [15;5]
% 19.43/3.01  --res_forward_subs                      full
% 19.43/3.01  --res_backward_subs                     full
% 19.43/3.01  --res_forward_subs_resolution           true
% 19.43/3.01  --res_backward_subs_resolution          true
% 19.43/3.01  --res_orphan_elimination                true
% 19.43/3.01  --res_time_limit                        2.
% 19.43/3.01  --res_out_proof                         true
% 19.43/3.01  
% 19.43/3.01  ------ Superposition Options
% 19.43/3.01  
% 19.43/3.01  --superposition_flag                    true
% 19.43/3.01  --sup_passive_queue_type                priority_queues
% 19.43/3.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.43/3.01  --sup_passive_queues_freq               [1;4]
% 19.43/3.01  --demod_completeness_check              fast
% 19.43/3.01  --demod_use_ground                      true
% 19.43/3.01  --sup_to_prop_solver                    passive
% 19.43/3.01  --sup_prop_simpl_new                    true
% 19.43/3.01  --sup_prop_simpl_given                  true
% 19.43/3.01  --sup_fun_splitting                     false
% 19.43/3.01  --sup_smt_interval                      50000
% 19.43/3.01  
% 19.43/3.01  ------ Superposition Simplification Setup
% 19.43/3.01  
% 19.43/3.01  --sup_indices_passive                   []
% 19.43/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.43/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.43/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.43/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.43/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.43/3.01  --sup_full_bw                           [BwDemod]
% 19.43/3.01  --sup_immed_triv                        [TrivRules]
% 19.43/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.43/3.01  --sup_immed_bw_main                     []
% 19.43/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.43/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.43/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.43/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.43/3.01  
% 19.43/3.01  ------ Combination Options
% 19.43/3.01  
% 19.43/3.01  --comb_res_mult                         3
% 19.43/3.01  --comb_sup_mult                         2
% 19.43/3.01  --comb_inst_mult                        10
% 19.43/3.01  
% 19.43/3.01  ------ Debug Options
% 19.43/3.01  
% 19.43/3.01  --dbg_backtrace                         false
% 19.43/3.01  --dbg_dump_prop_clauses                 false
% 19.43/3.01  --dbg_dump_prop_clauses_file            -
% 19.43/3.01  --dbg_out_stat                          false
% 19.43/3.01  ------ Parsing...
% 19.43/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.43/3.01  
% 19.43/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.43/3.01  
% 19.43/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.43/3.01  
% 19.43/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.43/3.01  ------ Proving...
% 19.43/3.01  ------ Problem Properties 
% 19.43/3.01  
% 19.43/3.01  
% 19.43/3.01  clauses                                 28
% 19.43/3.01  conjectures                             4
% 19.43/3.01  EPR                                     7
% 19.43/3.01  Horn                                    21
% 19.43/3.01  unary                                   6
% 19.43/3.01  binary                                  11
% 19.43/3.01  lits                                    62
% 19.43/3.01  lits eq                                 12
% 19.43/3.01  fd_pure                                 0
% 19.43/3.01  fd_pseudo                               0
% 19.43/3.01  fd_cond                                 0
% 19.43/3.01  fd_pseudo_cond                          5
% 19.43/3.01  AC symbols                              0
% 19.43/3.01  
% 19.43/3.01  ------ Input Options Time Limit: Unbounded
% 19.43/3.01  
% 19.43/3.01  
% 19.43/3.01  ------ 
% 19.43/3.01  Current options:
% 19.43/3.01  ------ 
% 19.43/3.01  
% 19.43/3.01  ------ Input Options
% 19.43/3.01  
% 19.43/3.01  --out_options                           all
% 19.43/3.01  --tptp_safe_out                         true
% 19.43/3.01  --problem_path                          ""
% 19.43/3.01  --include_path                          ""
% 19.43/3.01  --clausifier                            res/vclausify_rel
% 19.43/3.01  --clausifier_options                    --mode clausify
% 19.43/3.01  --stdin                                 false
% 19.43/3.01  --stats_out                             sel
% 19.43/3.01  
% 19.43/3.01  ------ General Options
% 19.43/3.01  
% 19.43/3.01  --fof                                   false
% 19.43/3.01  --time_out_real                         604.99
% 19.43/3.01  --time_out_virtual                      -1.
% 19.43/3.01  --symbol_type_check                     false
% 19.43/3.01  --clausify_out                          false
% 19.43/3.01  --sig_cnt_out                           false
% 19.43/3.01  --trig_cnt_out                          false
% 19.43/3.01  --trig_cnt_out_tolerance                1.
% 19.43/3.01  --trig_cnt_out_sk_spl                   false
% 19.43/3.01  --abstr_cl_out                          false
% 19.43/3.01  
% 19.43/3.01  ------ Global Options
% 19.43/3.01  
% 19.43/3.01  --schedule                              none
% 19.43/3.01  --add_important_lit                     false
% 19.43/3.01  --prop_solver_per_cl                    1000
% 19.43/3.01  --min_unsat_core                        false
% 19.43/3.01  --soft_assumptions                      false
% 19.43/3.01  --soft_lemma_size                       3
% 19.43/3.01  --prop_impl_unit_size                   0
% 19.43/3.01  --prop_impl_unit                        []
% 19.43/3.01  --share_sel_clauses                     true
% 19.43/3.01  --reset_solvers                         false
% 19.43/3.01  --bc_imp_inh                            [conj_cone]
% 19.43/3.01  --conj_cone_tolerance                   3.
% 19.43/3.01  --extra_neg_conj                        none
% 19.43/3.01  --large_theory_mode                     true
% 19.43/3.01  --prolific_symb_bound                   200
% 19.43/3.01  --lt_threshold                          2000
% 19.43/3.01  --clause_weak_htbl                      true
% 19.43/3.01  --gc_record_bc_elim                     false
% 19.43/3.01  
% 19.43/3.01  ------ Preprocessing Options
% 19.43/3.01  
% 19.43/3.01  --preprocessing_flag                    true
% 19.43/3.01  --time_out_prep_mult                    0.1
% 19.43/3.01  --splitting_mode                        input
% 19.43/3.01  --splitting_grd                         true
% 19.43/3.01  --splitting_cvd                         false
% 19.43/3.01  --splitting_cvd_svl                     false
% 19.43/3.01  --splitting_nvd                         32
% 19.43/3.01  --sub_typing                            true
% 19.43/3.01  --prep_gs_sim                           false
% 19.43/3.01  --prep_unflatten                        true
% 19.43/3.01  --prep_res_sim                          true
% 19.43/3.01  --prep_upred                            true
% 19.43/3.01  --prep_sem_filter                       exhaustive
% 19.43/3.01  --prep_sem_filter_out                   false
% 19.43/3.01  --pred_elim                             false
% 19.43/3.01  --res_sim_input                         true
% 19.43/3.01  --eq_ax_congr_red                       true
% 19.43/3.01  --pure_diseq_elim                       true
% 19.43/3.01  --brand_transform                       false
% 19.43/3.01  --non_eq_to_eq                          false
% 19.43/3.01  --prep_def_merge                        true
% 19.43/3.01  --prep_def_merge_prop_impl              false
% 19.43/3.01  --prep_def_merge_mbd                    true
% 19.43/3.01  --prep_def_merge_tr_red                 false
% 19.43/3.01  --prep_def_merge_tr_cl                  false
% 19.43/3.01  --smt_preprocessing                     true
% 19.43/3.01  --smt_ac_axioms                         fast
% 19.43/3.01  --preprocessed_out                      false
% 19.43/3.01  --preprocessed_stats                    false
% 19.43/3.01  
% 19.43/3.01  ------ Abstraction refinement Options
% 19.43/3.01  
% 19.43/3.01  --abstr_ref                             []
% 19.43/3.01  --abstr_ref_prep                        false
% 19.43/3.01  --abstr_ref_until_sat                   false
% 19.43/3.01  --abstr_ref_sig_restrict                funpre
% 19.43/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.43/3.01  --abstr_ref_under                       []
% 19.43/3.01  
% 19.43/3.01  ------ SAT Options
% 19.43/3.01  
% 19.43/3.01  --sat_mode                              false
% 19.43/3.01  --sat_fm_restart_options                ""
% 19.43/3.01  --sat_gr_def                            false
% 19.43/3.01  --sat_epr_types                         true
% 19.43/3.01  --sat_non_cyclic_types                  false
% 19.43/3.01  --sat_finite_models                     false
% 19.43/3.01  --sat_fm_lemmas                         false
% 19.43/3.01  --sat_fm_prep                           false
% 19.43/3.01  --sat_fm_uc_incr                        true
% 19.43/3.01  --sat_out_model                         small
% 19.43/3.01  --sat_out_clauses                       false
% 19.43/3.01  
% 19.43/3.01  ------ QBF Options
% 19.43/3.01  
% 19.43/3.01  --qbf_mode                              false
% 19.43/3.01  --qbf_elim_univ                         false
% 19.43/3.01  --qbf_dom_inst                          none
% 19.43/3.01  --qbf_dom_pre_inst                      false
% 19.43/3.01  --qbf_sk_in                             false
% 19.43/3.01  --qbf_pred_elim                         true
% 19.43/3.01  --qbf_split                             512
% 19.43/3.01  
% 19.43/3.01  ------ BMC1 Options
% 19.43/3.01  
% 19.43/3.01  --bmc1_incremental                      false
% 19.43/3.01  --bmc1_axioms                           reachable_all
% 19.43/3.01  --bmc1_min_bound                        0
% 19.43/3.01  --bmc1_max_bound                        -1
% 19.43/3.01  --bmc1_max_bound_default                -1
% 19.43/3.01  --bmc1_symbol_reachability              true
% 19.43/3.01  --bmc1_property_lemmas                  false
% 19.43/3.01  --bmc1_k_induction                      false
% 19.43/3.01  --bmc1_non_equiv_states                 false
% 19.43/3.01  --bmc1_deadlock                         false
% 19.43/3.01  --bmc1_ucm                              false
% 19.43/3.01  --bmc1_add_unsat_core                   none
% 19.43/3.01  --bmc1_unsat_core_children              false
% 19.43/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.43/3.01  --bmc1_out_stat                         full
% 19.43/3.01  --bmc1_ground_init                      false
% 19.43/3.01  --bmc1_pre_inst_next_state              false
% 19.43/3.01  --bmc1_pre_inst_state                   false
% 19.43/3.01  --bmc1_pre_inst_reach_state             false
% 19.43/3.01  --bmc1_out_unsat_core                   false
% 19.43/3.01  --bmc1_aig_witness_out                  false
% 19.43/3.01  --bmc1_verbose                          false
% 19.43/3.01  --bmc1_dump_clauses_tptp                false
% 19.43/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.43/3.01  --bmc1_dump_file                        -
% 19.43/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.43/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.43/3.01  --bmc1_ucm_extend_mode                  1
% 19.43/3.01  --bmc1_ucm_init_mode                    2
% 19.43/3.01  --bmc1_ucm_cone_mode                    none
% 19.43/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.43/3.01  --bmc1_ucm_relax_model                  4
% 19.43/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.43/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.43/3.01  --bmc1_ucm_layered_model                none
% 19.43/3.01  --bmc1_ucm_max_lemma_size               10
% 19.43/3.01  
% 19.43/3.01  ------ AIG Options
% 19.43/3.01  
% 19.43/3.01  --aig_mode                              false
% 19.43/3.01  
% 19.43/3.01  ------ Instantiation Options
% 19.43/3.01  
% 19.43/3.01  --instantiation_flag                    true
% 19.43/3.01  --inst_sos_flag                         false
% 19.43/3.01  --inst_sos_phase                        true
% 19.43/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.43/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.43/3.01  --inst_lit_sel_side                     num_symb
% 19.43/3.01  --inst_solver_per_active                1400
% 19.43/3.01  --inst_solver_calls_frac                1.
% 19.43/3.01  --inst_passive_queue_type               priority_queues
% 19.43/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.43/3.01  --inst_passive_queues_freq              [25;2]
% 19.43/3.01  --inst_dismatching                      true
% 19.43/3.01  --inst_eager_unprocessed_to_passive     true
% 19.43/3.01  --inst_prop_sim_given                   true
% 19.43/3.01  --inst_prop_sim_new                     false
% 19.43/3.01  --inst_subs_new                         false
% 19.43/3.01  --inst_eq_res_simp                      false
% 19.43/3.01  --inst_subs_given                       false
% 19.43/3.01  --inst_orphan_elimination               true
% 19.43/3.01  --inst_learning_loop_flag               true
% 19.43/3.01  --inst_learning_start                   3000
% 19.43/3.01  --inst_learning_factor                  2
% 19.43/3.01  --inst_start_prop_sim_after_learn       3
% 19.43/3.01  --inst_sel_renew                        solver
% 19.43/3.01  --inst_lit_activity_flag                true
% 19.43/3.01  --inst_restr_to_given                   false
% 19.43/3.01  --inst_activity_threshold               500
% 19.43/3.01  --inst_out_proof                        true
% 19.43/3.01  
% 19.43/3.01  ------ Resolution Options
% 19.43/3.01  
% 19.43/3.01  --resolution_flag                       true
% 19.43/3.01  --res_lit_sel                           adaptive
% 19.43/3.01  --res_lit_sel_side                      none
% 19.43/3.01  --res_ordering                          kbo
% 19.43/3.01  --res_to_prop_solver                    active
% 19.43/3.01  --res_prop_simpl_new                    false
% 19.43/3.01  --res_prop_simpl_given                  true
% 19.43/3.01  --res_passive_queue_type                priority_queues
% 19.43/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.43/3.01  --res_passive_queues_freq               [15;5]
% 19.43/3.01  --res_forward_subs                      full
% 19.43/3.01  --res_backward_subs                     full
% 19.43/3.01  --res_forward_subs_resolution           true
% 19.43/3.01  --res_backward_subs_resolution          true
% 19.43/3.01  --res_orphan_elimination                true
% 19.43/3.01  --res_time_limit                        2.
% 19.43/3.01  --res_out_proof                         true
% 19.43/3.01  
% 19.43/3.01  ------ Superposition Options
% 19.43/3.01  
% 19.43/3.01  --superposition_flag                    true
% 19.43/3.01  --sup_passive_queue_type                priority_queues
% 19.43/3.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.43/3.01  --sup_passive_queues_freq               [1;4]
% 19.43/3.01  --demod_completeness_check              fast
% 19.43/3.01  --demod_use_ground                      true
% 19.43/3.01  --sup_to_prop_solver                    passive
% 19.43/3.01  --sup_prop_simpl_new                    true
% 19.43/3.01  --sup_prop_simpl_given                  true
% 19.43/3.01  --sup_fun_splitting                     false
% 19.43/3.01  --sup_smt_interval                      50000
% 19.43/3.01  
% 19.43/3.01  ------ Superposition Simplification Setup
% 19.43/3.01  
% 19.43/3.01  --sup_indices_passive                   []
% 19.43/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.43/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.43/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.43/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.43/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.43/3.01  --sup_full_bw                           [BwDemod]
% 19.43/3.01  --sup_immed_triv                        [TrivRules]
% 19.43/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.43/3.01  --sup_immed_bw_main                     []
% 19.43/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.43/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.43/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.43/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.43/3.01  
% 19.43/3.01  ------ Combination Options
% 19.43/3.01  
% 19.43/3.01  --comb_res_mult                         3
% 19.43/3.01  --comb_sup_mult                         2
% 19.43/3.01  --comb_inst_mult                        10
% 19.43/3.01  
% 19.43/3.01  ------ Debug Options
% 19.43/3.01  
% 19.43/3.01  --dbg_backtrace                         false
% 19.43/3.01  --dbg_dump_prop_clauses                 false
% 19.43/3.01  --dbg_dump_prop_clauses_file            -
% 19.43/3.01  --dbg_out_stat                          false
% 19.43/3.01  
% 19.43/3.01  
% 19.43/3.01  
% 19.43/3.01  
% 19.43/3.01  ------ Proving...
% 19.43/3.01  
% 19.43/3.01  
% 19.43/3.01  % SZS status Theorem for theBenchmark.p
% 19.43/3.01  
% 19.43/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.43/3.01  
% 19.43/3.01  fof(f1,axiom,(
% 19.43/3.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f24,plain,(
% 19.43/3.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.43/3.01    inference(nnf_transformation,[],[f1])).
% 19.43/3.01  
% 19.43/3.01  fof(f25,plain,(
% 19.43/3.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.43/3.01    inference(flattening,[],[f24])).
% 19.43/3.01  
% 19.43/3.01  fof(f26,plain,(
% 19.43/3.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.43/3.01    inference(rectify,[],[f25])).
% 19.43/3.01  
% 19.43/3.01  fof(f27,plain,(
% 19.43/3.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.43/3.01    introduced(choice_axiom,[])).
% 19.43/3.01  
% 19.43/3.01  fof(f28,plain,(
% 19.43/3.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.43/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 19.43/3.01  
% 19.43/3.01  fof(f40,plain,(
% 19.43/3.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.43/3.01    inference(cnf_transformation,[],[f28])).
% 19.43/3.01  
% 19.43/3.01  fof(f2,axiom,(
% 19.43/3.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f43,plain,(
% 19.43/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.43/3.01    inference(cnf_transformation,[],[f2])).
% 19.43/3.01  
% 19.43/3.01  fof(f69,plain,(
% 19.43/3.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.43/3.01    inference(definition_unfolding,[],[f40,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f4,axiom,(
% 19.43/3.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f46,plain,(
% 19.43/3.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.43/3.01    inference(cnf_transformation,[],[f4])).
% 19.43/3.01  
% 19.43/3.01  fof(f75,plain,(
% 19.43/3.01    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 19.43/3.01    inference(definition_unfolding,[],[f46,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f5,axiom,(
% 19.43/3.01    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f47,plain,(
% 19.43/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.43/3.01    inference(cnf_transformation,[],[f5])).
% 19.43/3.01  
% 19.43/3.01  fof(f66,plain,(
% 19.43/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 19.43/3.01    inference(definition_unfolding,[],[f47,f43,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f38,plain,(
% 19.43/3.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.43/3.01    inference(cnf_transformation,[],[f28])).
% 19.43/3.01  
% 19.43/3.01  fof(f71,plain,(
% 19.43/3.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 19.43/3.01    inference(definition_unfolding,[],[f38,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f80,plain,(
% 19.43/3.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 19.43/3.01    inference(equality_resolution,[],[f71])).
% 19.43/3.01  
% 19.43/3.01  fof(f37,plain,(
% 19.43/3.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.43/3.01    inference(cnf_transformation,[],[f28])).
% 19.43/3.01  
% 19.43/3.01  fof(f72,plain,(
% 19.43/3.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 19.43/3.01    inference(definition_unfolding,[],[f37,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f81,plain,(
% 19.43/3.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 19.43/3.01    inference(equality_resolution,[],[f72])).
% 19.43/3.01  
% 19.43/3.01  fof(f13,conjecture,(
% 19.43/3.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f14,negated_conjecture,(
% 19.43/3.01    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 19.43/3.01    inference(negated_conjecture,[],[f13])).
% 19.43/3.01  
% 19.43/3.01  fof(f22,plain,(
% 19.43/3.01    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.43/3.01    inference(ennf_transformation,[],[f14])).
% 19.43/3.01  
% 19.43/3.01  fof(f23,plain,(
% 19.43/3.01    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.43/3.01    inference(flattening,[],[f22])).
% 19.43/3.01  
% 19.43/3.01  fof(f35,plain,(
% 19.43/3.01    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK3 & r1_tarski(sK3,k3_subset_1(sK2,sK4)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK2)))),
% 19.43/3.01    introduced(choice_axiom,[])).
% 19.43/3.01  
% 19.43/3.01  fof(f36,plain,(
% 19.43/3.01    k1_xboole_0 != sK3 & r1_tarski(sK3,k3_subset_1(sK2,sK4)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 19.43/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f35])).
% 19.43/3.01  
% 19.43/3.01  fof(f63,plain,(
% 19.43/3.01    r1_tarski(sK3,sK4)),
% 19.43/3.01    inference(cnf_transformation,[],[f36])).
% 19.43/3.01  
% 19.43/3.01  fof(f8,axiom,(
% 19.43/3.01    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f30,plain,(
% 19.43/3.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 19.43/3.01    inference(nnf_transformation,[],[f8])).
% 19.43/3.01  
% 19.43/3.01  fof(f31,plain,(
% 19.43/3.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 19.43/3.01    inference(rectify,[],[f30])).
% 19.43/3.01  
% 19.43/3.01  fof(f32,plain,(
% 19.43/3.01    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 19.43/3.01    introduced(choice_axiom,[])).
% 19.43/3.01  
% 19.43/3.01  fof(f33,plain,(
% 19.43/3.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 19.43/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 19.43/3.01  
% 19.43/3.01  fof(f52,plain,(
% 19.43/3.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 19.43/3.01    inference(cnf_transformation,[],[f33])).
% 19.43/3.01  
% 19.43/3.01  fof(f82,plain,(
% 19.43/3.01    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 19.43/3.01    inference(equality_resolution,[],[f52])).
% 19.43/3.01  
% 19.43/3.01  fof(f9,axiom,(
% 19.43/3.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f18,plain,(
% 19.43/3.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 19.43/3.01    inference(ennf_transformation,[],[f9])).
% 19.43/3.01  
% 19.43/3.01  fof(f34,plain,(
% 19.43/3.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 19.43/3.01    inference(nnf_transformation,[],[f18])).
% 19.43/3.01  
% 19.43/3.01  fof(f56,plain,(
% 19.43/3.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 19.43/3.01    inference(cnf_transformation,[],[f34])).
% 19.43/3.01  
% 19.43/3.01  fof(f12,axiom,(
% 19.43/3.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f21,plain,(
% 19.43/3.01    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.43/3.01    inference(ennf_transformation,[],[f12])).
% 19.43/3.01  
% 19.43/3.01  fof(f61,plain,(
% 19.43/3.01    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.43/3.01    inference(cnf_transformation,[],[f21])).
% 19.43/3.01  
% 19.43/3.01  fof(f62,plain,(
% 19.43/3.01    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 19.43/3.01    inference(cnf_transformation,[],[f36])).
% 19.43/3.01  
% 19.43/3.01  fof(f64,plain,(
% 19.43/3.01    r1_tarski(sK3,k3_subset_1(sK2,sK4))),
% 19.43/3.01    inference(cnf_transformation,[],[f36])).
% 19.43/3.01  
% 19.43/3.01  fof(f10,axiom,(
% 19.43/3.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f19,plain,(
% 19.43/3.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.43/3.01    inference(ennf_transformation,[],[f10])).
% 19.43/3.01  
% 19.43/3.01  fof(f59,plain,(
% 19.43/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.43/3.01    inference(cnf_transformation,[],[f19])).
% 19.43/3.01  
% 19.43/3.01  fof(f78,plain,(
% 19.43/3.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.43/3.01    inference(definition_unfolding,[],[f59,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f7,axiom,(
% 19.43/3.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f29,plain,(
% 19.43/3.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 19.43/3.01    inference(nnf_transformation,[],[f7])).
% 19.43/3.01  
% 19.43/3.01  fof(f50,plain,(
% 19.43/3.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 19.43/3.01    inference(cnf_transformation,[],[f29])).
% 19.43/3.01  
% 19.43/3.01  fof(f76,plain,(
% 19.43/3.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 19.43/3.01    inference(definition_unfolding,[],[f50,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f49,plain,(
% 19.43/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 19.43/3.01    inference(cnf_transformation,[],[f29])).
% 19.43/3.01  
% 19.43/3.01  fof(f77,plain,(
% 19.43/3.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 19.43/3.01    inference(definition_unfolding,[],[f49,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f6,axiom,(
% 19.43/3.01    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f16,plain,(
% 19.43/3.01    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 19.43/3.01    inference(ennf_transformation,[],[f6])).
% 19.43/3.01  
% 19.43/3.01  fof(f17,plain,(
% 19.43/3.01    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 19.43/3.01    inference(flattening,[],[f16])).
% 19.43/3.01  
% 19.43/3.01  fof(f48,plain,(
% 19.43/3.01    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 19.43/3.01    inference(cnf_transformation,[],[f17])).
% 19.43/3.01  
% 19.43/3.01  fof(f3,axiom,(
% 19.43/3.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f15,plain,(
% 19.43/3.01    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 19.43/3.01    inference(ennf_transformation,[],[f3])).
% 19.43/3.01  
% 19.43/3.01  fof(f45,plain,(
% 19.43/3.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 19.43/3.01    inference(cnf_transformation,[],[f15])).
% 19.43/3.01  
% 19.43/3.01  fof(f73,plain,(
% 19.43/3.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 19.43/3.01    inference(definition_unfolding,[],[f45,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f58,plain,(
% 19.43/3.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 19.43/3.01    inference(cnf_transformation,[],[f34])).
% 19.43/3.01  
% 19.43/3.01  fof(f11,axiom,(
% 19.43/3.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 19.43/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.43/3.01  
% 19.43/3.01  fof(f20,plain,(
% 19.43/3.01    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.43/3.01    inference(ennf_transformation,[],[f11])).
% 19.43/3.01  
% 19.43/3.01  fof(f60,plain,(
% 19.43/3.01    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.43/3.01    inference(cnf_transformation,[],[f20])).
% 19.43/3.01  
% 19.43/3.01  fof(f39,plain,(
% 19.43/3.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 19.43/3.01    inference(cnf_transformation,[],[f28])).
% 19.43/3.01  
% 19.43/3.01  fof(f70,plain,(
% 19.43/3.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 19.43/3.01    inference(definition_unfolding,[],[f39,f43])).
% 19.43/3.01  
% 19.43/3.01  fof(f79,plain,(
% 19.43/3.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 19.43/3.01    inference(equality_resolution,[],[f70])).
% 19.43/3.01  
% 19.43/3.01  fof(f65,plain,(
% 19.43/3.01    k1_xboole_0 != sK3),
% 19.43/3.01    inference(cnf_transformation,[],[f36])).
% 19.43/3.01  
% 19.43/3.01  cnf(c_3,plain,
% 19.43/3.01      ( r2_hidden(sK0(X0,X1,X2),X0)
% 19.43/3.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.43/3.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 19.43/3.01      inference(cnf_transformation,[],[f69]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_858,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 19.43/3.01      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 19.43/3.01      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_9,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 19.43/3.01      inference(cnf_transformation,[],[f75]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_0,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 19.43/3.01      inference(cnf_transformation,[],[f66]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1083,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1194,plain,
% 19.43/3.01      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_1083,c_9]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_5,plain,
% 19.43/3.01      ( ~ r2_hidden(X0,X1)
% 19.43/3.01      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 19.43/3.01      inference(cnf_transformation,[],[f80]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_856,plain,
% 19.43/3.01      ( r2_hidden(X0,X1) != iProver_top
% 19.43/3.01      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_2732,plain,
% 19.43/3.01      ( r2_hidden(X0,X1) != iProver_top
% 19.43/3.01      | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_1083,c_856]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_6,plain,
% 19.43/3.01      ( r2_hidden(X0,X1)
% 19.43/3.01      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 19.43/3.01      inference(cnf_transformation,[],[f81]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_855,plain,
% 19.43/3.01      ( r2_hidden(X0,X1) = iProver_top
% 19.43/3.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_2236,plain,
% 19.43/3.01      ( r2_hidden(X0,X1) = iProver_top
% 19.43/3.01      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_0,c_855]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_9921,plain,
% 19.43/3.01      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 19.43/3.01      inference(forward_subsumption_resolution,
% 19.43/3.01                [status(thm)],
% 19.43/3.01                [c_2732,c_2236]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_9927,plain,
% 19.43/3.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_1194,c_9921]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_9989,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 19.43/3.01      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_858,c_9927]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_26,negated_conjecture,
% 19.43/3.01      ( r1_tarski(sK3,sK4) ),
% 19.43/3.01      inference(cnf_transformation,[],[f63]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_837,plain,
% 19.43/3.01      ( r1_tarski(sK3,sK4) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_15,plain,
% 19.43/3.01      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 19.43/3.01      inference(cnf_transformation,[],[f82]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_847,plain,
% 19.43/3.01      ( r1_tarski(X0,X1) != iProver_top
% 19.43/3.01      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_19,plain,
% 19.43/3.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 19.43/3.01      inference(cnf_transformation,[],[f56]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_843,plain,
% 19.43/3.01      ( m1_subset_1(X0,X1) = iProver_top
% 19.43/3.01      | r2_hidden(X0,X1) != iProver_top
% 19.43/3.01      | v1_xboole_0(X1) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1976,plain,
% 19.43/3.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 19.43/3.01      | r1_tarski(X0,X1) != iProver_top
% 19.43/3.01      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_847,c_843]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_23,plain,
% 19.43/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.43/3.01      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 19.43/3.01      inference(cnf_transformation,[],[f61]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_839,plain,
% 19.43/3.01      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 19.43/3.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_8307,plain,
% 19.43/3.01      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 19.43/3.01      | r1_tarski(X1,X0) != iProver_top
% 19.43/3.01      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_1976,c_839]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_28422,plain,
% 19.43/3.01      ( k3_subset_1(sK4,k3_subset_1(sK4,sK3)) = sK3
% 19.43/3.01      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_837,c_8307]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_27,negated_conjecture,
% 19.43/3.01      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 19.43/3.01      inference(cnf_transformation,[],[f62]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_29,plain,
% 19.43/3.01      ( r1_tarski(sK3,sK4) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_25,negated_conjecture,
% 19.43/3.01      ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) ),
% 19.43/3.01      inference(cnf_transformation,[],[f64]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_294,plain,( X0 = X0 ),theory(equality) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_311,plain,
% 19.43/3.01      ( sK3 = sK3 ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_294]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1051,plain,
% 19.43/3.01      ( ~ r1_tarski(sK3,sK4) | r2_hidden(sK3,k1_zfmisc_1(sK4)) ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_15]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1052,plain,
% 19.43/3.01      ( r1_tarski(sK3,sK4) != iProver_top
% 19.43/3.01      | r2_hidden(sK3,k1_zfmisc_1(sK4)) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_21,plain,
% 19.43/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.43/3.01      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 19.43/3.01      inference(cnf_transformation,[],[f78]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1107,plain,
% 19.43/3.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK2))
% 19.43/3.01      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k3_subset_1(sK2,sK4) ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_21]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1175,plain,
% 19.43/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK4))
% 19.43/3.01      | ~ r2_hidden(sK3,k1_zfmisc_1(sK4))
% 19.43/3.01      | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_19]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1176,plain,
% 19.43/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top
% 19.43/3.01      | r2_hidden(sK3,k1_zfmisc_1(sK4)) != iProver_top
% 19.43/3.01      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_11,plain,
% 19.43/3.01      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 19.43/3.01      inference(cnf_transformation,[],[f76]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1246,plain,
% 19.43/3.01      ( r1_xboole_0(sK3,sK4)
% 19.43/3.01      | k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) != sK3 ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_11]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1247,plain,
% 19.43/3.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) != sK3
% 19.43/3.01      | r1_xboole_0(sK3,sK4) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_1246]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1392,plain,
% 19.43/3.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK4))
% 19.43/3.01      | k3_subset_1(sK4,k3_subset_1(sK4,sK3)) = sK3 ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_23]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1396,plain,
% 19.43/3.01      ( k3_subset_1(sK4,k3_subset_1(sK4,sK3)) = sK3
% 19.43/3.01      | m1_subset_1(sK3,k1_zfmisc_1(sK4)) != iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_12,plain,
% 19.43/3.01      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 19.43/3.01      inference(cnf_transformation,[],[f77]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1422,plain,
% 19.43/3.01      ( ~ r1_xboole_0(sK3,sK4)
% 19.43/3.01      | k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = sK3 ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_12]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_10,plain,
% 19.43/3.01      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 19.43/3.01      inference(cnf_transformation,[],[f48]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1547,plain,
% 19.43/3.01      ( ~ r1_xboole_0(sK3,sK4) | v1_xboole_0(sK3) ),
% 19.43/3.01      inference(resolution,[status(thm)],[c_10,c_26]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1548,plain,
% 19.43/3.01      ( r1_xboole_0(sK3,sK4) != iProver_top
% 19.43/3.01      | v1_xboole_0(sK3) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_1547]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_299,plain,
% 19.43/3.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.43/3.01      theory(equality) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1138,plain,
% 19.43/3.01      ( r1_tarski(X0,X1)
% 19.43/3.01      | ~ r1_tarski(sK3,k3_subset_1(sK2,sK4))
% 19.43/3.01      | X1 != k3_subset_1(sK2,sK4)
% 19.43/3.01      | X0 != sK3 ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_299]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1271,plain,
% 19.43/3.01      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 19.43/3.01      | ~ r1_tarski(sK3,k3_subset_1(sK2,sK4))
% 19.43/3.01      | X0 != sK3
% 19.43/3.01      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k3_subset_1(sK2,sK4) ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_1138]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_2076,plain,
% 19.43/3.01      ( r1_tarski(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)))
% 19.43/3.01      | ~ r1_tarski(sK3,k3_subset_1(sK2,sK4))
% 19.43/3.01      | X0 != sK3
% 19.43/3.01      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) != k3_subset_1(sK2,sK4) ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_1271]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_2078,plain,
% 19.43/3.01      ( ~ r1_tarski(sK3,k3_subset_1(sK2,sK4))
% 19.43/3.01      | r1_tarski(sK3,k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)))
% 19.43/3.01      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) != k3_subset_1(sK2,sK4)
% 19.43/3.01      | sK3 != sK3 ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_2076]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_7,plain,
% 19.43/3.01      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 19.43/3.01      | r1_xboole_0(X0,X2) ),
% 19.43/3.01      inference(cnf_transformation,[],[f73]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_2142,plain,
% 19.43/3.01      ( ~ r1_tarski(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)))
% 19.43/3.01      | r1_xboole_0(X0,sK4) ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_7]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_2144,plain,
% 19.43/3.01      ( ~ r1_tarski(sK3,k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)))
% 19.43/3.01      | r1_xboole_0(sK3,sK4) ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_2142]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_17,plain,
% 19.43/3.01      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 19.43/3.01      inference(cnf_transformation,[],[f58]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1726,plain,
% 19.43/3.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.43/3.01      | ~ v1_xboole_0(X0)
% 19.43/3.01      | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_17]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_3809,plain,
% 19.43/3.01      ( m1_subset_1(X0,k1_zfmisc_1(sK4))
% 19.43/3.01      | ~ v1_xboole_0(X0)
% 19.43/3.01      | ~ v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_1726]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_3810,plain,
% 19.43/3.01      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) = iProver_top
% 19.43/3.01      | v1_xboole_0(X0) != iProver_top
% 19.43/3.01      | v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_3809]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_3812,plain,
% 19.43/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top
% 19.43/3.01      | v1_xboole_0(k1_zfmisc_1(sK4)) != iProver_top
% 19.43/3.01      | v1_xboole_0(sK3) != iProver_top ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_3810]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_28913,plain,
% 19.43/3.01      ( k3_subset_1(sK4,k3_subset_1(sK4,sK3)) = sK3 ),
% 19.43/3.01      inference(global_propositional_subsumption,
% 19.43/3.01                [status(thm)],
% 19.43/3.01                [c_28422,c_27,c_29,c_25,c_311,c_1052,c_1107,c_1176,
% 19.43/3.01                 c_1247,c_1396,c_1422,c_1548,c_2078,c_2144,c_3812]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_22,plain,
% 19.43/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.43/3.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 19.43/3.01      inference(cnf_transformation,[],[f60]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_840,plain,
% 19.43/3.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.43/3.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_28918,plain,
% 19.43/3.01      ( m1_subset_1(k3_subset_1(sK4,sK3),k1_zfmisc_1(sK4)) != iProver_top
% 19.43/3.01      | m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_28913,c_840]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_28932,plain,
% 19.43/3.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK4)) = iProver_top ),
% 19.43/3.01      inference(global_propositional_subsumption,
% 19.43/3.01                [status(thm)],
% 19.43/3.01                [c_28918,c_27,c_29,c_25,c_311,c_1052,c_1107,c_1176,
% 19.43/3.01                 c_1247,c_1422,c_1548,c_2078,c_2144,c_3812]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_841,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 19.43/3.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_28940,plain,
% 19.43/3.01      ( k5_xboole_0(sK4,k3_xboole_0(sK4,sK3)) = k3_subset_1(sK4,sK3) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_28932,c_841]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1084,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1882,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_1084,c_0]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_29155,plain,
% 19.43/3.01      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3)))) = k3_xboole_0(sK4,k3_xboole_0(sK4,sK3)) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_28940,c_1882]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_32280,plain,
% 19.43/3.01      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,sK3))))) = k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3)))) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_29155,c_1882]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_2518,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,X1))) = k3_subset_1(X0,k3_subset_1(X0,X1))
% 19.43/3.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_840,c_841]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_52768,plain,
% 19.43/3.01      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3))) = k3_subset_1(sK4,k3_subset_1(sK4,sK3)) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_28932,c_2518]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_29157,plain,
% 19.43/3.01      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3))) = k3_xboole_0(sK4,sK3) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_28940,c_0]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_52786,plain,
% 19.43/3.01      ( k3_xboole_0(sK4,sK3) = sK3 ),
% 19.43/3.01      inference(light_normalisation,
% 19.43/3.01                [status(thm)],
% 19.43/3.01                [c_52768,c_28913,c_29157]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_72572,plain,
% 19.43/3.01      ( k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3)))) = k5_xboole_0(sK4,sK3) ),
% 19.43/3.01      inference(light_normalisation,[status(thm)],[c_32280,c_52786]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_72635,plain,
% 19.43/3.01      ( r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(sK4,sK3))) != iProver_top
% 19.43/3.01      | r2_hidden(X0,sK4) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_72572,c_855]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_4,plain,
% 19.43/3.01      ( ~ r2_hidden(X0,X1)
% 19.43/3.01      | r2_hidden(X0,X2)
% 19.43/3.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 19.43/3.01      inference(cnf_transformation,[],[f79]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_857,plain,
% 19.43/3.01      ( r2_hidden(X0,X1) != iProver_top
% 19.43/3.01      | r2_hidden(X0,X2) = iProver_top
% 19.43/3.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_52934,plain,
% 19.43/3.01      ( r2_hidden(X0,k5_xboole_0(sK4,sK3)) = iProver_top
% 19.43/3.01      | r2_hidden(X0,sK4) != iProver_top
% 19.43/3.01      | r2_hidden(X0,sK3) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_52786,c_857]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_52937,plain,
% 19.43/3.01      ( r2_hidden(X0,sK4) = iProver_top
% 19.43/3.01      | r2_hidden(X0,sK3) != iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_52786,c_2236]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_838,plain,
% 19.43/3.01      ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_836,plain,
% 19.43/3.01      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_2519,plain,
% 19.43/3.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k3_subset_1(sK2,sK4) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_836,c_841]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_854,plain,
% 19.43/3.01      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 19.43/3.01      | r1_xboole_0(X0,X2) = iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_5493,plain,
% 19.43/3.01      ( r1_tarski(X0,k3_subset_1(sK2,sK4)) != iProver_top
% 19.43/3.01      | r1_xboole_0(X0,sK4) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_2519,c_854]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_8158,plain,
% 19.43/3.01      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_838,c_5493]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_850,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 19.43/3.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 19.43/3.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_8298,plain,
% 19.43/3.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = sK3 ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_8158,c_850]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_8612,plain,
% 19.43/3.01      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK3)) = k3_xboole_0(sK3,sK4) ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_8298,c_0]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_8638,plain,
% 19.43/3.01      ( k3_xboole_0(sK3,sK4) = k3_xboole_0(sK3,k1_xboole_0) ),
% 19.43/3.01      inference(demodulation,[status(thm)],[c_8612,c_1083]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_8662,plain,
% 19.43/3.01      ( r2_hidden(X0,k5_xboole_0(sK3,k3_xboole_0(sK3,k1_xboole_0))) != iProver_top
% 19.43/3.01      | r2_hidden(X0,sK4) != iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_8638,c_856]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_8665,plain,
% 19.43/3.01      ( r2_hidden(X0,sK4) != iProver_top
% 19.43/3.01      | r2_hidden(X0,sK3) != iProver_top ),
% 19.43/3.01      inference(demodulation,[status(thm)],[c_8662,c_9]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_54534,plain,
% 19.43/3.01      ( r2_hidden(X0,sK3) != iProver_top ),
% 19.43/3.01      inference(global_propositional_subsumption,
% 19.43/3.01                [status(thm)],
% 19.43/3.01                [c_52937,c_8665]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_2729,plain,
% 19.43/3.01      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 19.43/3.01      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_0,c_856]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_72632,plain,
% 19.43/3.01      ( r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(sK4,sK3))) != iProver_top
% 19.43/3.01      | r2_hidden(X0,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_xboole_0(sK4,k3_subset_1(sK4,sK3))))) != iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_72572,c_2729]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_72693,plain,
% 19.43/3.01      ( r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(sK4,sK3))) != iProver_top
% 19.43/3.01      | r2_hidden(X0,k5_xboole_0(sK4,sK3)) != iProver_top ),
% 19.43/3.01      inference(light_normalisation,[status(thm)],[c_72632,c_72572]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_73452,plain,
% 19.43/3.01      ( r2_hidden(X0,k5_xboole_0(sK4,k5_xboole_0(sK4,sK3))) != iProver_top ),
% 19.43/3.01      inference(global_propositional_subsumption,
% 19.43/3.01                [status(thm)],
% 19.43/3.01                [c_72635,c_8665,c_52934,c_52937,c_72693]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_73475,plain,
% 19.43/3.01      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,sK3)),k3_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,sK3)),X0)) = k1_xboole_0 ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_9989,c_73452]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_54542,plain,
% 19.43/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK3
% 19.43/3.01      | r2_hidden(sK0(X0,X1,sK3),X0) = iProver_top ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_858,c_54534]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_73487,plain,
% 19.43/3.01      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,sK3)),k3_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,sK3)),X0)) = sK3 ),
% 19.43/3.01      inference(superposition,[status(thm)],[c_54542,c_73452]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_73535,plain,
% 19.43/3.01      ( sK3 = k1_xboole_0 ),
% 19.43/3.01      inference(demodulation,[status(thm)],[c_73475,c_73487]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1269,plain,
% 19.43/3.01      ( k1_xboole_0 = k1_xboole_0 ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_294]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_295,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1106,plain,
% 19.43/3.01      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_295]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_1268,plain,
% 19.43/3.01      ( sK3 != k1_xboole_0
% 19.43/3.01      | k1_xboole_0 = sK3
% 19.43/3.01      | k1_xboole_0 != k1_xboole_0 ),
% 19.43/3.01      inference(instantiation,[status(thm)],[c_1106]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(c_24,negated_conjecture,
% 19.43/3.01      ( k1_xboole_0 != sK3 ),
% 19.43/3.01      inference(cnf_transformation,[],[f65]) ).
% 19.43/3.01  
% 19.43/3.01  cnf(contradiction,plain,
% 19.43/3.01      ( $false ),
% 19.43/3.01      inference(minisat,[status(thm)],[c_73535,c_1269,c_1268,c_24]) ).
% 19.43/3.01  
% 19.43/3.01  
% 19.43/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.43/3.01  
% 19.43/3.01  ------                               Statistics
% 19.43/3.01  
% 19.43/3.01  ------ Selected
% 19.43/3.01  
% 19.43/3.01  total_time:                             2.109
% 19.43/3.01  
%------------------------------------------------------------------------------
