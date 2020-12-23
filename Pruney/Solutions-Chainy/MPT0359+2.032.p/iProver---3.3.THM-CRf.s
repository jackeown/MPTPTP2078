%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:06 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  148 (1272 expanded)
%              Number of clauses        :   79 ( 390 expanded)
%              Number of leaves         :   20 ( 281 expanded)
%              Depth                    :   25
%              Number of atoms          :  443 (4425 expanded)
%              Number of equality atoms :  178 (1399 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK3) != sK4
        | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) )
      & ( k2_subset_1(sK3) = sK4
        | r1_tarski(k3_subset_1(sK3,sK4),sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k2_subset_1(sK3) != sK4
      | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) )
    & ( k2_subset_1(sK3) = sK4
      | r1_tarski(k3_subset_1(sK3,sK4),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f37])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f66,plain,
    ( k2_subset_1(sK3) != sK4
    | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f62,f58])).

fof(f76,plain,
    ( k3_subset_1(sK3,k1_xboole_0) != sK4
    | ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,
    ( k2_subset_1(sK3) = sK4
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,
    ( k3_subset_1(sK3,k1_xboole_0) = sK4
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f55])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_958,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_334,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_335,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_1135,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
    inference(equality_resolution,[status(thm)],[c_335])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_949,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2632,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_949])).

cnf(c_494,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_508,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k3_subset_1(sK3,k1_xboole_0) != sK4 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_945,plain,
    ( k3_subset_1(sK3,k1_xboole_0) != sK4
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1003,plain,
    ( sK4 != sK3
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_945,c_18])).

cnf(c_1087,plain,
    ( ~ r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | sK4 != sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1003])).

cnf(c_1222,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_495,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1224,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_1254,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_1255,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | k3_subset_1(sK3,k1_xboole_0) = sK4 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_944,plain,
    ( k3_subset_1(sK3,k1_xboole_0) = sK4
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_973,plain,
    ( sK4 = sK3
    | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_944,c_18])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_947,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1235,plain,
    ( k3_xboole_0(k3_subset_1(sK3,sK4),sK4) = k3_subset_1(sK3,sK4)
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_973,c_947])).

cnf(c_1469,plain,
    ( k3_xboole_0(sK4,k3_subset_1(sK3,sK4)) = k3_subset_1(sK3,sK4)
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_0,c_1235])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_954,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1547,plain,
    ( sK4 = sK3
    | r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_954])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_961,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_962,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1853,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_962])).

cnf(c_1857,plain,
    ( r1_tarski(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1853])).

cnf(c_1859,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1857])).

cnf(c_497,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1976,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_1978,plain,
    ( ~ r1_tarski(sK4,sK4)
    | r1_tarski(sK3,sK4)
    | sK4 != sK4
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_948,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1911,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_948])).

cnf(c_2021,plain,
    ( r2_hidden(sK0(k3_subset_1(sK3,sK4),X0),sK3) = iProver_top
    | r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_1911])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_960,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2029,plain,
    ( r2_hidden(sK0(k3_subset_1(sK3,sK4),X0),X1) = iProver_top
    | r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2021,c_960])).

cnf(c_2256,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2029,c_962])).

cnf(c_2311,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),X0)
    | ~ r1_tarski(sK3,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2256])).

cnf(c_2313,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
    | ~ r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2311])).

cnf(c_2947,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2632,c_508,c_1087,c_1222,c_1255,c_1547,c_1859,c_1978,c_2313])).

cnf(c_4708,plain,
    ( k3_xboole_0(X0,k3_subset_1(sK3,sK4)) = X1
    | r2_hidden(sK1(X0,k3_subset_1(sK3,sK4),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_2947])).

cnf(c_5708,plain,
    ( k3_xboole_0(X0,k3_subset_1(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_4708,c_2947])).

cnf(c_17,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_946,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1234,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_946,c_947])).

cnf(c_6066,plain,
    ( k3_subset_1(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5708,c_1234])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_950,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3419,plain,
    ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_950])).

cnf(c_3714,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3419,c_508,c_1087,c_1222,c_1255,c_1547,c_1859,c_1978,c_2313,c_2632])).

cnf(c_3722,plain,
    ( r2_hidden(sK0(sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_3714])).

cnf(c_3877,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3722,c_962])).

cnf(c_4159,plain,
    ( k3_xboole_0(sK3,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_3877,c_947])).

cnf(c_7817,plain,
    ( k3_subset_1(sK3,sK4) = k5_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_4159,c_1135])).

cnf(c_13673,plain,
    ( k5_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6066,c_7817])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_325,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_326,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK4)) = sK4
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_1132,plain,
    ( k3_subset_1(sK3,k3_subset_1(sK3,sK4)) = sK4 ),
    inference(equality_resolution,[status(thm)],[c_326])).

cnf(c_8093,plain,
    ( k3_subset_1(sK3,k5_xboole_0(sK3,sK3)) = sK4 ),
    inference(demodulation,[status(thm)],[c_7817,c_1132])).

cnf(c_13694,plain,
    ( k3_subset_1(sK3,k1_xboole_0) = sK4 ),
    inference(demodulation,[status(thm)],[c_13673,c_8093])).

cnf(c_13696,plain,
    ( sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_13694,c_18])).

cnf(c_2954,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_2947])).

cnf(c_2970,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2954])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13696,c_2970,c_1003])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:44:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.64/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.99  
% 3.64/0.99  ------  iProver source info
% 3.64/0.99  
% 3.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.99  git: non_committed_changes: false
% 3.64/0.99  git: last_make_outside_of_git: false
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  ------ Input Options
% 3.64/0.99  
% 3.64/0.99  --out_options                           all
% 3.64/0.99  --tptp_safe_out                         true
% 3.64/0.99  --problem_path                          ""
% 3.64/0.99  --include_path                          ""
% 3.64/0.99  --clausifier                            res/vclausify_rel
% 3.64/0.99  --clausifier_options                    --mode clausify
% 3.64/0.99  --stdin                                 false
% 3.64/0.99  --stats_out                             all
% 3.64/0.99  
% 3.64/0.99  ------ General Options
% 3.64/0.99  
% 3.64/0.99  --fof                                   false
% 3.64/0.99  --time_out_real                         305.
% 3.64/0.99  --time_out_virtual                      -1.
% 3.64/0.99  --symbol_type_check                     false
% 3.64/0.99  --clausify_out                          false
% 3.64/0.99  --sig_cnt_out                           false
% 3.64/0.99  --trig_cnt_out                          false
% 3.64/0.99  --trig_cnt_out_tolerance                1.
% 3.64/0.99  --trig_cnt_out_sk_spl                   false
% 3.64/0.99  --abstr_cl_out                          false
% 3.64/0.99  
% 3.64/0.99  ------ Global Options
% 3.64/0.99  
% 3.64/0.99  --schedule                              default
% 3.64/0.99  --add_important_lit                     false
% 3.64/0.99  --prop_solver_per_cl                    1000
% 3.64/0.99  --min_unsat_core                        false
% 3.64/0.99  --soft_assumptions                      false
% 3.64/0.99  --soft_lemma_size                       3
% 3.64/0.99  --prop_impl_unit_size                   0
% 3.64/0.99  --prop_impl_unit                        []
% 3.64/0.99  --share_sel_clauses                     true
% 3.64/0.99  --reset_solvers                         false
% 3.64/0.99  --bc_imp_inh                            [conj_cone]
% 3.64/0.99  --conj_cone_tolerance                   3.
% 3.64/0.99  --extra_neg_conj                        none
% 3.64/0.99  --large_theory_mode                     true
% 3.64/0.99  --prolific_symb_bound                   200
% 3.64/0.99  --lt_threshold                          2000
% 3.64/0.99  --clause_weak_htbl                      true
% 3.64/0.99  --gc_record_bc_elim                     false
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing Options
% 3.64/0.99  
% 3.64/0.99  --preprocessing_flag                    true
% 3.64/0.99  --time_out_prep_mult                    0.1
% 3.64/0.99  --splitting_mode                        input
% 3.64/0.99  --splitting_grd                         true
% 3.64/0.99  --splitting_cvd                         false
% 3.64/0.99  --splitting_cvd_svl                     false
% 3.64/0.99  --splitting_nvd                         32
% 3.64/0.99  --sub_typing                            true
% 3.64/0.99  --prep_gs_sim                           true
% 3.64/0.99  --prep_unflatten                        true
% 3.64/0.99  --prep_res_sim                          true
% 3.64/0.99  --prep_upred                            true
% 3.64/0.99  --prep_sem_filter                       exhaustive
% 3.64/0.99  --prep_sem_filter_out                   false
% 3.64/0.99  --pred_elim                             true
% 3.64/0.99  --res_sim_input                         true
% 3.64/0.99  --eq_ax_congr_red                       true
% 3.64/0.99  --pure_diseq_elim                       true
% 3.64/0.99  --brand_transform                       false
% 3.64/0.99  --non_eq_to_eq                          false
% 3.64/0.99  --prep_def_merge                        true
% 3.64/0.99  --prep_def_merge_prop_impl              false
% 3.64/0.99  --prep_def_merge_mbd                    true
% 3.64/0.99  --prep_def_merge_tr_red                 false
% 3.64/0.99  --prep_def_merge_tr_cl                  false
% 3.64/0.99  --smt_preprocessing                     true
% 3.64/0.99  --smt_ac_axioms                         fast
% 3.64/0.99  --preprocessed_out                      false
% 3.64/0.99  --preprocessed_stats                    false
% 3.64/0.99  
% 3.64/0.99  ------ Abstraction refinement Options
% 3.64/0.99  
% 3.64/0.99  --abstr_ref                             []
% 3.64/0.99  --abstr_ref_prep                        false
% 3.64/0.99  --abstr_ref_until_sat                   false
% 3.64/0.99  --abstr_ref_sig_restrict                funpre
% 3.64/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.99  --abstr_ref_under                       []
% 3.64/0.99  
% 3.64/0.99  ------ SAT Options
% 3.64/0.99  
% 3.64/0.99  --sat_mode                              false
% 3.64/0.99  --sat_fm_restart_options                ""
% 3.64/0.99  --sat_gr_def                            false
% 3.64/0.99  --sat_epr_types                         true
% 3.64/0.99  --sat_non_cyclic_types                  false
% 3.64/0.99  --sat_finite_models                     false
% 3.64/0.99  --sat_fm_lemmas                         false
% 3.64/0.99  --sat_fm_prep                           false
% 3.64/0.99  --sat_fm_uc_incr                        true
% 3.64/0.99  --sat_out_model                         small
% 3.64/0.99  --sat_out_clauses                       false
% 3.64/0.99  
% 3.64/0.99  ------ QBF Options
% 3.64/0.99  
% 3.64/0.99  --qbf_mode                              false
% 3.64/0.99  --qbf_elim_univ                         false
% 3.64/0.99  --qbf_dom_inst                          none
% 3.64/0.99  --qbf_dom_pre_inst                      false
% 3.64/0.99  --qbf_sk_in                             false
% 3.64/0.99  --qbf_pred_elim                         true
% 3.64/0.99  --qbf_split                             512
% 3.64/0.99  
% 3.64/0.99  ------ BMC1 Options
% 3.64/0.99  
% 3.64/0.99  --bmc1_incremental                      false
% 3.64/0.99  --bmc1_axioms                           reachable_all
% 3.64/0.99  --bmc1_min_bound                        0
% 3.64/0.99  --bmc1_max_bound                        -1
% 3.64/0.99  --bmc1_max_bound_default                -1
% 3.64/0.99  --bmc1_symbol_reachability              true
% 3.64/0.99  --bmc1_property_lemmas                  false
% 3.64/0.99  --bmc1_k_induction                      false
% 3.64/0.99  --bmc1_non_equiv_states                 false
% 3.64/0.99  --bmc1_deadlock                         false
% 3.64/0.99  --bmc1_ucm                              false
% 3.64/0.99  --bmc1_add_unsat_core                   none
% 3.64/0.99  --bmc1_unsat_core_children              false
% 3.64/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.99  --bmc1_out_stat                         full
% 3.64/0.99  --bmc1_ground_init                      false
% 3.64/0.99  --bmc1_pre_inst_next_state              false
% 3.64/0.99  --bmc1_pre_inst_state                   false
% 3.64/0.99  --bmc1_pre_inst_reach_state             false
% 3.64/0.99  --bmc1_out_unsat_core                   false
% 3.64/0.99  --bmc1_aig_witness_out                  false
% 3.64/0.99  --bmc1_verbose                          false
% 3.64/0.99  --bmc1_dump_clauses_tptp                false
% 3.64/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.99  --bmc1_dump_file                        -
% 3.64/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.99  --bmc1_ucm_extend_mode                  1
% 3.64/0.99  --bmc1_ucm_init_mode                    2
% 3.64/0.99  --bmc1_ucm_cone_mode                    none
% 3.64/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.99  --bmc1_ucm_relax_model                  4
% 3.64/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.99  --bmc1_ucm_layered_model                none
% 3.64/0.99  --bmc1_ucm_max_lemma_size               10
% 3.64/0.99  
% 3.64/0.99  ------ AIG Options
% 3.64/0.99  
% 3.64/0.99  --aig_mode                              false
% 3.64/0.99  
% 3.64/0.99  ------ Instantiation Options
% 3.64/0.99  
% 3.64/0.99  --instantiation_flag                    true
% 3.64/0.99  --inst_sos_flag                         false
% 3.64/0.99  --inst_sos_phase                        true
% 3.64/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel_side                     num_symb
% 3.64/0.99  --inst_solver_per_active                1400
% 3.64/0.99  --inst_solver_calls_frac                1.
% 3.64/0.99  --inst_passive_queue_type               priority_queues
% 3.64/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.99  --inst_passive_queues_freq              [25;2]
% 3.64/0.99  --inst_dismatching                      true
% 3.64/0.99  --inst_eager_unprocessed_to_passive     true
% 3.64/0.99  --inst_prop_sim_given                   true
% 3.64/0.99  --inst_prop_sim_new                     false
% 3.64/0.99  --inst_subs_new                         false
% 3.64/0.99  --inst_eq_res_simp                      false
% 3.64/0.99  --inst_subs_given                       false
% 3.64/0.99  --inst_orphan_elimination               true
% 3.64/0.99  --inst_learning_loop_flag               true
% 3.64/0.99  --inst_learning_start                   3000
% 3.64/0.99  --inst_learning_factor                  2
% 3.64/0.99  --inst_start_prop_sim_after_learn       3
% 3.64/0.99  --inst_sel_renew                        solver
% 3.64/0.99  --inst_lit_activity_flag                true
% 3.64/0.99  --inst_restr_to_given                   false
% 3.64/0.99  --inst_activity_threshold               500
% 3.64/0.99  --inst_out_proof                        true
% 3.64/0.99  
% 3.64/0.99  ------ Resolution Options
% 3.64/0.99  
% 3.64/0.99  --resolution_flag                       true
% 3.64/0.99  --res_lit_sel                           adaptive
% 3.64/0.99  --res_lit_sel_side                      none
% 3.64/0.99  --res_ordering                          kbo
% 3.64/0.99  --res_to_prop_solver                    active
% 3.64/0.99  --res_prop_simpl_new                    false
% 3.64/0.99  --res_prop_simpl_given                  true
% 3.64/0.99  --res_passive_queue_type                priority_queues
% 3.64/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.99  --res_passive_queues_freq               [15;5]
% 3.64/0.99  --res_forward_subs                      full
% 3.64/0.99  --res_backward_subs                     full
% 3.64/0.99  --res_forward_subs_resolution           true
% 3.64/0.99  --res_backward_subs_resolution          true
% 3.64/0.99  --res_orphan_elimination                true
% 3.64/0.99  --res_time_limit                        2.
% 3.64/0.99  --res_out_proof                         true
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Options
% 3.64/0.99  
% 3.64/0.99  --superposition_flag                    true
% 3.64/0.99  --sup_passive_queue_type                priority_queues
% 3.64/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.64/0.99  --demod_completeness_check              fast
% 3.64/0.99  --demod_use_ground                      true
% 3.64/0.99  --sup_to_prop_solver                    passive
% 3.64/0.99  --sup_prop_simpl_new                    true
% 3.64/0.99  --sup_prop_simpl_given                  true
% 3.64/0.99  --sup_fun_splitting                     false
% 3.64/0.99  --sup_smt_interval                      50000
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Simplification Setup
% 3.64/0.99  
% 3.64/0.99  --sup_indices_passive                   []
% 3.64/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_full_bw                           [BwDemod]
% 3.64/0.99  --sup_immed_triv                        [TrivRules]
% 3.64/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_immed_bw_main                     []
% 3.64/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  
% 3.64/0.99  ------ Combination Options
% 3.64/0.99  
% 3.64/0.99  --comb_res_mult                         3
% 3.64/0.99  --comb_sup_mult                         2
% 3.64/0.99  --comb_inst_mult                        10
% 3.64/0.99  
% 3.64/0.99  ------ Debug Options
% 3.64/0.99  
% 3.64/0.99  --dbg_backtrace                         false
% 3.64/0.99  --dbg_dump_prop_clauses                 false
% 3.64/0.99  --dbg_dump_prop_clauses_file            -
% 3.64/0.99  --dbg_out_stat                          false
% 3.64/0.99  ------ Parsing...
% 3.64/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  ------ Proving...
% 3.64/0.99  ------ Problem Properties 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  clauses                                 25
% 3.64/0.99  conjectures                             2
% 3.64/0.99  EPR                                     2
% 3.64/0.99  Horn                                    17
% 3.64/0.99  unary                                   3
% 3.64/0.99  binary                                  13
% 3.64/0.99  lits                                    58
% 3.64/0.99  lits eq                                 19
% 3.64/0.99  fd_pure                                 0
% 3.64/0.99  fd_pseudo                               0
% 3.64/0.99  fd_cond                                 0
% 3.64/0.99  fd_pseudo_cond                          6
% 3.64/0.99  AC symbols                              0
% 3.64/0.99  
% 3.64/0.99  ------ Schedule dynamic 5 is on 
% 3.64/0.99  
% 3.64/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  Current options:
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  ------ Input Options
% 3.64/0.99  
% 3.64/0.99  --out_options                           all
% 3.64/0.99  --tptp_safe_out                         true
% 3.64/0.99  --problem_path                          ""
% 3.64/0.99  --include_path                          ""
% 3.64/0.99  --clausifier                            res/vclausify_rel
% 3.64/0.99  --clausifier_options                    --mode clausify
% 3.64/0.99  --stdin                                 false
% 3.64/0.99  --stats_out                             all
% 3.64/0.99  
% 3.64/0.99  ------ General Options
% 3.64/0.99  
% 3.64/0.99  --fof                                   false
% 3.64/0.99  --time_out_real                         305.
% 3.64/0.99  --time_out_virtual                      -1.
% 3.64/0.99  --symbol_type_check                     false
% 3.64/0.99  --clausify_out                          false
% 3.64/0.99  --sig_cnt_out                           false
% 3.64/0.99  --trig_cnt_out                          false
% 3.64/0.99  --trig_cnt_out_tolerance                1.
% 3.64/0.99  --trig_cnt_out_sk_spl                   false
% 3.64/0.99  --abstr_cl_out                          false
% 3.64/0.99  
% 3.64/0.99  ------ Global Options
% 3.64/0.99  
% 3.64/0.99  --schedule                              default
% 3.64/0.99  --add_important_lit                     false
% 3.64/0.99  --prop_solver_per_cl                    1000
% 3.64/0.99  --min_unsat_core                        false
% 3.64/0.99  --soft_assumptions                      false
% 3.64/0.99  --soft_lemma_size                       3
% 3.64/0.99  --prop_impl_unit_size                   0
% 3.64/0.99  --prop_impl_unit                        []
% 3.64/0.99  --share_sel_clauses                     true
% 3.64/0.99  --reset_solvers                         false
% 3.64/0.99  --bc_imp_inh                            [conj_cone]
% 3.64/0.99  --conj_cone_tolerance                   3.
% 3.64/0.99  --extra_neg_conj                        none
% 3.64/0.99  --large_theory_mode                     true
% 3.64/0.99  --prolific_symb_bound                   200
% 3.64/0.99  --lt_threshold                          2000
% 3.64/0.99  --clause_weak_htbl                      true
% 3.64/0.99  --gc_record_bc_elim                     false
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing Options
% 3.64/0.99  
% 3.64/0.99  --preprocessing_flag                    true
% 3.64/0.99  --time_out_prep_mult                    0.1
% 3.64/0.99  --splitting_mode                        input
% 3.64/0.99  --splitting_grd                         true
% 3.64/0.99  --splitting_cvd                         false
% 3.64/0.99  --splitting_cvd_svl                     false
% 3.64/0.99  --splitting_nvd                         32
% 3.64/0.99  --sub_typing                            true
% 3.64/0.99  --prep_gs_sim                           true
% 3.64/0.99  --prep_unflatten                        true
% 3.64/0.99  --prep_res_sim                          true
% 3.64/0.99  --prep_upred                            true
% 3.64/0.99  --prep_sem_filter                       exhaustive
% 3.64/0.99  --prep_sem_filter_out                   false
% 3.64/0.99  --pred_elim                             true
% 3.64/0.99  --res_sim_input                         true
% 3.64/0.99  --eq_ax_congr_red                       true
% 3.64/0.99  --pure_diseq_elim                       true
% 3.64/0.99  --brand_transform                       false
% 3.64/0.99  --non_eq_to_eq                          false
% 3.64/0.99  --prep_def_merge                        true
% 3.64/0.99  --prep_def_merge_prop_impl              false
% 3.64/0.99  --prep_def_merge_mbd                    true
% 3.64/0.99  --prep_def_merge_tr_red                 false
% 3.64/0.99  --prep_def_merge_tr_cl                  false
% 3.64/0.99  --smt_preprocessing                     true
% 3.64/0.99  --smt_ac_axioms                         fast
% 3.64/0.99  --preprocessed_out                      false
% 3.64/0.99  --preprocessed_stats                    false
% 3.64/0.99  
% 3.64/0.99  ------ Abstraction refinement Options
% 3.64/0.99  
% 3.64/0.99  --abstr_ref                             []
% 3.64/0.99  --abstr_ref_prep                        false
% 3.64/0.99  --abstr_ref_until_sat                   false
% 3.64/0.99  --abstr_ref_sig_restrict                funpre
% 3.64/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.99  --abstr_ref_under                       []
% 3.64/0.99  
% 3.64/0.99  ------ SAT Options
% 3.64/0.99  
% 3.64/0.99  --sat_mode                              false
% 3.64/0.99  --sat_fm_restart_options                ""
% 3.64/0.99  --sat_gr_def                            false
% 3.64/0.99  --sat_epr_types                         true
% 3.64/0.99  --sat_non_cyclic_types                  false
% 3.64/0.99  --sat_finite_models                     false
% 3.64/0.99  --sat_fm_lemmas                         false
% 3.64/0.99  --sat_fm_prep                           false
% 3.64/0.99  --sat_fm_uc_incr                        true
% 3.64/0.99  --sat_out_model                         small
% 3.64/0.99  --sat_out_clauses                       false
% 3.64/0.99  
% 3.64/0.99  ------ QBF Options
% 3.64/0.99  
% 3.64/0.99  --qbf_mode                              false
% 3.64/0.99  --qbf_elim_univ                         false
% 3.64/0.99  --qbf_dom_inst                          none
% 3.64/0.99  --qbf_dom_pre_inst                      false
% 3.64/0.99  --qbf_sk_in                             false
% 3.64/0.99  --qbf_pred_elim                         true
% 3.64/0.99  --qbf_split                             512
% 3.64/0.99  
% 3.64/0.99  ------ BMC1 Options
% 3.64/0.99  
% 3.64/0.99  --bmc1_incremental                      false
% 3.64/0.99  --bmc1_axioms                           reachable_all
% 3.64/0.99  --bmc1_min_bound                        0
% 3.64/0.99  --bmc1_max_bound                        -1
% 3.64/0.99  --bmc1_max_bound_default                -1
% 3.64/0.99  --bmc1_symbol_reachability              true
% 3.64/0.99  --bmc1_property_lemmas                  false
% 3.64/0.99  --bmc1_k_induction                      false
% 3.64/0.99  --bmc1_non_equiv_states                 false
% 3.64/0.99  --bmc1_deadlock                         false
% 3.64/0.99  --bmc1_ucm                              false
% 3.64/0.99  --bmc1_add_unsat_core                   none
% 3.64/0.99  --bmc1_unsat_core_children              false
% 3.64/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.99  --bmc1_out_stat                         full
% 3.64/0.99  --bmc1_ground_init                      false
% 3.64/0.99  --bmc1_pre_inst_next_state              false
% 3.64/0.99  --bmc1_pre_inst_state                   false
% 3.64/0.99  --bmc1_pre_inst_reach_state             false
% 3.64/0.99  --bmc1_out_unsat_core                   false
% 3.64/0.99  --bmc1_aig_witness_out                  false
% 3.64/0.99  --bmc1_verbose                          false
% 3.64/0.99  --bmc1_dump_clauses_tptp                false
% 3.64/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.99  --bmc1_dump_file                        -
% 3.64/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.99  --bmc1_ucm_extend_mode                  1
% 3.64/0.99  --bmc1_ucm_init_mode                    2
% 3.64/0.99  --bmc1_ucm_cone_mode                    none
% 3.64/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.99  --bmc1_ucm_relax_model                  4
% 3.64/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.99  --bmc1_ucm_layered_model                none
% 3.64/0.99  --bmc1_ucm_max_lemma_size               10
% 3.64/0.99  
% 3.64/0.99  ------ AIG Options
% 3.64/0.99  
% 3.64/0.99  --aig_mode                              false
% 3.64/0.99  
% 3.64/0.99  ------ Instantiation Options
% 3.64/0.99  
% 3.64/0.99  --instantiation_flag                    true
% 3.64/0.99  --inst_sos_flag                         false
% 3.64/0.99  --inst_sos_phase                        true
% 3.64/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel_side                     none
% 3.64/0.99  --inst_solver_per_active                1400
% 3.64/0.99  --inst_solver_calls_frac                1.
% 3.64/0.99  --inst_passive_queue_type               priority_queues
% 3.64/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.99  --inst_passive_queues_freq              [25;2]
% 3.64/0.99  --inst_dismatching                      true
% 3.64/0.99  --inst_eager_unprocessed_to_passive     true
% 3.64/0.99  --inst_prop_sim_given                   true
% 3.64/0.99  --inst_prop_sim_new                     false
% 3.64/0.99  --inst_subs_new                         false
% 3.64/0.99  --inst_eq_res_simp                      false
% 3.64/0.99  --inst_subs_given                       false
% 3.64/0.99  --inst_orphan_elimination               true
% 3.64/0.99  --inst_learning_loop_flag               true
% 3.64/0.99  --inst_learning_start                   3000
% 3.64/0.99  --inst_learning_factor                  2
% 3.64/0.99  --inst_start_prop_sim_after_learn       3
% 3.64/0.99  --inst_sel_renew                        solver
% 3.64/0.99  --inst_lit_activity_flag                true
% 3.64/0.99  --inst_restr_to_given                   false
% 3.64/0.99  --inst_activity_threshold               500
% 3.64/0.99  --inst_out_proof                        true
% 3.64/0.99  
% 3.64/0.99  ------ Resolution Options
% 3.64/0.99  
% 3.64/0.99  --resolution_flag                       false
% 3.64/0.99  --res_lit_sel                           adaptive
% 3.64/0.99  --res_lit_sel_side                      none
% 3.64/0.99  --res_ordering                          kbo
% 3.64/0.99  --res_to_prop_solver                    active
% 3.64/0.99  --res_prop_simpl_new                    false
% 3.64/0.99  --res_prop_simpl_given                  true
% 3.64/0.99  --res_passive_queue_type                priority_queues
% 3.64/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.99  --res_passive_queues_freq               [15;5]
% 3.64/0.99  --res_forward_subs                      full
% 3.64/0.99  --res_backward_subs                     full
% 3.64/0.99  --res_forward_subs_resolution           true
% 3.64/0.99  --res_backward_subs_resolution          true
% 3.64/0.99  --res_orphan_elimination                true
% 3.64/0.99  --res_time_limit                        2.
% 3.64/0.99  --res_out_proof                         true
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Options
% 3.64/0.99  
% 3.64/0.99  --superposition_flag                    true
% 3.64/0.99  --sup_passive_queue_type                priority_queues
% 3.64/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.64/0.99  --demod_completeness_check              fast
% 3.64/0.99  --demod_use_ground                      true
% 3.64/0.99  --sup_to_prop_solver                    passive
% 3.64/0.99  --sup_prop_simpl_new                    true
% 3.64/0.99  --sup_prop_simpl_given                  true
% 3.64/0.99  --sup_fun_splitting                     false
% 3.64/0.99  --sup_smt_interval                      50000
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Simplification Setup
% 3.64/0.99  
% 3.64/0.99  --sup_indices_passive                   []
% 3.64/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_full_bw                           [BwDemod]
% 3.64/0.99  --sup_immed_triv                        [TrivRules]
% 3.64/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_immed_bw_main                     []
% 3.64/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  
% 3.64/0.99  ------ Combination Options
% 3.64/0.99  
% 3.64/0.99  --comb_res_mult                         3
% 3.64/0.99  --comb_sup_mult                         2
% 3.64/0.99  --comb_inst_mult                        10
% 3.64/0.99  
% 3.64/0.99  ------ Debug Options
% 3.64/0.99  
% 3.64/0.99  --dbg_backtrace                         false
% 3.64/0.99  --dbg_dump_prop_clauses                 false
% 3.64/0.99  --dbg_dump_prop_clauses_file            -
% 3.64/0.99  --dbg_out_stat                          false
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS status Theorem for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  fof(f3,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f25,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(nnf_transformation,[],[f3])).
% 3.64/0.99  
% 3.64/0.99  fof(f26,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(flattening,[],[f25])).
% 3.64/0.99  
% 3.64/0.99  fof(f27,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(rectify,[],[f26])).
% 3.64/0.99  
% 3.64/0.99  fof(f28,plain,(
% 3.64/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f29,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 3.64/0.99  
% 3.64/0.99  fof(f47,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f29])).
% 3.64/0.99  
% 3.64/0.99  fof(f10,axiom,(
% 3.64/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f18,plain,(
% 3.64/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f60,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f18])).
% 3.64/0.99  
% 3.64/0.99  fof(f5,axiom,(
% 3.64/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f55,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f5])).
% 3.64/0.99  
% 3.64/0.99  fof(f75,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.64/0.99    inference(definition_unfolding,[],[f60,f55])).
% 3.64/0.99  
% 3.64/0.99  fof(f14,conjecture,(
% 3.64/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f15,negated_conjecture,(
% 3.64/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.64/0.99    inference(negated_conjecture,[],[f14])).
% 3.64/0.99  
% 3.64/0.99  fof(f20,plain,(
% 3.64/0.99    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f15])).
% 3.64/0.99  
% 3.64/0.99  fof(f35,plain,(
% 3.64/0.99    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.64/0.99    inference(nnf_transformation,[],[f20])).
% 3.64/0.99  
% 3.64/0.99  fof(f36,plain,(
% 3.64/0.99    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.64/0.99    inference(flattening,[],[f35])).
% 3.64/0.99  
% 3.64/0.99  fof(f37,plain,(
% 3.64/0.99    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK3) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)) & (k2_subset_1(sK3) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f38,plain,(
% 3.64/0.99    (k2_subset_1(sK3) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)) & (k2_subset_1(sK3) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f37])).
% 3.64/0.99  
% 3.64/0.99  fof(f64,plain,(
% 3.64/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.64/0.99    inference(cnf_transformation,[],[f38])).
% 3.64/0.99  
% 3.64/0.99  fof(f4,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f30,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(nnf_transformation,[],[f4])).
% 3.64/0.99  
% 3.64/0.99  fof(f31,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(flattening,[],[f30])).
% 3.64/0.99  
% 3.64/0.99  fof(f32,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(rectify,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f33,plain,(
% 3.64/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f34,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 3.64/0.99  
% 3.64/0.99  fof(f50,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f34])).
% 3.64/0.99  
% 3.64/0.99  fof(f72,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.64/0.99    inference(definition_unfolding,[],[f50,f55])).
% 3.64/0.99  
% 3.64/0.99  fof(f82,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.64/0.99    inference(equality_resolution,[],[f72])).
% 3.64/0.99  
% 3.64/0.99  fof(f66,plain,(
% 3.64/0.99    k2_subset_1(sK3) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 3.64/0.99    inference(cnf_transformation,[],[f38])).
% 3.64/0.99  
% 3.64/0.99  fof(f12,axiom,(
% 3.64/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f62,plain,(
% 3.64/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f12])).
% 3.64/0.99  
% 3.64/0.99  fof(f8,axiom,(
% 3.64/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f58,plain,(
% 3.64/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f8])).
% 3.64/0.99  
% 3.64/0.99  fof(f67,plain,(
% 3.64/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f62,f58])).
% 3.64/0.99  
% 3.64/0.99  fof(f76,plain,(
% 3.64/0.99    k3_subset_1(sK3,k1_xboole_0) != sK4 | ~r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 3.64/0.99    inference(definition_unfolding,[],[f66,f67])).
% 3.64/0.99  
% 3.64/0.99  fof(f9,axiom,(
% 3.64/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f59,plain,(
% 3.64/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.64/0.99    inference(cnf_transformation,[],[f9])).
% 3.64/0.99  
% 3.64/0.99  fof(f74,plain,(
% 3.64/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.64/0.99    inference(definition_unfolding,[],[f59,f67])).
% 3.64/0.99  
% 3.64/0.99  fof(f1,axiom,(
% 3.64/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f39,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f1])).
% 3.64/0.99  
% 3.64/0.99  fof(f65,plain,(
% 3.64/0.99    k2_subset_1(sK3) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 3.64/0.99    inference(cnf_transformation,[],[f38])).
% 3.64/0.99  
% 3.64/0.99  fof(f77,plain,(
% 3.64/0.99    k3_subset_1(sK3,k1_xboole_0) = sK4 | r1_tarski(k3_subset_1(sK3,sK4),sK4)),
% 3.64/0.99    inference(definition_unfolding,[],[f65,f67])).
% 3.64/0.99  
% 3.64/0.99  fof(f6,axiom,(
% 3.64/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f17,plain,(
% 3.64/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.64/0.99    inference(ennf_transformation,[],[f6])).
% 3.64/0.99  
% 3.64/0.99  fof(f56,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f17])).
% 3.64/0.99  
% 3.64/0.99  fof(f43,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f29])).
% 3.64/0.99  
% 3.64/0.99  fof(f80,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.64/0.99    inference(equality_resolution,[],[f43])).
% 3.64/0.99  
% 3.64/0.99  fof(f2,axiom,(
% 3.64/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f16,plain,(
% 3.64/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f2])).
% 3.64/0.99  
% 3.64/0.99  fof(f21,plain,(
% 3.64/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.64/0.99    inference(nnf_transformation,[],[f16])).
% 3.64/0.99  
% 3.64/0.99  fof(f22,plain,(
% 3.64/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.64/0.99    inference(rectify,[],[f21])).
% 3.64/0.99  
% 3.64/0.99  fof(f23,plain,(
% 3.64/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f24,plain,(
% 3.64/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.64/0.99  
% 3.64/0.99  fof(f41,plain,(
% 3.64/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f24])).
% 3.64/0.99  
% 3.64/0.99  fof(f42,plain,(
% 3.64/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f24])).
% 3.64/0.99  
% 3.64/0.99  fof(f49,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f34])).
% 3.64/0.99  
% 3.64/0.99  fof(f73,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.64/0.99    inference(definition_unfolding,[],[f49,f55])).
% 3.64/0.99  
% 3.64/0.99  fof(f83,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.64/0.99    inference(equality_resolution,[],[f73])).
% 3.64/0.99  
% 3.64/0.99  fof(f40,plain,(
% 3.64/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f24])).
% 3.64/0.99  
% 3.64/0.99  fof(f7,axiom,(
% 3.64/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f57,plain,(
% 3.64/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f7])).
% 3.64/0.99  
% 3.64/0.99  fof(f51,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f34])).
% 3.64/0.99  
% 3.64/0.99  fof(f71,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.64/0.99    inference(definition_unfolding,[],[f51,f55])).
% 3.64/0.99  
% 3.64/0.99  fof(f81,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.64/0.99    inference(equality_resolution,[],[f71])).
% 3.64/0.99  
% 3.64/0.99  fof(f11,axiom,(
% 3.64/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f19,plain,(
% 3.64/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f11])).
% 3.64/0.99  
% 3.64/0.99  fof(f61,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f19])).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5,plain,
% 3.64/0.99      ( r2_hidden(sK1(X0,X1,X2),X1)
% 3.64/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.64/0.99      | k3_xboole_0(X0,X1) = X2 ),
% 3.64/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_958,plain,
% 3.64/0.99      ( k3_xboole_0(X0,X1) = X2
% 3.64/0.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 3.64/0.99      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_19,plain,
% 3.64/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.64/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_24,negated_conjecture,
% 3.64/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_334,plain,
% 3.64/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.64/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 3.64/0.99      | sK4 != X1 ),
% 3.64/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_335,plain,
% 3.64/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
% 3.64/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 3.64/0.99      inference(unflattening,[status(thm)],[c_334]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1135,plain,
% 3.64/0.99      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
% 3.64/0.99      inference(equality_resolution,[status(thm)],[c_335]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_14,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,X1)
% 3.64/0.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.64/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_949,plain,
% 3.64/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.64/0.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2632,plain,
% 3.64/0.99      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
% 3.64/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1135,c_949]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_494,plain,( X0 = X0 ),theory(equality) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_508,plain,
% 3.64/0.99      ( sK4 = sK4 ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_494]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_22,negated_conjecture,
% 3.64/0.99      ( ~ r1_tarski(k3_subset_1(sK3,sK4),sK4)
% 3.64/0.99      | k3_subset_1(sK3,k1_xboole_0) != sK4 ),
% 3.64/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_945,plain,
% 3.64/0.99      ( k3_subset_1(sK3,k1_xboole_0) != sK4
% 3.64/0.99      | r1_tarski(k3_subset_1(sK3,sK4),sK4) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_18,plain,
% 3.64/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.64/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1003,plain,
% 3.64/0.99      ( sK4 != sK3 | r1_tarski(k3_subset_1(sK3,sK4),sK4) != iProver_top ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_945,c_18]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1087,plain,
% 3.64/0.99      ( ~ r1_tarski(k3_subset_1(sK3,sK4),sK4) | sK4 != sK3 ),
% 3.64/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1003]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1222,plain,
% 3.64/0.99      ( sK3 = sK3 ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_494]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_495,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1224,plain,
% 3.64/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_495]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1254,plain,
% 3.64/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_1224]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1255,plain,
% 3.64/0.99      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_1254]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_0,plain,
% 3.64/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_23,negated_conjecture,
% 3.64/0.99      ( r1_tarski(k3_subset_1(sK3,sK4),sK4)
% 3.64/0.99      | k3_subset_1(sK3,k1_xboole_0) = sK4 ),
% 3.64/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_944,plain,
% 3.64/0.99      ( k3_subset_1(sK3,k1_xboole_0) = sK4
% 3.64/0.99      | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_973,plain,
% 3.64/0.99      ( sK4 = sK3 | r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_944,c_18]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_16,plain,
% 3.64/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.64/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_947,plain,
% 3.64/0.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1235,plain,
% 3.64/0.99      ( k3_xboole_0(k3_subset_1(sK3,sK4),sK4) = k3_subset_1(sK3,sK4)
% 3.64/0.99      | sK4 = sK3 ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_973,c_947]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1469,plain,
% 3.64/0.99      ( k3_xboole_0(sK4,k3_subset_1(sK3,sK4)) = k3_subset_1(sK3,sK4)
% 3.64/0.99      | sK4 = sK3 ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_0,c_1235]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_9,plain,
% 3.64/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_954,plain,
% 3.64/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.64/0.99      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1547,plain,
% 3.64/0.99      ( sK4 = sK3
% 3.64/0.99      | r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
% 3.64/0.99      | r2_hidden(X0,sK4) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1469,c_954]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2,plain,
% 3.64/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.64/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_961,plain,
% 3.64/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.64/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.64/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_962,plain,
% 3.64/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.64/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1853,plain,
% 3.64/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_961,c_962]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1857,plain,
% 3.64/0.99      ( r1_tarski(X0,X0) ),
% 3.64/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1853]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1859,plain,
% 3.64/0.99      ( r1_tarski(sK4,sK4) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_1857]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_497,plain,
% 3.64/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.64/0.99      theory(equality) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1976,plain,
% 3.64/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_497]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1978,plain,
% 3.64/0.99      ( ~ r1_tarski(sK4,sK4)
% 3.64/0.99      | r1_tarski(sK3,sK4)
% 3.64/0.99      | sK4 != sK4
% 3.64/0.99      | sK3 != sK4 ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_1976]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_15,plain,
% 3.64/0.99      ( r2_hidden(X0,X1)
% 3.64/0.99      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.64/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_948,plain,
% 3.64/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.64/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1911,plain,
% 3.64/0.99      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top
% 3.64/0.99      | r2_hidden(X0,sK3) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1135,c_948]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2021,plain,
% 3.64/0.99      ( r2_hidden(sK0(k3_subset_1(sK3,sK4),X0),sK3) = iProver_top
% 3.64/0.99      | r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_961,c_1911]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_960,plain,
% 3.64/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.64/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.64/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2029,plain,
% 3.64/0.99      ( r2_hidden(sK0(k3_subset_1(sK3,sK4),X0),X1) = iProver_top
% 3.64/0.99      | r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top
% 3.64/0.99      | r1_tarski(sK3,X1) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_2021,c_960]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2256,plain,
% 3.64/0.99      ( r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top
% 3.64/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_2029,c_962]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2311,plain,
% 3.64/0.99      ( r1_tarski(k3_subset_1(sK3,sK4),X0) | ~ r1_tarski(sK3,X0) ),
% 3.64/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2256]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2313,plain,
% 3.64/0.99      ( r1_tarski(k3_subset_1(sK3,sK4),sK4) | ~ r1_tarski(sK3,sK4) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_2311]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2947,plain,
% 3.64/0.99      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) != iProver_top ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_2632,c_508,c_1087,c_1222,c_1255,c_1547,c_1859,c_1978,
% 3.64/0.99                 c_2313]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4708,plain,
% 3.64/0.99      ( k3_xboole_0(X0,k3_subset_1(sK3,sK4)) = X1
% 3.64/0.99      | r2_hidden(sK1(X0,k3_subset_1(sK3,sK4),X1),X1) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_958,c_2947]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5708,plain,
% 3.64/0.99      ( k3_xboole_0(X0,k3_subset_1(sK3,sK4)) = k3_subset_1(sK3,sK4) ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_4708,c_2947]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_17,plain,
% 3.64/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_946,plain,
% 3.64/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1234,plain,
% 3.64/0.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_946,c_947]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6066,plain,
% 3.64/0.99      ( k3_subset_1(sK3,sK4) = k1_xboole_0 ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_5708,c_1234]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_13,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,X1)
% 3.64/0.99      | r2_hidden(X0,X2)
% 3.64/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.64/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_950,plain,
% 3.64/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.64/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.64/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3419,plain,
% 3.64/0.99      ( r2_hidden(X0,k3_subset_1(sK3,sK4)) = iProver_top
% 3.64/0.99      | r2_hidden(X0,sK4) = iProver_top
% 3.64/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1135,c_950]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3714,plain,
% 3.64/0.99      ( r2_hidden(X0,sK4) = iProver_top
% 3.64/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_3419,c_508,c_1087,c_1222,c_1255,c_1547,c_1859,c_1978,
% 3.64/0.99                 c_2313,c_2632]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3722,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK3,X0),sK4) = iProver_top
% 3.64/0.99      | r1_tarski(sK3,X0) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_961,c_3714]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3877,plain,
% 3.64/0.99      ( r1_tarski(sK3,sK4) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_3722,c_962]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4159,plain,
% 3.64/0.99      ( k3_xboole_0(sK3,sK4) = sK3 ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_3877,c_947]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7817,plain,
% 3.64/0.99      ( k3_subset_1(sK3,sK4) = k5_xboole_0(sK3,sK3) ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_4159,c_1135]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_13673,plain,
% 3.64/0.99      ( k5_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_6066,c_7817]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_20,plain,
% 3.64/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.64/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.64/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_325,plain,
% 3.64/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.64/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 3.64/0.99      | sK4 != X1 ),
% 3.64/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_326,plain,
% 3.64/0.99      ( k3_subset_1(X0,k3_subset_1(X0,sK4)) = sK4
% 3.64/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 3.64/0.99      inference(unflattening,[status(thm)],[c_325]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1132,plain,
% 3.64/0.99      ( k3_subset_1(sK3,k3_subset_1(sK3,sK4)) = sK4 ),
% 3.64/0.99      inference(equality_resolution,[status(thm)],[c_326]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_8093,plain,
% 3.64/0.99      ( k3_subset_1(sK3,k5_xboole_0(sK3,sK3)) = sK4 ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_7817,c_1132]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_13694,plain,
% 3.64/0.99      ( k3_subset_1(sK3,k1_xboole_0) = sK4 ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_13673,c_8093]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_13696,plain,
% 3.64/0.99      ( sK4 = sK3 ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_13694,c_18]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2954,plain,
% 3.64/0.99      ( r1_tarski(k3_subset_1(sK3,sK4),X0) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_961,c_2947]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2970,plain,
% 3.64/0.99      ( r1_tarski(k3_subset_1(sK3,sK4),sK4) = iProver_top ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_2954]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(contradiction,plain,
% 3.64/0.99      ( $false ),
% 3.64/0.99      inference(minisat,[status(thm)],[c_13696,c_2970,c_1003]) ).
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  ------                               Statistics
% 3.64/0.99  
% 3.64/0.99  ------ General
% 3.64/0.99  
% 3.64/0.99  abstr_ref_over_cycles:                  0
% 3.64/0.99  abstr_ref_under_cycles:                 0
% 3.64/0.99  gc_basic_clause_elim:                   0
% 3.64/0.99  forced_gc_time:                         0
% 3.64/0.99  parsing_time:                           0.008
% 3.64/0.99  unif_index_cands_time:                  0.
% 3.64/0.99  unif_index_add_time:                    0.
% 3.64/0.99  orderings_time:                         0.
% 3.64/0.99  out_proof_time:                         0.009
% 3.64/0.99  total_time:                             0.36
% 3.64/0.99  num_of_symbols:                         44
% 3.64/0.99  num_of_terms:                           13546
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing
% 3.64/0.99  
% 3.64/0.99  num_of_splits:                          0
% 3.64/0.99  num_of_split_atoms:                     0
% 3.64/0.99  num_of_reused_defs:                     0
% 3.64/0.99  num_eq_ax_congr_red:                    21
% 3.64/0.99  num_of_sem_filtered_clauses:            1
% 3.64/0.99  num_of_subtypes:                        0
% 3.64/0.99  monotx_restored_types:                  0
% 3.64/0.99  sat_num_of_epr_types:                   0
% 3.64/0.99  sat_num_of_non_cyclic_types:            0
% 3.64/0.99  sat_guarded_non_collapsed_types:        0
% 3.64/0.99  num_pure_diseq_elim:                    0
% 3.64/0.99  simp_replaced_by:                       0
% 3.64/0.99  res_preprocessed:                       92
% 3.64/0.99  prep_upred:                             0
% 3.64/0.99  prep_unflattend:                        21
% 3.64/0.99  smt_new_axioms:                         0
% 3.64/0.99  pred_elim_cands:                        3
% 3.64/0.99  pred_elim:                              1
% 3.64/0.99  pred_elim_cl:                           0
% 3.64/0.99  pred_elim_cycles:                       2
% 3.64/0.99  merged_defs:                            6
% 3.64/0.99  merged_defs_ncl:                        0
% 3.64/0.99  bin_hyper_res:                          6
% 3.64/0.99  prep_cycles:                            3
% 3.64/0.99  pred_elim_time:                         0.002
% 3.64/0.99  splitting_time:                         0.
% 3.64/0.99  sem_filter_time:                        0.
% 3.64/0.99  monotx_time:                            0.001
% 3.64/0.99  subtype_inf_time:                       0.
% 3.64/0.99  
% 3.64/0.99  ------ Problem properties
% 3.64/0.99  
% 3.64/0.99  clauses:                                25
% 3.64/0.99  conjectures:                            2
% 3.64/0.99  epr:                                    2
% 3.64/0.99  horn:                                   17
% 3.64/0.99  ground:                                 2
% 3.64/0.99  unary:                                  3
% 3.64/0.99  binary:                                 13
% 3.64/0.99  lits:                                   58
% 3.64/0.99  lits_eq:                                19
% 3.64/0.99  fd_pure:                                0
% 3.64/0.99  fd_pseudo:                              0
% 3.64/0.99  fd_cond:                                0
% 3.64/0.99  fd_pseudo_cond:                         6
% 3.64/0.99  ac_symbols:                             0
% 3.64/0.99  
% 3.64/0.99  ------ Propositional Solver
% 3.64/0.99  
% 3.64/0.99  prop_solver_calls:                      26
% 3.64/0.99  prop_fast_solver_calls:                 741
% 3.64/0.99  smt_solver_calls:                       0
% 3.64/0.99  smt_fast_solver_calls:                  0
% 3.64/0.99  prop_num_of_clauses:                    4865
% 3.64/0.99  prop_preprocess_simplified:             9575
% 3.64/0.99  prop_fo_subsumed:                       12
% 3.64/0.99  prop_solver_time:                       0.
% 3.64/0.99  smt_solver_time:                        0.
% 3.64/0.99  smt_fast_solver_time:                   0.
% 3.64/0.99  prop_fast_solver_time:                  0.
% 3.64/0.99  prop_unsat_core_time:                   0.
% 3.64/0.99  
% 3.64/0.99  ------ QBF
% 3.64/0.99  
% 3.64/0.99  qbf_q_res:                              0
% 3.64/0.99  qbf_num_tautologies:                    0
% 3.64/0.99  qbf_prep_cycles:                        0
% 3.64/0.99  
% 3.64/0.99  ------ BMC1
% 3.64/0.99  
% 3.64/0.99  bmc1_current_bound:                     -1
% 3.64/0.99  bmc1_last_solved_bound:                 -1
% 3.64/0.99  bmc1_unsat_core_size:                   -1
% 3.64/0.99  bmc1_unsat_core_parents_size:           -1
% 3.64/0.99  bmc1_merge_next_fun:                    0
% 3.64/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.64/0.99  
% 3.64/0.99  ------ Instantiation
% 3.64/0.99  
% 3.64/0.99  inst_num_of_clauses:                    1325
% 3.64/0.99  inst_num_in_passive:                    654
% 3.64/0.99  inst_num_in_active:                     489
% 3.64/0.99  inst_num_in_unprocessed:                182
% 3.64/0.99  inst_num_of_loops:                      660
% 3.64/0.99  inst_num_of_learning_restarts:          0
% 3.64/0.99  inst_num_moves_active_passive:          167
% 3.64/0.99  inst_lit_activity:                      0
% 3.64/0.99  inst_lit_activity_moves:                0
% 3.64/0.99  inst_num_tautologies:                   0
% 3.64/0.99  inst_num_prop_implied:                  0
% 3.64/0.99  inst_num_existing_simplified:           0
% 3.64/0.99  inst_num_eq_res_simplified:             0
% 3.64/0.99  inst_num_child_elim:                    0
% 3.64/0.99  inst_num_of_dismatching_blockings:      704
% 3.64/0.99  inst_num_of_non_proper_insts:           1224
% 3.64/0.99  inst_num_of_duplicates:                 0
% 3.64/0.99  inst_inst_num_from_inst_to_res:         0
% 3.64/0.99  inst_dismatching_checking_time:         0.
% 3.64/0.99  
% 3.64/0.99  ------ Resolution
% 3.64/0.99  
% 3.64/0.99  res_num_of_clauses:                     0
% 3.64/0.99  res_num_in_passive:                     0
% 3.64/0.99  res_num_in_active:                      0
% 3.64/0.99  res_num_of_loops:                       95
% 3.64/0.99  res_forward_subset_subsumed:            139
% 3.64/0.99  res_backward_subset_subsumed:           0
% 3.64/0.99  res_forward_subsumed:                   0
% 3.64/0.99  res_backward_subsumed:                  0
% 3.64/0.99  res_forward_subsumption_resolution:     0
% 3.64/0.99  res_backward_subsumption_resolution:    0
% 3.64/0.99  res_clause_to_clause_subsumption:       3571
% 3.64/0.99  res_orphan_elimination:                 0
% 3.64/0.99  res_tautology_del:                      162
% 3.64/0.99  res_num_eq_res_simplified:              0
% 3.64/0.99  res_num_sel_changes:                    0
% 3.64/0.99  res_moves_from_active_to_pass:          0
% 3.64/0.99  
% 3.64/0.99  ------ Superposition
% 3.64/0.99  
% 3.64/0.99  sup_time_total:                         0.
% 3.64/0.99  sup_time_generating:                    0.
% 3.64/0.99  sup_time_sim_full:                      0.
% 3.64/0.99  sup_time_sim_immed:                     0.
% 3.64/0.99  
% 3.64/0.99  sup_num_of_clauses:                     517
% 3.64/0.99  sup_num_in_active:                      71
% 3.64/0.99  sup_num_in_passive:                     446
% 3.64/0.99  sup_num_of_loops:                       131
% 3.64/0.99  sup_fw_superposition:                   325
% 3.64/0.99  sup_bw_superposition:                   758
% 3.64/0.99  sup_immediate_simplified:               250
% 3.64/0.99  sup_given_eliminated:                   2
% 3.64/0.99  comparisons_done:                       0
% 3.64/0.99  comparisons_avoided:                    6
% 3.64/0.99  
% 3.64/0.99  ------ Simplifications
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  sim_fw_subset_subsumed:                 37
% 3.64/0.99  sim_bw_subset_subsumed:                 42
% 3.64/0.99  sim_fw_subsumed:                        65
% 3.64/0.99  sim_bw_subsumed:                        24
% 3.64/0.99  sim_fw_subsumption_res:                 6
% 3.64/0.99  sim_bw_subsumption_res:                 5
% 3.64/0.99  sim_tautology_del:                      58
% 3.64/0.99  sim_eq_tautology_del:                   10
% 3.64/0.99  sim_eq_res_simp:                        9
% 3.64/0.99  sim_fw_demodulated:                     45
% 3.64/0.99  sim_bw_demodulated:                     63
% 3.64/0.99  sim_light_normalised:                   85
% 3.64/0.99  sim_joinable_taut:                      0
% 3.64/0.99  sim_joinable_simp:                      0
% 3.64/0.99  sim_ac_normalised:                      0
% 3.64/0.99  sim_smt_subsumption:                    0
% 3.64/0.99  
%------------------------------------------------------------------------------
