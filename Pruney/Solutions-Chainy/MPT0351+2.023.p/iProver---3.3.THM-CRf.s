%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:22 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 252 expanded)
%              Number of clauses        :   63 (  88 expanded)
%              Number of leaves         :   18 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  396 ( 953 expanded)
%              Number of equality atoms :  154 ( 308 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f33])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f14])).

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

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f60,plain,(
    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1003,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_988,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_991,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1015,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_991,c_18])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k1_enumset1(X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_989,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1544,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X1,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_989])).

cnf(c_4726,plain,
    ( k3_tarski(k1_enumset1(sK4,sK4,sK3)) = k4_subset_1(sK3,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_988,c_1544])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1000,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5602,plain,
    ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4726,c_1000])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1370,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(resolution,[status(thm)],[c_17,c_23])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1196,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
    | r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1373,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1370,c_23,c_29,c_1196])).

cnf(c_1577,plain,
    ( r1_tarski(sK4,sK3) ),
    inference(resolution,[status(thm)],[c_13,c_1373])).

cnf(c_2263,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_2,c_1577])).

cnf(c_2264,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2263])).

cnf(c_6383,plain,
    ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5602,c_2264])).

cnf(c_6393,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(sK3,sK4,sK3)
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_6383])).

cnf(c_6439,plain,
    ( k3_tarski(k1_enumset1(sK3,sK3,sK3)) = k4_subset_1(sK3,sK4,sK3)
    | r2_hidden(sK1(sK3,sK3,k4_subset_1(sK3,sK4,sK3)),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6393])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1002,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5603,plain,
    ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4726,c_1002])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1004,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5931,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(sK3,sK4,sK3)
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5603,c_1004])).

cnf(c_5978,plain,
    ( k3_tarski(k1_enumset1(sK3,sK3,sK3)) = k4_subset_1(sK3,sK4,sK3)
    | r2_hidden(sK1(sK3,sK3,k4_subset_1(sK3,sK4,sK3)),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5931])).

cnf(c_461,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_460,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2245,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_461,c_460])).

cnf(c_5437,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | X2 = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[status(thm)],[c_2245,c_5])).

cnf(c_5439,plain,
    ( r2_hidden(sK1(sK3,sK3,sK3),sK3)
    | sK3 = k3_tarski(k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_5437])).

cnf(c_1283,plain,
    ( X0 != X1
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != X1
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_2100,plain,
    ( X0 != k4_subset_1(X1,sK4,X2)
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(X1,sK4,X2) ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_3783,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(X0,sK4,X1)
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k3_tarski(k1_enumset1(X2,X2,X3))
    | k3_tarski(k1_enumset1(X2,X2,X3)) != k4_subset_1(X0,sK4,X1) ),
    inference(instantiation,[status(thm)],[c_2100])).

cnf(c_3787,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(sK3,sK4,sK3)
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k3_tarski(k1_enumset1(sK3,sK3,sK3))
    | k3_tarski(k1_enumset1(sK3,sK3,sK3)) != k4_subset_1(sK3,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_3783])).

cnf(c_3110,plain,
    ( k2_subset_1(sK3) != X0
    | k2_subset_1(sK3) = k3_tarski(k1_enumset1(X1,X1,X2))
    | k3_tarski(k1_enumset1(X1,X1,X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_3111,plain,
    ( k2_subset_1(sK3) = k3_tarski(k1_enumset1(sK3,sK3,sK3))
    | k2_subset_1(sK3) != sK3
    | k3_tarski(k1_enumset1(sK3,sK3,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_3110])).

cnf(c_2870,plain,
    ( X0 != k3_tarski(k1_enumset1(X1,X1,X2))
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_2871,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k1_enumset1(sK3,sK3,sK3))
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = sK3
    | sK3 != k3_tarski(k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_2870])).

cnf(c_1199,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != X0
    | k2_subset_1(sK3) != X0
    | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_2867,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k1_enumset1(X0,X0,X1))
    | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    | k2_subset_1(sK3) != k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_2868,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k1_enumset1(sK3,sK3,sK3))
    | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    | k2_subset_1(sK3) != k3_tarski(k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_2867])).

cnf(c_469,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_1285,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(X0,X1,X2)
    | k2_subset_1(sK3) != X2
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_1597,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(X0,sK4,X1)
    | k2_subset_1(sK3) != X1
    | sK4 != sK4
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_1598,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(sK3,sK4,sK3)
    | k2_subset_1(sK3) != sK3
    | sK4 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_1328,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1200,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != sK3
    | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    | k2_subset_1(sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_479,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_69,plain,
    ( ~ r2_hidden(sK1(sK3,sK3,sK3),sK3)
    | k3_tarski(k1_enumset1(sK3,sK3,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_34,plain,
    ( k2_subset_1(sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_22,negated_conjecture,
    ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6439,c_5978,c_5439,c_3787,c_3111,c_2871,c_2868,c_1598,c_1328,c_1200,c_479,c_69,c_34,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:24:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.60/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/0.98  
% 3.60/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/0.98  
% 3.60/0.98  ------  iProver source info
% 3.60/0.98  
% 3.60/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.60/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/0.98  git: non_committed_changes: false
% 3.60/0.98  git: last_make_outside_of_git: false
% 3.60/0.98  
% 3.60/0.98  ------ 
% 3.60/0.98  ------ Parsing...
% 3.60/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/0.98  
% 3.60/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.60/0.98  
% 3.60/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/0.98  
% 3.60/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/0.98  ------ Proving...
% 3.60/0.98  ------ Problem Properties 
% 3.60/0.98  
% 3.60/0.98  
% 3.60/0.98  clauses                                 24
% 3.60/0.98  conjectures                             2
% 3.60/0.98  EPR                                     5
% 3.60/0.98  Horn                                    18
% 3.60/0.98  unary                                   6
% 3.60/0.98  binary                                  6
% 3.60/0.98  lits                                    55
% 3.60/0.98  lits eq                                 9
% 3.60/0.98  fd_pure                                 0
% 3.60/0.98  fd_pseudo                               0
% 3.60/0.98  fd_cond                                 0
% 3.60/0.98  fd_pseudo_cond                          5
% 3.60/0.98  AC symbols                              0
% 3.60/0.98  
% 3.60/0.98  ------ Input Options Time Limit: Unbounded
% 3.60/0.98  
% 3.60/0.98  
% 3.60/0.98  ------ 
% 3.60/0.98  Current options:
% 3.60/0.98  ------ 
% 3.60/0.98  
% 3.60/0.98  
% 3.60/0.98  
% 3.60/0.98  
% 3.60/0.98  ------ Proving...
% 3.60/0.98  
% 3.60/0.98  
% 3.60/0.98  % SZS status Theorem for theBenchmark.p
% 3.60/0.98  
% 3.60/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/0.98  
% 3.60/0.98  fof(f2,axiom,(
% 3.60/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f23,plain,(
% 3.60/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.60/0.98    inference(nnf_transformation,[],[f2])).
% 3.60/0.98  
% 3.60/0.98  fof(f24,plain,(
% 3.60/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.60/0.98    inference(flattening,[],[f23])).
% 3.60/0.98  
% 3.60/0.98  fof(f25,plain,(
% 3.60/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.60/0.98    inference(rectify,[],[f24])).
% 3.60/0.98  
% 3.60/0.98  fof(f26,plain,(
% 3.60/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.60/0.98    introduced(choice_axiom,[])).
% 3.60/0.98  
% 3.60/0.98  fof(f27,plain,(
% 3.60/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.60/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 3.60/0.98  
% 3.60/0.98  fof(f41,plain,(
% 3.60/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.60/0.98    inference(cnf_transformation,[],[f27])).
% 3.60/0.98  
% 3.60/0.98  fof(f6,axiom,(
% 3.60/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f50,plain,(
% 3.60/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.60/0.98    inference(cnf_transformation,[],[f6])).
% 3.60/0.98  
% 3.60/0.98  fof(f4,axiom,(
% 3.60/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f45,plain,(
% 3.60/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.60/0.98    inference(cnf_transformation,[],[f4])).
% 3.60/0.98  
% 3.60/0.98  fof(f61,plain,(
% 3.60/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.60/0.98    inference(definition_unfolding,[],[f50,f45])).
% 3.60/0.98  
% 3.60/0.98  fof(f64,plain,(
% 3.60/0.98    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.60/0.98    inference(definition_unfolding,[],[f41,f61])).
% 3.60/0.98  
% 3.60/0.98  fof(f12,conjecture,(
% 3.60/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f13,negated_conjecture,(
% 3.60/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 3.60/0.98    inference(negated_conjecture,[],[f12])).
% 3.60/0.98  
% 3.60/0.98  fof(f18,plain,(
% 3.60/0.98    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.60/0.98    inference(ennf_transformation,[],[f13])).
% 3.60/0.98  
% 3.60/0.98  fof(f33,plain,(
% 3.60/0.98    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 3.60/0.98    introduced(choice_axiom,[])).
% 3.60/0.98  
% 3.60/0.98  fof(f34,plain,(
% 3.60/0.98    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.60/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f33])).
% 3.60/0.98  
% 3.60/0.98  fof(f59,plain,(
% 3.60/0.98    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.60/0.98    inference(cnf_transformation,[],[f34])).
% 3.60/0.98  
% 3.60/0.98  fof(f9,axiom,(
% 3.60/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f56,plain,(
% 3.60/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.60/0.98    inference(cnf_transformation,[],[f9])).
% 3.60/0.98  
% 3.60/0.98  fof(f8,axiom,(
% 3.60/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f55,plain,(
% 3.60/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.60/0.98    inference(cnf_transformation,[],[f8])).
% 3.60/0.98  
% 3.60/0.98  fof(f11,axiom,(
% 3.60/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f16,plain,(
% 3.60/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.60/0.98    inference(ennf_transformation,[],[f11])).
% 3.60/0.98  
% 3.60/0.98  fof(f17,plain,(
% 3.60/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.60/0.98    inference(flattening,[],[f16])).
% 3.60/0.98  
% 3.60/0.98  fof(f58,plain,(
% 3.60/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.60/0.98    inference(cnf_transformation,[],[f17])).
% 3.60/0.98  
% 3.60/0.98  fof(f69,plain,(
% 3.60/0.98    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.60/0.98    inference(definition_unfolding,[],[f58,f61])).
% 3.60/0.98  
% 3.60/0.98  fof(f38,plain,(
% 3.60/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.60/0.98    inference(cnf_transformation,[],[f27])).
% 3.60/0.98  
% 3.60/0.98  fof(f67,plain,(
% 3.60/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 3.60/0.98    inference(definition_unfolding,[],[f38,f61])).
% 3.60/0.98  
% 3.60/0.98  fof(f72,plain,(
% 3.60/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 3.60/0.98    inference(equality_resolution,[],[f67])).
% 3.60/0.98  
% 3.60/0.98  fof(f1,axiom,(
% 3.60/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f14,plain,(
% 3.60/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.60/0.98    inference(ennf_transformation,[],[f1])).
% 3.60/0.98  
% 3.60/0.98  fof(f19,plain,(
% 3.60/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.60/0.98    inference(nnf_transformation,[],[f14])).
% 3.60/0.98  
% 3.60/0.98  fof(f20,plain,(
% 3.60/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.60/0.98    inference(rectify,[],[f19])).
% 3.60/0.98  
% 3.60/0.98  fof(f21,plain,(
% 3.60/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.60/0.98    introduced(choice_axiom,[])).
% 3.60/0.98  
% 3.60/0.98  fof(f22,plain,(
% 3.60/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.60/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.60/0.98  
% 3.60/0.98  fof(f35,plain,(
% 3.60/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.60/0.98    inference(cnf_transformation,[],[f22])).
% 3.60/0.98  
% 3.60/0.98  fof(f5,axiom,(
% 3.60/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f28,plain,(
% 3.60/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.60/0.98    inference(nnf_transformation,[],[f5])).
% 3.60/0.98  
% 3.60/0.98  fof(f29,plain,(
% 3.60/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.60/0.98    inference(rectify,[],[f28])).
% 3.60/0.98  
% 3.60/0.98  fof(f30,plain,(
% 3.60/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.60/0.98    introduced(choice_axiom,[])).
% 3.60/0.98  
% 3.60/0.98  fof(f31,plain,(
% 3.60/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.60/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 3.60/0.98  
% 3.60/0.98  fof(f46,plain,(
% 3.60/0.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.60/0.98    inference(cnf_transformation,[],[f31])).
% 3.60/0.98  
% 3.60/0.98  fof(f74,plain,(
% 3.60/0.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.60/0.98    inference(equality_resolution,[],[f46])).
% 3.60/0.98  
% 3.60/0.98  fof(f7,axiom,(
% 3.60/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f15,plain,(
% 3.60/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.60/0.98    inference(ennf_transformation,[],[f7])).
% 3.60/0.98  
% 3.60/0.98  fof(f32,plain,(
% 3.60/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.60/0.98    inference(nnf_transformation,[],[f15])).
% 3.60/0.98  
% 3.60/0.98  fof(f51,plain,(
% 3.60/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.60/0.98    inference(cnf_transformation,[],[f32])).
% 3.60/0.98  
% 3.60/0.98  fof(f10,axiom,(
% 3.60/0.98    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.98  
% 3.60/0.98  fof(f57,plain,(
% 3.60/0.98    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.60/0.98    inference(cnf_transformation,[],[f10])).
% 3.60/0.98  
% 3.60/0.98  fof(f40,plain,(
% 3.60/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.60/0.98    inference(cnf_transformation,[],[f27])).
% 3.60/0.98  
% 3.60/0.98  fof(f65,plain,(
% 3.60/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 3.60/0.98    inference(definition_unfolding,[],[f40,f61])).
% 3.60/0.98  
% 3.60/0.98  fof(f70,plain,(
% 3.60/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.60/0.98    inference(equality_resolution,[],[f65])).
% 3.60/0.98  
% 3.60/0.98  fof(f42,plain,(
% 3.60/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.60/0.98    inference(cnf_transformation,[],[f27])).
% 3.60/0.98  
% 3.60/0.98  fof(f63,plain,(
% 3.60/0.98    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X2 | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.60/0.98    inference(definition_unfolding,[],[f42,f61])).
% 3.60/0.98  
% 3.60/0.98  fof(f60,plain,(
% 3.60/0.98    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))),
% 3.60/0.98    inference(cnf_transformation,[],[f34])).
% 3.60/0.98  
% 3.60/0.98  cnf(c_5,plain,
% 3.60/0.98      ( r2_hidden(sK1(X0,X1,X2),X1)
% 3.60/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.60/0.98      | r2_hidden(sK1(X0,X1,X2),X0)
% 3.60/0.98      | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
% 3.60/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1003,plain,
% 3.60/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 3.60/0.98      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
% 3.60/0.98      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 3.60/0.98      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top ),
% 3.60/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_23,negated_conjecture,
% 3.60/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 3.60/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_988,plain,
% 3.60/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.60/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_19,plain,
% 3.60/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.60/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_991,plain,
% 3.60/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.60/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_18,plain,
% 3.60/0.98      ( k2_subset_1(X0) = X0 ),
% 3.60/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1015,plain,
% 3.60/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.60/0.98      inference(light_normalisation,[status(thm)],[c_991,c_18]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_21,plain,
% 3.60/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.60/0.98      | k3_tarski(k1_enumset1(X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 3.60/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_989,plain,
% 3.60/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.60/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.60/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1544,plain,
% 3.60/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X1,X0,X1)
% 3.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.60/0.98      inference(superposition,[status(thm)],[c_1015,c_989]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_4726,plain,
% 3.60/0.98      ( k3_tarski(k1_enumset1(sK4,sK4,sK3)) = k4_subset_1(sK3,sK4,sK3) ),
% 3.60/0.98      inference(superposition,[status(thm)],[c_988,c_1544]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_8,plain,
% 3.60/0.98      ( r2_hidden(X0,X1)
% 3.60/0.98      | r2_hidden(X0,X2)
% 3.60/0.98      | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 3.60/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1000,plain,
% 3.60/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.60/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.60/0.98      | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) != iProver_top ),
% 3.60/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_5602,plain,
% 3.60/0.98      ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) != iProver_top
% 3.60/0.98      | r2_hidden(X0,sK4) = iProver_top
% 3.60/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 3.60/0.98      inference(superposition,[status(thm)],[c_4726,c_1000]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_2,plain,
% 3.60/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.60/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_13,plain,
% 3.60/0.98      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.60/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_17,plain,
% 3.60/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.60/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1370,plain,
% 3.60/0.98      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 3.60/0.98      inference(resolution,[status(thm)],[c_17,c_23]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_20,plain,
% 3.60/0.98      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.60/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_29,plain,
% 3.60/0.98      ( ~ v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1196,plain,
% 3.60/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
% 3.60/0.98      | r2_hidden(sK4,k1_zfmisc_1(sK3))
% 3.60/0.98      | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1373,plain,
% 3.60/0.98      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
% 3.60/0.98      inference(global_propositional_subsumption,
% 3.60/0.98                [status(thm)],
% 3.60/0.98                [c_1370,c_23,c_29,c_1196]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1577,plain,
% 3.60/0.98      ( r1_tarski(sK4,sK3) ),
% 3.60/0.98      inference(resolution,[status(thm)],[c_13,c_1373]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_2263,plain,
% 3.60/0.98      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,sK3) ),
% 3.60/0.98      inference(resolution,[status(thm)],[c_2,c_1577]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_2264,plain,
% 3.60/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 3.60/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 3.60/0.98      inference(predicate_to_equality,[status(thm)],[c_2263]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_6383,plain,
% 3.60/0.98      ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) != iProver_top
% 3.60/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 3.60/0.98      inference(global_propositional_subsumption,
% 3.60/0.98                [status(thm)],
% 3.60/0.98                [c_5602,c_2264]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_6393,plain,
% 3.60/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(sK3,sK4,sK3)
% 3.60/0.98      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X0) = iProver_top
% 3.60/0.98      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X1) = iProver_top
% 3.60/0.98      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),sK3) = iProver_top ),
% 3.60/0.98      inference(superposition,[status(thm)],[c_1003,c_6383]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_6439,plain,
% 3.60/0.98      ( k3_tarski(k1_enumset1(sK3,sK3,sK3)) = k4_subset_1(sK3,sK4,sK3)
% 3.60/0.98      | r2_hidden(sK1(sK3,sK3,k4_subset_1(sK3,sK4,sK3)),sK3) = iProver_top ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_6393]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_6,plain,
% 3.60/0.98      ( ~ r2_hidden(X0,X1)
% 3.60/0.98      | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 3.60/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1002,plain,
% 3.60/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.60/0.98      | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
% 3.60/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_5603,plain,
% 3.60/0.98      ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) = iProver_top
% 3.60/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.60/0.98      inference(superposition,[status(thm)],[c_4726,c_1002]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_4,plain,
% 3.60/0.98      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.60/0.98      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 3.60/0.98      | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
% 3.60/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1004,plain,
% 3.60/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 3.60/0.98      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 3.60/0.98      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top ),
% 3.60/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_5931,plain,
% 3.60/0.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(sK3,sK4,sK3)
% 3.60/0.98      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X0) != iProver_top
% 3.60/0.98      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),sK3) != iProver_top ),
% 3.60/0.98      inference(superposition,[status(thm)],[c_5603,c_1004]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_5978,plain,
% 3.60/0.98      ( k3_tarski(k1_enumset1(sK3,sK3,sK3)) = k4_subset_1(sK3,sK4,sK3)
% 3.60/0.98      | r2_hidden(sK1(sK3,sK3,k4_subset_1(sK3,sK4,sK3)),sK3) != iProver_top ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_5931]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_461,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_460,plain,( X0 = X0 ),theory(equality) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_2245,plain,
% 3.60/0.98      ( X0 != X1 | X1 = X0 ),
% 3.60/0.98      inference(resolution,[status(thm)],[c_461,c_460]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_5437,plain,
% 3.60/0.98      ( r2_hidden(sK1(X0,X1,X2),X1)
% 3.60/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.60/0.98      | r2_hidden(sK1(X0,X1,X2),X0)
% 3.60/0.98      | X2 = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 3.60/0.98      inference(resolution,[status(thm)],[c_2245,c_5]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_5439,plain,
% 3.60/0.98      ( r2_hidden(sK1(sK3,sK3,sK3),sK3)
% 3.60/0.98      | sK3 = k3_tarski(k1_enumset1(sK3,sK3,sK3)) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_5437]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1283,plain,
% 3.60/0.98      ( X0 != X1
% 3.60/0.98      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != X1
% 3.60/0.98      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_461]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_2100,plain,
% 3.60/0.98      ( X0 != k4_subset_1(X1,sK4,X2)
% 3.60/0.98      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0
% 3.60/0.98      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(X1,sK4,X2) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_1283]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_3783,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(X0,sK4,X1)
% 3.60/0.98      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k3_tarski(k1_enumset1(X2,X2,X3))
% 3.60/0.98      | k3_tarski(k1_enumset1(X2,X2,X3)) != k4_subset_1(X0,sK4,X1) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_2100]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_3787,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(sK3,sK4,sK3)
% 3.60/0.98      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k3_tarski(k1_enumset1(sK3,sK3,sK3))
% 3.60/0.98      | k3_tarski(k1_enumset1(sK3,sK3,sK3)) != k4_subset_1(sK3,sK4,sK3) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_3783]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_3110,plain,
% 3.60/0.98      ( k2_subset_1(sK3) != X0
% 3.60/0.98      | k2_subset_1(sK3) = k3_tarski(k1_enumset1(X1,X1,X2))
% 3.60/0.98      | k3_tarski(k1_enumset1(X1,X1,X2)) != X0 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_461]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_3111,plain,
% 3.60/0.98      ( k2_subset_1(sK3) = k3_tarski(k1_enumset1(sK3,sK3,sK3))
% 3.60/0.98      | k2_subset_1(sK3) != sK3
% 3.60/0.98      | k3_tarski(k1_enumset1(sK3,sK3,sK3)) != sK3 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_3110]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_2870,plain,
% 3.60/0.98      ( X0 != k3_tarski(k1_enumset1(X1,X1,X2))
% 3.60/0.98      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0
% 3.60/0.98      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k1_enumset1(X1,X1,X2)) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_1283]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_2871,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k1_enumset1(sK3,sK3,sK3))
% 3.60/0.98      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = sK3
% 3.60/0.98      | sK3 != k3_tarski(k1_enumset1(sK3,sK3,sK3)) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_2870]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1199,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != X0
% 3.60/0.98      | k2_subset_1(sK3) != X0
% 3.60/0.98      | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_461]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_2867,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k1_enumset1(X0,X0,X1))
% 3.60/0.98      | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
% 3.60/0.98      | k2_subset_1(sK3) != k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_1199]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_2868,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k1_enumset1(sK3,sK3,sK3))
% 3.60/0.98      | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
% 3.60/0.98      | k2_subset_1(sK3) != k3_tarski(k1_enumset1(sK3,sK3,sK3)) ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_2867]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_469,plain,
% 3.60/0.98      ( X0 != X1
% 3.60/0.98      | X2 != X3
% 3.60/0.98      | X4 != X5
% 3.60/0.98      | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
% 3.60/0.98      theory(equality) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1285,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(X0,X1,X2)
% 3.60/0.98      | k2_subset_1(sK3) != X2
% 3.60/0.98      | sK4 != X1
% 3.60/0.98      | sK3 != X0 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_469]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1597,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(X0,sK4,X1)
% 3.60/0.98      | k2_subset_1(sK3) != X1
% 3.60/0.98      | sK4 != sK4
% 3.60/0.98      | sK3 != X0 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_1285]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1598,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(sK3,sK4,sK3)
% 3.60/0.98      | k2_subset_1(sK3) != sK3
% 3.60/0.98      | sK4 != sK4
% 3.60/0.98      | sK3 != sK3 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_1597]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1328,plain,
% 3.60/0.98      ( sK4 = sK4 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_460]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_1200,plain,
% 3.60/0.98      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != sK3
% 3.60/0.98      | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
% 3.60/0.98      | k2_subset_1(sK3) != sK3 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_1199]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_479,plain,
% 3.60/0.98      ( sK3 = sK3 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_460]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_69,plain,
% 3.60/0.98      ( ~ r2_hidden(sK1(sK3,sK3,sK3),sK3)
% 3.60/0.98      | k3_tarski(k1_enumset1(sK3,sK3,sK3)) = sK3 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_34,plain,
% 3.60/0.98      ( k2_subset_1(sK3) = sK3 ),
% 3.60/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(c_22,negated_conjecture,
% 3.60/0.98      ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
% 3.60/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.60/0.98  
% 3.60/0.98  cnf(contradiction,plain,
% 3.60/0.98      ( $false ),
% 3.60/0.98      inference(minisat,
% 3.60/0.98                [status(thm)],
% 3.60/0.98                [c_6439,c_5978,c_5439,c_3787,c_3111,c_2871,c_2868,c_1598,
% 3.60/0.98                 c_1328,c_1200,c_479,c_69,c_34,c_22]) ).
% 3.60/0.98  
% 3.60/0.98  
% 3.60/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/0.98  
% 3.60/0.98  ------                               Statistics
% 3.60/0.98  
% 3.60/0.98  ------ Selected
% 3.60/0.98  
% 3.60/0.98  total_time:                             0.162
% 3.60/0.98  
%------------------------------------------------------------------------------
