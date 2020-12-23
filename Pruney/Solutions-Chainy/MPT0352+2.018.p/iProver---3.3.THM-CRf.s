%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:34 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 323 expanded)
%              Number of clauses        :   71 ( 117 expanded)
%              Number of leaves         :   17 (  70 expanded)
%              Depth                    :   22
%              Number of atoms          :  298 (1168 expanded)
%              Number of equality atoms :  101 ( 198 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK3) )
        & ( r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | ~ r1_tarski(sK2,X2) )
          & ( r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | r1_tarski(sK2,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f37,f36])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_542,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_543,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_1660,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_543])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1497,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1874,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1660,c_1497])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1498,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1875,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1660,c_1498])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_551,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_552,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_1663,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_552])).

cnf(c_2045,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1875,c_1663])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1889,plain,
    ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1901,plain,
    ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1889])).

cnf(c_1903,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_2049,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2045,c_1903])).

cnf(c_2213,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1874,c_1903,c_2045])).

cnf(c_2217,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2213,c_1663])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1510,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13191,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_1510])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1513,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13997,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13191,c_1513])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1503,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14352,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_13997,c_1503])).

cnf(c_11,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14929,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_14352,c_11])).

cnf(c_18972,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_14929])).

cnf(c_21589,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK1)) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_10,c_18972])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_506,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_507,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_33,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_509,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_33])).

cnf(c_1496,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1499,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2498,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_1499])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1512,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2716,plain,
    ( k4_xboole_0(sK3,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2498,c_1512])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1506,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2841,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2716,c_1506])).

cnf(c_3160,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2841,c_1512])).

cnf(c_524,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_525,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_527,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_33])).

cnf(c_1495,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_2499,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1499])).

cnf(c_2832,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2499,c_1512])).

cnf(c_2948,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2832,c_11])).

cnf(c_3921,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2948])).

cnf(c_21676,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21589,c_3160,c_3921])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2246,plain,
    ( r1_tarski(sK2,sK3)
    | k4_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1758,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | k4_xboole_0(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1655,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | k4_xboole_0(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1656,plain,
    ( k4_xboole_0(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = k1_xboole_0
    | r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1655])).

cnf(c_30,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21676,c_2246,c_2049,c_1758,c_1656,c_24,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.72/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.98  
% 3.72/0.98  ------  iProver source info
% 3.72/0.98  
% 3.72/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.98  git: non_committed_changes: false
% 3.72/0.98  git: last_make_outside_of_git: false
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options
% 3.72/0.98  
% 3.72/0.98  --out_options                           all
% 3.72/0.98  --tptp_safe_out                         true
% 3.72/0.98  --problem_path                          ""
% 3.72/0.98  --include_path                          ""
% 3.72/0.98  --clausifier                            res/vclausify_rel
% 3.72/0.98  --clausifier_options                    --mode clausify
% 3.72/0.98  --stdin                                 false
% 3.72/0.98  --stats_out                             all
% 3.72/0.98  
% 3.72/0.98  ------ General Options
% 3.72/0.98  
% 3.72/0.98  --fof                                   false
% 3.72/0.98  --time_out_real                         305.
% 3.72/0.98  --time_out_virtual                      -1.
% 3.72/0.98  --symbol_type_check                     false
% 3.72/0.98  --clausify_out                          false
% 3.72/0.98  --sig_cnt_out                           false
% 3.72/0.98  --trig_cnt_out                          false
% 3.72/0.98  --trig_cnt_out_tolerance                1.
% 3.72/0.98  --trig_cnt_out_sk_spl                   false
% 3.72/0.98  --abstr_cl_out                          false
% 3.72/0.98  
% 3.72/0.98  ------ Global Options
% 3.72/0.98  
% 3.72/0.98  --schedule                              default
% 3.72/0.98  --add_important_lit                     false
% 3.72/0.98  --prop_solver_per_cl                    1000
% 3.72/0.98  --min_unsat_core                        false
% 3.72/0.98  --soft_assumptions                      false
% 3.72/0.98  --soft_lemma_size                       3
% 3.72/0.98  --prop_impl_unit_size                   0
% 3.72/0.98  --prop_impl_unit                        []
% 3.72/0.98  --share_sel_clauses                     true
% 3.72/0.98  --reset_solvers                         false
% 3.72/0.98  --bc_imp_inh                            [conj_cone]
% 3.72/0.98  --conj_cone_tolerance                   3.
% 3.72/0.98  --extra_neg_conj                        none
% 3.72/0.98  --large_theory_mode                     true
% 3.72/0.98  --prolific_symb_bound                   200
% 3.72/0.98  --lt_threshold                          2000
% 3.72/0.98  --clause_weak_htbl                      true
% 3.72/0.98  --gc_record_bc_elim                     false
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing Options
% 3.72/0.98  
% 3.72/0.98  --preprocessing_flag                    true
% 3.72/0.98  --time_out_prep_mult                    0.1
% 3.72/0.98  --splitting_mode                        input
% 3.72/0.98  --splitting_grd                         true
% 3.72/0.98  --splitting_cvd                         false
% 3.72/0.98  --splitting_cvd_svl                     false
% 3.72/0.98  --splitting_nvd                         32
% 3.72/0.98  --sub_typing                            true
% 3.72/0.98  --prep_gs_sim                           true
% 3.72/0.98  --prep_unflatten                        true
% 3.72/0.98  --prep_res_sim                          true
% 3.72/0.98  --prep_upred                            true
% 3.72/0.98  --prep_sem_filter                       exhaustive
% 3.72/0.98  --prep_sem_filter_out                   false
% 3.72/0.98  --pred_elim                             true
% 3.72/0.98  --res_sim_input                         true
% 3.72/0.98  --eq_ax_congr_red                       true
% 3.72/0.98  --pure_diseq_elim                       true
% 3.72/0.98  --brand_transform                       false
% 3.72/0.98  --non_eq_to_eq                          false
% 3.72/0.98  --prep_def_merge                        true
% 3.72/0.98  --prep_def_merge_prop_impl              false
% 3.72/0.98  --prep_def_merge_mbd                    true
% 3.72/0.98  --prep_def_merge_tr_red                 false
% 3.72/0.98  --prep_def_merge_tr_cl                  false
% 3.72/0.98  --smt_preprocessing                     true
% 3.72/0.98  --smt_ac_axioms                         fast
% 3.72/0.98  --preprocessed_out                      false
% 3.72/0.98  --preprocessed_stats                    false
% 3.72/0.98  
% 3.72/0.98  ------ Abstraction refinement Options
% 3.72/0.98  
% 3.72/0.98  --abstr_ref                             []
% 3.72/0.98  --abstr_ref_prep                        false
% 3.72/0.98  --abstr_ref_until_sat                   false
% 3.72/0.98  --abstr_ref_sig_restrict                funpre
% 3.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.98  --abstr_ref_under                       []
% 3.72/0.98  
% 3.72/0.98  ------ SAT Options
% 3.72/0.98  
% 3.72/0.98  --sat_mode                              false
% 3.72/0.98  --sat_fm_restart_options                ""
% 3.72/0.98  --sat_gr_def                            false
% 3.72/0.98  --sat_epr_types                         true
% 3.72/0.98  --sat_non_cyclic_types                  false
% 3.72/0.98  --sat_finite_models                     false
% 3.72/0.98  --sat_fm_lemmas                         false
% 3.72/0.98  --sat_fm_prep                           false
% 3.72/0.98  --sat_fm_uc_incr                        true
% 3.72/0.98  --sat_out_model                         small
% 3.72/0.98  --sat_out_clauses                       false
% 3.72/0.98  
% 3.72/0.98  ------ QBF Options
% 3.72/0.98  
% 3.72/0.98  --qbf_mode                              false
% 3.72/0.98  --qbf_elim_univ                         false
% 3.72/0.98  --qbf_dom_inst                          none
% 3.72/0.98  --qbf_dom_pre_inst                      false
% 3.72/0.98  --qbf_sk_in                             false
% 3.72/0.98  --qbf_pred_elim                         true
% 3.72/0.98  --qbf_split                             512
% 3.72/0.98  
% 3.72/0.98  ------ BMC1 Options
% 3.72/0.98  
% 3.72/0.98  --bmc1_incremental                      false
% 3.72/0.98  --bmc1_axioms                           reachable_all
% 3.72/0.98  --bmc1_min_bound                        0
% 3.72/0.98  --bmc1_max_bound                        -1
% 3.72/0.98  --bmc1_max_bound_default                -1
% 3.72/0.98  --bmc1_symbol_reachability              true
% 3.72/0.98  --bmc1_property_lemmas                  false
% 3.72/0.98  --bmc1_k_induction                      false
% 3.72/0.98  --bmc1_non_equiv_states                 false
% 3.72/0.98  --bmc1_deadlock                         false
% 3.72/0.98  --bmc1_ucm                              false
% 3.72/0.98  --bmc1_add_unsat_core                   none
% 3.72/0.98  --bmc1_unsat_core_children              false
% 3.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.98  --bmc1_out_stat                         full
% 3.72/0.98  --bmc1_ground_init                      false
% 3.72/0.98  --bmc1_pre_inst_next_state              false
% 3.72/0.98  --bmc1_pre_inst_state                   false
% 3.72/0.98  --bmc1_pre_inst_reach_state             false
% 3.72/0.98  --bmc1_out_unsat_core                   false
% 3.72/0.98  --bmc1_aig_witness_out                  false
% 3.72/0.98  --bmc1_verbose                          false
% 3.72/0.98  --bmc1_dump_clauses_tptp                false
% 3.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.98  --bmc1_dump_file                        -
% 3.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.98  --bmc1_ucm_extend_mode                  1
% 3.72/0.98  --bmc1_ucm_init_mode                    2
% 3.72/0.98  --bmc1_ucm_cone_mode                    none
% 3.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.98  --bmc1_ucm_relax_model                  4
% 3.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.98  --bmc1_ucm_layered_model                none
% 3.72/0.98  --bmc1_ucm_max_lemma_size               10
% 3.72/0.98  
% 3.72/0.98  ------ AIG Options
% 3.72/0.98  
% 3.72/0.98  --aig_mode                              false
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation Options
% 3.72/0.98  
% 3.72/0.98  --instantiation_flag                    true
% 3.72/0.98  --inst_sos_flag                         false
% 3.72/0.98  --inst_sos_phase                        true
% 3.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel_side                     num_symb
% 3.72/0.98  --inst_solver_per_active                1400
% 3.72/0.98  --inst_solver_calls_frac                1.
% 3.72/0.98  --inst_passive_queue_type               priority_queues
% 3.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.98  --inst_passive_queues_freq              [25;2]
% 3.72/0.98  --inst_dismatching                      true
% 3.72/0.98  --inst_eager_unprocessed_to_passive     true
% 3.72/0.98  --inst_prop_sim_given                   true
% 3.72/0.98  --inst_prop_sim_new                     false
% 3.72/0.98  --inst_subs_new                         false
% 3.72/0.98  --inst_eq_res_simp                      false
% 3.72/0.98  --inst_subs_given                       false
% 3.72/0.98  --inst_orphan_elimination               true
% 3.72/0.98  --inst_learning_loop_flag               true
% 3.72/0.98  --inst_learning_start                   3000
% 3.72/0.98  --inst_learning_factor                  2
% 3.72/0.98  --inst_start_prop_sim_after_learn       3
% 3.72/0.98  --inst_sel_renew                        solver
% 3.72/0.98  --inst_lit_activity_flag                true
% 3.72/0.98  --inst_restr_to_given                   false
% 3.72/0.98  --inst_activity_threshold               500
% 3.72/0.98  --inst_out_proof                        true
% 3.72/0.98  
% 3.72/0.98  ------ Resolution Options
% 3.72/0.98  
% 3.72/0.98  --resolution_flag                       true
% 3.72/0.98  --res_lit_sel                           adaptive
% 3.72/0.98  --res_lit_sel_side                      none
% 3.72/0.98  --res_ordering                          kbo
% 3.72/0.98  --res_to_prop_solver                    active
% 3.72/0.98  --res_prop_simpl_new                    false
% 3.72/0.98  --res_prop_simpl_given                  true
% 3.72/0.98  --res_passive_queue_type                priority_queues
% 3.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.98  --res_passive_queues_freq               [15;5]
% 3.72/0.98  --res_forward_subs                      full
% 3.72/0.98  --res_backward_subs                     full
% 3.72/0.98  --res_forward_subs_resolution           true
% 3.72/0.98  --res_backward_subs_resolution          true
% 3.72/0.98  --res_orphan_elimination                true
% 3.72/0.98  --res_time_limit                        2.
% 3.72/0.98  --res_out_proof                         true
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Options
% 3.72/0.98  
% 3.72/0.98  --superposition_flag                    true
% 3.72/0.98  --sup_passive_queue_type                priority_queues
% 3.72/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.98  --demod_completeness_check              fast
% 3.72/0.98  --demod_use_ground                      true
% 3.72/0.98  --sup_to_prop_solver                    passive
% 3.72/0.98  --sup_prop_simpl_new                    true
% 3.72/0.98  --sup_prop_simpl_given                  true
% 3.72/0.98  --sup_fun_splitting                     false
% 3.72/0.98  --sup_smt_interval                      50000
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Simplification Setup
% 3.72/0.98  
% 3.72/0.98  --sup_indices_passive                   []
% 3.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_full_bw                           [BwDemod]
% 3.72/0.98  --sup_immed_triv                        [TrivRules]
% 3.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_immed_bw_main                     []
% 3.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  
% 3.72/0.98  ------ Combination Options
% 3.72/0.98  
% 3.72/0.98  --comb_res_mult                         3
% 3.72/0.98  --comb_sup_mult                         2
% 3.72/0.98  --comb_inst_mult                        10
% 3.72/0.98  
% 3.72/0.98  ------ Debug Options
% 3.72/0.98  
% 3.72/0.98  --dbg_backtrace                         false
% 3.72/0.98  --dbg_dump_prop_clauses                 false
% 3.72/0.98  --dbg_dump_prop_clauses_file            -
% 3.72/0.98  --dbg_out_stat                          false
% 3.72/0.98  ------ Parsing...
% 3.72/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  ------ Proving...
% 3.72/0.98  ------ Problem Properties 
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  clauses                                 25
% 3.72/0.98  conjectures                             2
% 3.72/0.98  EPR                                     2
% 3.72/0.98  Horn                                    23
% 3.72/0.98  unary                                   6
% 3.72/0.98  binary                                  16
% 3.72/0.98  lits                                    47
% 3.72/0.98  lits eq                                 15
% 3.72/0.98  fd_pure                                 0
% 3.72/0.98  fd_pseudo                               0
% 3.72/0.98  fd_cond                                 1
% 3.72/0.98  fd_pseudo_cond                          2
% 3.72/0.98  AC symbols                              0
% 3.72/0.98  
% 3.72/0.98  ------ Schedule dynamic 5 is on 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  Current options:
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options
% 3.72/0.98  
% 3.72/0.98  --out_options                           all
% 3.72/0.98  --tptp_safe_out                         true
% 3.72/0.98  --problem_path                          ""
% 3.72/0.98  --include_path                          ""
% 3.72/0.98  --clausifier                            res/vclausify_rel
% 3.72/0.98  --clausifier_options                    --mode clausify
% 3.72/0.98  --stdin                                 false
% 3.72/0.98  --stats_out                             all
% 3.72/0.98  
% 3.72/0.98  ------ General Options
% 3.72/0.98  
% 3.72/0.98  --fof                                   false
% 3.72/0.98  --time_out_real                         305.
% 3.72/0.98  --time_out_virtual                      -1.
% 3.72/0.98  --symbol_type_check                     false
% 3.72/0.98  --clausify_out                          false
% 3.72/0.98  --sig_cnt_out                           false
% 3.72/0.98  --trig_cnt_out                          false
% 3.72/0.98  --trig_cnt_out_tolerance                1.
% 3.72/0.98  --trig_cnt_out_sk_spl                   false
% 3.72/0.98  --abstr_cl_out                          false
% 3.72/0.98  
% 3.72/0.98  ------ Global Options
% 3.72/0.98  
% 3.72/0.98  --schedule                              default
% 3.72/0.98  --add_important_lit                     false
% 3.72/0.98  --prop_solver_per_cl                    1000
% 3.72/0.98  --min_unsat_core                        false
% 3.72/0.98  --soft_assumptions                      false
% 3.72/0.98  --soft_lemma_size                       3
% 3.72/0.98  --prop_impl_unit_size                   0
% 3.72/0.98  --prop_impl_unit                        []
% 3.72/0.98  --share_sel_clauses                     true
% 3.72/0.98  --reset_solvers                         false
% 3.72/0.98  --bc_imp_inh                            [conj_cone]
% 3.72/0.98  --conj_cone_tolerance                   3.
% 3.72/0.98  --extra_neg_conj                        none
% 3.72/0.98  --large_theory_mode                     true
% 3.72/0.98  --prolific_symb_bound                   200
% 3.72/0.98  --lt_threshold                          2000
% 3.72/0.98  --clause_weak_htbl                      true
% 3.72/0.98  --gc_record_bc_elim                     false
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing Options
% 3.72/0.98  
% 3.72/0.98  --preprocessing_flag                    true
% 3.72/0.98  --time_out_prep_mult                    0.1
% 3.72/0.98  --splitting_mode                        input
% 3.72/0.98  --splitting_grd                         true
% 3.72/0.98  --splitting_cvd                         false
% 3.72/0.98  --splitting_cvd_svl                     false
% 3.72/0.98  --splitting_nvd                         32
% 3.72/0.98  --sub_typing                            true
% 3.72/0.98  --prep_gs_sim                           true
% 3.72/0.98  --prep_unflatten                        true
% 3.72/0.98  --prep_res_sim                          true
% 3.72/0.98  --prep_upred                            true
% 3.72/0.98  --prep_sem_filter                       exhaustive
% 3.72/0.98  --prep_sem_filter_out                   false
% 3.72/0.98  --pred_elim                             true
% 3.72/0.98  --res_sim_input                         true
% 3.72/0.98  --eq_ax_congr_red                       true
% 3.72/0.98  --pure_diseq_elim                       true
% 3.72/0.98  --brand_transform                       false
% 3.72/0.98  --non_eq_to_eq                          false
% 3.72/0.98  --prep_def_merge                        true
% 3.72/0.98  --prep_def_merge_prop_impl              false
% 3.72/0.98  --prep_def_merge_mbd                    true
% 3.72/0.98  --prep_def_merge_tr_red                 false
% 3.72/0.98  --prep_def_merge_tr_cl                  false
% 3.72/0.98  --smt_preprocessing                     true
% 3.72/0.98  --smt_ac_axioms                         fast
% 3.72/0.98  --preprocessed_out                      false
% 3.72/0.98  --preprocessed_stats                    false
% 3.72/0.98  
% 3.72/0.98  ------ Abstraction refinement Options
% 3.72/0.98  
% 3.72/0.98  --abstr_ref                             []
% 3.72/0.98  --abstr_ref_prep                        false
% 3.72/0.98  --abstr_ref_until_sat                   false
% 3.72/0.98  --abstr_ref_sig_restrict                funpre
% 3.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.98  --abstr_ref_under                       []
% 3.72/0.98  
% 3.72/0.98  ------ SAT Options
% 3.72/0.98  
% 3.72/0.98  --sat_mode                              false
% 3.72/0.98  --sat_fm_restart_options                ""
% 3.72/0.98  --sat_gr_def                            false
% 3.72/0.98  --sat_epr_types                         true
% 3.72/0.98  --sat_non_cyclic_types                  false
% 3.72/0.98  --sat_finite_models                     false
% 3.72/0.98  --sat_fm_lemmas                         false
% 3.72/0.98  --sat_fm_prep                           false
% 3.72/0.98  --sat_fm_uc_incr                        true
% 3.72/0.98  --sat_out_model                         small
% 3.72/0.98  --sat_out_clauses                       false
% 3.72/0.98  
% 3.72/0.98  ------ QBF Options
% 3.72/0.98  
% 3.72/0.98  --qbf_mode                              false
% 3.72/0.98  --qbf_elim_univ                         false
% 3.72/0.98  --qbf_dom_inst                          none
% 3.72/0.98  --qbf_dom_pre_inst                      false
% 3.72/0.98  --qbf_sk_in                             false
% 3.72/0.98  --qbf_pred_elim                         true
% 3.72/0.98  --qbf_split                             512
% 3.72/0.98  
% 3.72/0.98  ------ BMC1 Options
% 3.72/0.98  
% 3.72/0.98  --bmc1_incremental                      false
% 3.72/0.98  --bmc1_axioms                           reachable_all
% 3.72/0.98  --bmc1_min_bound                        0
% 3.72/0.98  --bmc1_max_bound                        -1
% 3.72/0.98  --bmc1_max_bound_default                -1
% 3.72/0.98  --bmc1_symbol_reachability              true
% 3.72/0.98  --bmc1_property_lemmas                  false
% 3.72/0.98  --bmc1_k_induction                      false
% 3.72/0.98  --bmc1_non_equiv_states                 false
% 3.72/0.98  --bmc1_deadlock                         false
% 3.72/0.98  --bmc1_ucm                              false
% 3.72/0.98  --bmc1_add_unsat_core                   none
% 3.72/0.98  --bmc1_unsat_core_children              false
% 3.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.98  --bmc1_out_stat                         full
% 3.72/0.98  --bmc1_ground_init                      false
% 3.72/0.98  --bmc1_pre_inst_next_state              false
% 3.72/0.98  --bmc1_pre_inst_state                   false
% 3.72/0.98  --bmc1_pre_inst_reach_state             false
% 3.72/0.98  --bmc1_out_unsat_core                   false
% 3.72/0.98  --bmc1_aig_witness_out                  false
% 3.72/0.98  --bmc1_verbose                          false
% 3.72/0.98  --bmc1_dump_clauses_tptp                false
% 3.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.98  --bmc1_dump_file                        -
% 3.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.98  --bmc1_ucm_extend_mode                  1
% 3.72/0.98  --bmc1_ucm_init_mode                    2
% 3.72/0.98  --bmc1_ucm_cone_mode                    none
% 3.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.98  --bmc1_ucm_relax_model                  4
% 3.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.98  --bmc1_ucm_layered_model                none
% 3.72/0.98  --bmc1_ucm_max_lemma_size               10
% 3.72/0.98  
% 3.72/0.98  ------ AIG Options
% 3.72/0.98  
% 3.72/0.98  --aig_mode                              false
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation Options
% 3.72/0.98  
% 3.72/0.98  --instantiation_flag                    true
% 3.72/0.98  --inst_sos_flag                         false
% 3.72/0.98  --inst_sos_phase                        true
% 3.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel_side                     none
% 3.72/0.98  --inst_solver_per_active                1400
% 3.72/0.98  --inst_solver_calls_frac                1.
% 3.72/0.98  --inst_passive_queue_type               priority_queues
% 3.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.98  --inst_passive_queues_freq              [25;2]
% 3.72/0.98  --inst_dismatching                      true
% 3.72/0.98  --inst_eager_unprocessed_to_passive     true
% 3.72/0.98  --inst_prop_sim_given                   true
% 3.72/0.98  --inst_prop_sim_new                     false
% 3.72/0.98  --inst_subs_new                         false
% 3.72/0.98  --inst_eq_res_simp                      false
% 3.72/0.98  --inst_subs_given                       false
% 3.72/0.98  --inst_orphan_elimination               true
% 3.72/0.98  --inst_learning_loop_flag               true
% 3.72/0.98  --inst_learning_start                   3000
% 3.72/0.98  --inst_learning_factor                  2
% 3.72/0.98  --inst_start_prop_sim_after_learn       3
% 3.72/0.98  --inst_sel_renew                        solver
% 3.72/0.98  --inst_lit_activity_flag                true
% 3.72/0.98  --inst_restr_to_given                   false
% 3.72/0.98  --inst_activity_threshold               500
% 3.72/0.98  --inst_out_proof                        true
% 3.72/0.98  
% 3.72/0.98  ------ Resolution Options
% 3.72/0.98  
% 3.72/0.98  --resolution_flag                       false
% 3.72/0.98  --res_lit_sel                           adaptive
% 3.72/0.98  --res_lit_sel_side                      none
% 3.72/0.98  --res_ordering                          kbo
% 3.72/0.98  --res_to_prop_solver                    active
% 3.72/0.98  --res_prop_simpl_new                    false
% 3.72/0.98  --res_prop_simpl_given                  true
% 3.72/0.98  --res_passive_queue_type                priority_queues
% 3.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.98  --res_passive_queues_freq               [15;5]
% 3.72/0.98  --res_forward_subs                      full
% 3.72/0.98  --res_backward_subs                     full
% 3.72/0.98  --res_forward_subs_resolution           true
% 3.72/0.98  --res_backward_subs_resolution          true
% 3.72/0.98  --res_orphan_elimination                true
% 3.72/0.98  --res_time_limit                        2.
% 3.72/0.98  --res_out_proof                         true
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Options
% 3.72/0.98  
% 3.72/0.98  --superposition_flag                    true
% 3.72/0.98  --sup_passive_queue_type                priority_queues
% 3.72/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.98  --demod_completeness_check              fast
% 3.72/0.98  --demod_use_ground                      true
% 3.72/0.98  --sup_to_prop_solver                    passive
% 3.72/0.98  --sup_prop_simpl_new                    true
% 3.72/0.98  --sup_prop_simpl_given                  true
% 3.72/0.98  --sup_fun_splitting                     false
% 3.72/0.98  --sup_smt_interval                      50000
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Simplification Setup
% 3.72/0.98  
% 3.72/0.98  --sup_indices_passive                   []
% 3.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_full_bw                           [BwDemod]
% 3.72/0.98  --sup_immed_triv                        [TrivRules]
% 3.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_immed_bw_main                     []
% 3.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  
% 3.72/0.98  ------ Combination Options
% 3.72/0.98  
% 3.72/0.98  --comb_res_mult                         3
% 3.72/0.98  --comb_sup_mult                         2
% 3.72/0.98  --comb_inst_mult                        10
% 3.72/0.98  
% 3.72/0.98  ------ Debug Options
% 3.72/0.98  
% 3.72/0.98  --dbg_backtrace                         false
% 3.72/0.98  --dbg_dump_prop_clauses                 false
% 3.72/0.98  --dbg_dump_prop_clauses_file            -
% 3.72/0.98  --dbg_out_stat                          false
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS status Theorem for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  fof(f9,axiom,(
% 3.72/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f49,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f9])).
% 3.72/0.98  
% 3.72/0.98  fof(f1,axiom,(
% 3.72/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f39,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f1])).
% 3.72/0.98  
% 3.72/0.98  fof(f14,axiom,(
% 3.72/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f25,plain,(
% 3.72/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/0.98    inference(ennf_transformation,[],[f14])).
% 3.72/0.98  
% 3.72/0.98  fof(f61,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f25])).
% 3.72/0.98  
% 3.72/0.98  fof(f16,conjecture,(
% 3.72/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f17,negated_conjecture,(
% 3.72/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.72/0.98    inference(negated_conjecture,[],[f16])).
% 3.72/0.98  
% 3.72/0.98  fof(f26,plain,(
% 3.72/0.98    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/0.98    inference(ennf_transformation,[],[f17])).
% 3.72/0.98  
% 3.72/0.98  fof(f34,plain,(
% 3.72/0.98    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/0.98    inference(nnf_transformation,[],[f26])).
% 3.72/0.98  
% 3.72/0.98  fof(f35,plain,(
% 3.72/0.98    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/0.98    inference(flattening,[],[f34])).
% 3.72/0.98  
% 3.72/0.98  fof(f37,plain,(
% 3.72/0.98    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f36,plain,(
% 3.72/0.98    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f38,plain,(
% 3.72/0.98    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f37,f36])).
% 3.72/0.98  
% 3.72/0.98  fof(f64,plain,(
% 3.72/0.98    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.72/0.98    inference(cnf_transformation,[],[f38])).
% 3.72/0.98  
% 3.72/0.98  fof(f65,plain,(
% 3.72/0.98    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 3.72/0.98    inference(cnf_transformation,[],[f38])).
% 3.72/0.98  
% 3.72/0.98  fof(f66,plain,(
% 3.72/0.98    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 3.72/0.98    inference(cnf_transformation,[],[f38])).
% 3.72/0.98  
% 3.72/0.98  fof(f63,plain,(
% 3.72/0.98    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.72/0.98    inference(cnf_transformation,[],[f38])).
% 3.72/0.99  
% 3.72/0.99  fof(f6,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f22,plain,(
% 3.72/0.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.72/0.99    inference(ennf_transformation,[],[f6])).
% 3.72/0.99  
% 3.72/0.99  fof(f46,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f22])).
% 3.72/0.99  
% 3.72/0.99  fof(f4,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f19,plain,(
% 3.72/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.72/0.99    inference(ennf_transformation,[],[f4])).
% 3.72/0.99  
% 3.72/0.99  fof(f44,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f19])).
% 3.72/0.99  
% 3.72/0.99  fof(f2,axiom,(
% 3.72/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f18,plain,(
% 3.72/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.72/0.99    inference(ennf_transformation,[],[f2])).
% 3.72/0.99  
% 3.72/0.99  fof(f40,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f18])).
% 3.72/0.99  
% 3.72/0.99  fof(f11,axiom,(
% 3.72/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f28,plain,(
% 3.72/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(nnf_transformation,[],[f11])).
% 3.72/0.99  
% 3.72/0.99  fof(f51,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f28])).
% 3.72/0.99  
% 3.72/0.99  fof(f10,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f50,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f10])).
% 3.72/0.99  
% 3.72/0.99  fof(f13,axiom,(
% 3.72/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f24,plain,(
% 3.72/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.72/0.99    inference(ennf_transformation,[],[f13])).
% 3.72/0.99  
% 3.72/0.99  fof(f33,plain,(
% 3.72/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.72/0.99    inference(nnf_transformation,[],[f24])).
% 3.72/0.99  
% 3.72/0.99  fof(f57,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f33])).
% 3.72/0.99  
% 3.72/0.99  fof(f15,axiom,(
% 3.72/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f62,plain,(
% 3.72/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f15])).
% 3.72/0.99  
% 3.72/0.99  fof(f12,axiom,(
% 3.72/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f29,plain,(
% 3.72/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.72/0.99    inference(nnf_transformation,[],[f12])).
% 3.72/0.99  
% 3.72/0.99  fof(f30,plain,(
% 3.72/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.72/0.99    inference(rectify,[],[f29])).
% 3.72/0.99  
% 3.72/0.99  fof(f31,plain,(
% 3.72/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f32,plain,(
% 3.72/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.72/0.99  
% 3.72/0.99  fof(f53,plain,(
% 3.72/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.72/0.99    inference(cnf_transformation,[],[f32])).
% 3.72/0.99  
% 3.72/0.99  fof(f68,plain,(
% 3.72/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.72/0.99    inference(equality_resolution,[],[f53])).
% 3.72/0.99  
% 3.72/0.99  fof(f3,axiom,(
% 3.72/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f27,plain,(
% 3.72/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.72/0.99    inference(nnf_transformation,[],[f3])).
% 3.72/0.99  
% 3.72/0.99  fof(f42,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f27])).
% 3.72/0.99  
% 3.72/0.99  fof(f7,axiom,(
% 3.72/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f47,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f7])).
% 3.72/0.99  
% 3.72/0.99  fof(f41,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.72/0.99    inference(cnf_transformation,[],[f27])).
% 3.72/0.99  
% 3.72/0.99  cnf(c_10,plain,
% 3.72/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_0,plain,
% 3.72/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_22,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_26,negated_conjecture,
% 3.72/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_542,plain,
% 3.72/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.72/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.72/0.99      | sK3 != X1 ),
% 3.72/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_543,plain,
% 3.72/0.99      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 3.72/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.72/0.99      inference(unflattening,[status(thm)],[c_542]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1660,plain,
% 3.72/0.99      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 3.72/0.99      inference(equality_resolution,[status(thm)],[c_543]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_25,negated_conjecture,
% 3.72/0.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 3.72/0.99      | r1_tarski(sK2,sK3) ),
% 3.72/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1497,plain,
% 3.72/0.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 3.72/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1874,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 3.72/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_1660,c_1497]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_24,negated_conjecture,
% 3.72/0.99      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 3.72/0.99      | ~ r1_tarski(sK2,sK3) ),
% 3.72/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1498,plain,
% 3.72/0.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 3.72/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1875,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 3.72/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_1660,c_1498]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_27,negated_conjecture,
% 3.72/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_551,plain,
% 3.72/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.72/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.72/0.99      | sK2 != X1 ),
% 3.72/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_552,plain,
% 3.72/0.99      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 3.72/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.72/0.99      inference(unflattening,[status(thm)],[c_551]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1663,plain,
% 3.72/0.99      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 3.72/0.99      inference(equality_resolution,[status(thm)],[c_552]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2045,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 3.72/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_1875,c_1663]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_7,plain,
% 3.72/0.99      ( ~ r1_tarski(X0,X1)
% 3.72/0.99      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1889,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2))
% 3.72/0.99      | ~ r1_tarski(sK2,sK3) ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1901,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2)) = iProver_top
% 3.72/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1889]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1903,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 3.72/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_1901]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2049,plain,
% 3.72/0.99      ( r1_tarski(sK2,sK3) != iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_2045,c_1903]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2213,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_1874,c_1903,c_2045]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2217,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 3.72/0.99      inference(light_normalisation,[status(thm)],[c_2213,c_1663]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_4,plain,
% 3.72/0.99      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 3.72/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1510,plain,
% 3.72/0.99      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 3.72/0.99      | r1_xboole_0(X0,X2) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_13191,plain,
% 3.72/0.99      ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2217,c_1510]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1,plain,
% 3.72/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1513,plain,
% 3.72/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.72/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_13997,plain,
% 3.72/0.99      ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_13191,c_1513]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_13,plain,
% 3.72/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1503,plain,
% 3.72/0.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_14352,plain,
% 3.72/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = sK2 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_13997,c_1503]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11,plain,
% 3.72/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_14929,plain,
% 3.72/0.99      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK2,X0) ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_14352,c_11]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_18972,plain,
% 3.72/0.99      ( k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k4_xboole_0(sK2,X0) ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_0,c_14929]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_21589,plain,
% 3.72/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK1)) = k4_xboole_0(sK2,sK3) ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_10,c_18972]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_21,plain,
% 3.72/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_506,plain,
% 3.72/0.99      ( r2_hidden(X0,X1)
% 3.72/0.99      | v1_xboole_0(X1)
% 3.72/0.99      | k1_zfmisc_1(sK1) != X1
% 3.72/0.99      | sK3 != X0 ),
% 3.72/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_507,plain,
% 3.72/0.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.72/0.99      inference(unflattening,[status(thm)],[c_506]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_23,plain,
% 3.72/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_33,plain,
% 3.72/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_509,plain,
% 3.72/0.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_507,c_33]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1496,plain,
% 3.72/0.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_17,plain,
% 3.72/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1499,plain,
% 3.72/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.72/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2498,plain,
% 3.72/0.99      ( r1_tarski(sK3,sK1) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1496,c_1499]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2,plain,
% 3.72/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1512,plain,
% 3.72/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.72/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2716,plain,
% 3.72/0.99      ( k4_xboole_0(sK3,sK1) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2498,c_1512]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_8,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1506,plain,
% 3.72/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2841,plain,
% 3.72/0.99      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2716,c_1506]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3160,plain,
% 3.72/0.99      ( k4_xboole_0(k1_xboole_0,sK3) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2841,c_1512]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_524,plain,
% 3.72/0.99      ( r2_hidden(X0,X1)
% 3.72/0.99      | v1_xboole_0(X1)
% 3.72/0.99      | k1_zfmisc_1(sK1) != X1
% 3.72/0.99      | sK2 != X0 ),
% 3.72/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_525,plain,
% 3.72/0.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.72/0.99      inference(unflattening,[status(thm)],[c_524]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_527,plain,
% 3.72/0.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_525,c_33]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1495,plain,
% 3.72/0.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2499,plain,
% 3.72/0.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1495,c_1499]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2832,plain,
% 3.72/0.99      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2499,c_1512]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2948,plain,
% 3.72/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_2832,c_11]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3921,plain,
% 3.72/0.99      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_0,c_2948]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_21676,plain,
% 3.72/0.99      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_21589,c_3160,c_3921]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3,plain,
% 3.72/0.99      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2246,plain,
% 3.72/0.99      ( r1_tarski(sK2,sK3) | k4_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1758,plain,
% 3.72/0.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 3.72/0.99      | k4_xboole_0(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != k1_xboole_0 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1655,plain,
% 3.72/0.99      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 3.72/0.99      | k4_xboole_0(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = k1_xboole_0 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1656,plain,
% 3.72/0.99      ( k4_xboole_0(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = k1_xboole_0
% 3.72/0.99      | r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1655]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_30,plain,
% 3.72/0.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 3.72/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(contradiction,plain,
% 3.72/0.99      ( $false ),
% 3.72/0.99      inference(minisat,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_21676,c_2246,c_2049,c_1758,c_1656,c_24,c_30]) ).
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  ------                               Statistics
% 3.72/0.99  
% 3.72/0.99  ------ General
% 3.72/0.99  
% 3.72/0.99  abstr_ref_over_cycles:                  0
% 3.72/0.99  abstr_ref_under_cycles:                 0
% 3.72/0.99  gc_basic_clause_elim:                   0
% 3.72/0.99  forced_gc_time:                         0
% 3.72/0.99  parsing_time:                           0.01
% 3.72/0.99  unif_index_cands_time:                  0.
% 3.72/0.99  unif_index_add_time:                    0.
% 3.72/0.99  orderings_time:                         0.
% 3.72/0.99  out_proof_time:                         0.008
% 3.72/0.99  total_time:                             0.487
% 3.72/0.99  num_of_symbols:                         45
% 3.72/0.99  num_of_terms:                           21542
% 3.72/0.99  
% 3.72/0.99  ------ Preprocessing
% 3.72/0.99  
% 3.72/0.99  num_of_splits:                          0
% 3.72/0.99  num_of_split_atoms:                     0
% 3.72/0.99  num_of_reused_defs:                     0
% 3.72/0.99  num_eq_ax_congr_red:                    15
% 3.72/0.99  num_of_sem_filtered_clauses:            1
% 3.72/0.99  num_of_subtypes:                        0
% 3.72/0.99  monotx_restored_types:                  0
% 3.72/0.99  sat_num_of_epr_types:                   0
% 3.72/0.99  sat_num_of_non_cyclic_types:            0
% 3.72/0.99  sat_guarded_non_collapsed_types:        0
% 3.72/0.99  num_pure_diseq_elim:                    0
% 3.72/0.99  simp_replaced_by:                       0
% 3.72/0.99  res_preprocessed:                       120
% 3.72/0.99  prep_upred:                             0
% 3.72/0.99  prep_unflattend:                        46
% 3.72/0.99  smt_new_axioms:                         0
% 3.72/0.99  pred_elim_cands:                        3
% 3.72/0.99  pred_elim:                              2
% 3.72/0.99  pred_elim_cl:                           3
% 3.72/0.99  pred_elim_cycles:                       5
% 3.72/0.99  merged_defs:                            32
% 3.72/0.99  merged_defs_ncl:                        0
% 3.72/0.99  bin_hyper_res:                          33
% 3.72/0.99  prep_cycles:                            4
% 3.72/0.99  pred_elim_time:                         0.006
% 3.72/0.99  splitting_time:                         0.
% 3.72/0.99  sem_filter_time:                        0.
% 3.72/0.99  monotx_time:                            0.001
% 3.72/0.99  subtype_inf_time:                       0.
% 3.72/0.99  
% 3.72/0.99  ------ Problem properties
% 3.72/0.99  
% 3.72/0.99  clauses:                                25
% 3.72/0.99  conjectures:                            2
% 3.72/0.99  epr:                                    2
% 3.72/0.99  horn:                                   23
% 3.72/0.99  ground:                                 4
% 3.72/0.99  unary:                                  6
% 3.72/0.99  binary:                                 16
% 3.72/0.99  lits:                                   47
% 3.72/0.99  lits_eq:                                15
% 3.72/0.99  fd_pure:                                0
% 3.72/0.99  fd_pseudo:                              0
% 3.72/0.99  fd_cond:                                1
% 3.72/0.99  fd_pseudo_cond:                         2
% 3.72/0.99  ac_symbols:                             0
% 3.72/0.99  
% 3.72/0.99  ------ Propositional Solver
% 3.72/0.99  
% 3.72/0.99  prop_solver_calls:                      27
% 3.72/0.99  prop_fast_solver_calls:                 781
% 3.72/0.99  smt_solver_calls:                       0
% 3.72/0.99  smt_fast_solver_calls:                  0
% 3.72/0.99  prop_num_of_clauses:                    6898
% 3.72/0.99  prop_preprocess_simplified:             13694
% 3.72/0.99  prop_fo_subsumed:                       11
% 3.72/0.99  prop_solver_time:                       0.
% 3.72/0.99  smt_solver_time:                        0.
% 3.72/0.99  smt_fast_solver_time:                   0.
% 3.72/0.99  prop_fast_solver_time:                  0.
% 3.72/0.99  prop_unsat_core_time:                   0.
% 3.72/0.99  
% 3.72/0.99  ------ QBF
% 3.72/0.99  
% 3.72/0.99  qbf_q_res:                              0
% 3.72/0.99  qbf_num_tautologies:                    0
% 3.72/0.99  qbf_prep_cycles:                        0
% 3.72/0.99  
% 3.72/0.99  ------ BMC1
% 3.72/0.99  
% 3.72/0.99  bmc1_current_bound:                     -1
% 3.72/0.99  bmc1_last_solved_bound:                 -1
% 3.72/0.99  bmc1_unsat_core_size:                   -1
% 3.72/0.99  bmc1_unsat_core_parents_size:           -1
% 3.72/0.99  bmc1_merge_next_fun:                    0
% 3.72/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.72/0.99  
% 3.72/0.99  ------ Instantiation
% 3.72/0.99  
% 3.72/0.99  inst_num_of_clauses:                    1459
% 3.72/0.99  inst_num_in_passive:                    666
% 3.72/0.99  inst_num_in_active:                     650
% 3.72/0.99  inst_num_in_unprocessed:                146
% 3.72/0.99  inst_num_of_loops:                      750
% 3.72/0.99  inst_num_of_learning_restarts:          0
% 3.72/0.99  inst_num_moves_active_passive:          94
% 3.72/0.99  inst_lit_activity:                      0
% 3.72/0.99  inst_lit_activity_moves:                0
% 3.72/0.99  inst_num_tautologies:                   0
% 3.72/0.99  inst_num_prop_implied:                  0
% 3.72/0.99  inst_num_existing_simplified:           0
% 3.72/0.99  inst_num_eq_res_simplified:             0
% 3.72/0.99  inst_num_child_elim:                    0
% 3.72/0.99  inst_num_of_dismatching_blockings:      3343
% 3.72/0.99  inst_num_of_non_proper_insts:           2267
% 3.72/0.99  inst_num_of_duplicates:                 0
% 3.72/0.99  inst_inst_num_from_inst_to_res:         0
% 3.72/0.99  inst_dismatching_checking_time:         0.
% 3.72/0.99  
% 3.72/0.99  ------ Resolution
% 3.72/0.99  
% 3.72/0.99  res_num_of_clauses:                     0
% 3.72/0.99  res_num_in_passive:                     0
% 3.72/0.99  res_num_in_active:                      0
% 3.72/0.99  res_num_of_loops:                       124
% 3.72/0.99  res_forward_subset_subsumed:            217
% 3.72/0.99  res_backward_subset_subsumed:           28
% 3.72/0.99  res_forward_subsumed:                   3
% 3.72/0.99  res_backward_subsumed:                  0
% 3.72/0.99  res_forward_subsumption_resolution:     2
% 3.72/0.99  res_backward_subsumption_resolution:    0
% 3.72/0.99  res_clause_to_clause_subsumption:       3408
% 3.72/0.99  res_orphan_elimination:                 0
% 3.72/0.99  res_tautology_del:                      253
% 3.72/0.99  res_num_eq_res_simplified:              0
% 3.72/0.99  res_num_sel_changes:                    0
% 3.72/0.99  res_moves_from_active_to_pass:          0
% 3.72/0.99  
% 3.72/0.99  ------ Superposition
% 3.72/0.99  
% 3.72/0.99  sup_time_total:                         0.
% 3.72/0.99  sup_time_generating:                    0.
% 3.72/0.99  sup_time_sim_full:                      0.
% 3.72/0.99  sup_time_sim_immed:                     0.
% 3.72/0.99  
% 3.72/0.99  sup_num_of_clauses:                     854
% 3.72/0.99  sup_num_in_active:                      143
% 3.72/0.99  sup_num_in_passive:                     711
% 3.72/0.99  sup_num_of_loops:                       149
% 3.72/0.99  sup_fw_superposition:                   866
% 3.72/0.99  sup_bw_superposition:                   1001
% 3.72/0.99  sup_immediate_simplified:               635
% 3.72/0.99  sup_given_eliminated:                   1
% 3.72/0.99  comparisons_done:                       0
% 3.72/0.99  comparisons_avoided:                    0
% 3.72/0.99  
% 3.72/0.99  ------ Simplifications
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  sim_fw_subset_subsumed:                 22
% 3.72/0.99  sim_bw_subset_subsumed:                 9
% 3.72/0.99  sim_fw_subsumed:                        158
% 3.72/0.99  sim_bw_subsumed:                        6
% 3.72/0.99  sim_fw_subsumption_res:                 0
% 3.72/0.99  sim_bw_subsumption_res:                 0
% 3.72/0.99  sim_tautology_del:                      9
% 3.72/0.99  sim_eq_tautology_del:                   80
% 3.72/0.99  sim_eq_res_simp:                        0
% 3.72/0.99  sim_fw_demodulated:                     226
% 3.72/0.99  sim_bw_demodulated:                     7
% 3.72/0.99  sim_light_normalised:                   292
% 3.72/0.99  sim_joinable_taut:                      0
% 3.72/0.99  sim_joinable_simp:                      0
% 3.72/0.99  sim_ac_normalised:                      0
% 3.72/0.99  sim_smt_subsumption:                    0
% 3.72/0.99  
%------------------------------------------------------------------------------
