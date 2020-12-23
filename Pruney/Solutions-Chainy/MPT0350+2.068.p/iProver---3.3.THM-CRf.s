%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:15 EST 2020

% Result     : Theorem 23.72s
% Output     : CNFRefutation 23.72s
% Verified   : 
% Statistics : Number of formulae       :  267 (381755 expanded)
%              Number of clauses        :  198 (130341 expanded)
%              Number of leaves         :   23 (107417 expanded)
%              Depth                    :   43
%              Number of atoms          :  387 (386234 expanded)
%              Number of equality atoms :  265 (381524 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f37])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f63,f43])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f47,f43,f69])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f69,f70])).

fof(f68,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1056,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1060,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_66243,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1056,c_1060])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1061,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3141,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1061])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3413,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3141,c_32])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1065,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7081,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3413,c_1065])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1069,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8130,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_7081,c_1069])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8310,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_8130,c_0])).

cnf(c_66244,plain,
    ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_66243,c_8310])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1059,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1057,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1431,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k4_subset_1(sK1,sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1057])).

cnf(c_2077,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,X0),k3_xboole_0(k3_subset_1(sK1,X0),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_1431])).

cnf(c_2440,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1056,c_2077])).

cnf(c_4,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1558,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_7])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1435,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(k5_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_1539,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_5,c_1435])).

cnf(c_1546,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1539])).

cnf(c_1567,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1558,c_1546])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1713,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1567,c_9])).

cnf(c_4433,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1713,c_9])).

cnf(c_1715,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1567,c_1539])).

cnf(c_1870,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1715,c_1539])).

cnf(c_1979,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1870,c_9])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1381,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_2208,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1870,c_1381])).

cnf(c_2219,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2208,c_8])).

cnf(c_2341,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2219,c_4])).

cnf(c_4432,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1713,c_2341])).

cnf(c_4448,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_4432])).

cnf(c_5524,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sP0_iProver_split,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1979,c_1979,c_4448])).

cnf(c_5534,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1567,c_5524])).

cnf(c_5554,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5534,c_8])).

cnf(c_5570,plain,
    ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5554,c_1381])).

cnf(c_5571,plain,
    ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5570,c_8])).

cnf(c_5667,plain,
    ( sP0_iProver_split = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5571,c_1567])).

cnf(c_1975,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1870])).

cnf(c_2209,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1975,c_1381])).

cnf(c_2218,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2209,c_8])).

cnf(c_2331,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_2218,c_9])).

cnf(c_6428,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP0_iProver_split,X1),X2)) = k5_xboole_0(X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_2331,c_2331,c_5667])).

cnf(c_6457,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP0_iProver_split,X2),X3))) = k5_xboole_0(k5_xboole_0(X0,X1),X3) ),
    inference(superposition,[status(thm)],[c_6428,c_9])).

cnf(c_6487,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_6457,c_6428])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1070,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8129,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1070,c_1069])).

cnf(c_34329,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(sP0_iProver_split,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_4433,c_4433,c_5667,c_6487,c_8129])).

cnf(c_1987,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1975,c_9])).

cnf(c_6361,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k3_xboole_0(sP0_iProver_split,X0),X1)) = k5_xboole_0(sP0_iProver_split,X1) ),
    inference(light_normalisation,[status(thm)],[c_1987,c_1987,c_5667])).

cnf(c_6379,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),X1)) = k5_xboole_0(sP0_iProver_split,X1) ),
    inference(superposition,[status(thm)],[c_0,c_6361])).

cnf(c_4425,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1567,c_1713])).

cnf(c_4457,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4425,c_8])).

cnf(c_7176,plain,
    ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4457,c_4457,c_5667])).

cnf(c_7181,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_7176,c_5524])).

cnf(c_7182,plain,
    ( k5_xboole_0(sP0_iProver_split,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7181,c_5667,c_7176])).

cnf(c_7380,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_6379,c_7182])).

cnf(c_7409,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),X1),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_7380,c_9])).

cnf(c_7398,plain,
    ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_2218,c_7380])).

cnf(c_7400,plain,
    ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) = k3_xboole_0(sP0_iProver_split,sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_5571,c_7380])).

cnf(c_7179,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(sP0_iProver_split,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7176,c_2341])).

cnf(c_7183,plain,
    ( k3_xboole_0(sP0_iProver_split,sP0_iProver_split) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_7179,c_4448,c_5667])).

cnf(c_7423,plain,
    ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_7400,c_7183])).

cnf(c_7425,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_7398,c_7423])).

cnf(c_7426,plain,
    ( k3_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_7425,c_5667])).

cnf(c_1868,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1715,c_9])).

cnf(c_4634,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1567,c_1868])).

cnf(c_4679,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4634,c_8])).

cnf(c_7188,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(sP0_iProver_split,X0),k3_xboole_0(sP0_iProver_split,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4679,c_4679,c_5667])).

cnf(c_7402,plain,
    ( k3_xboole_0(k3_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)),k3_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split))) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) ),
    inference(superposition,[status(thm)],[c_7188,c_7380])).

cnf(c_7420,plain,
    ( k3_xboole_0(k3_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)),k3_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split))) = k3_xboole_0(X0,sP0_iProver_split) ),
    inference(demodulation,[status(thm)],[c_7402,c_7182])).

cnf(c_7428,plain,
    ( k3_xboole_0(X0,sP0_iProver_split) = k3_xboole_0(sP0_iProver_split,sP0_iProver_split) ),
    inference(demodulation,[status(thm)],[c_7426,c_7420])).

cnf(c_7429,plain,
    ( k3_xboole_0(X0,sP0_iProver_split) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_7428,c_7426])).

cnf(c_7439,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k5_xboole_0(sP0_iProver_split,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7409,c_7429])).

cnf(c_6388,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sP0_iProver_split,X0),X1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sP0_iProver_split,X1)) ),
    inference(superposition,[status(thm)],[c_6361,c_5524])).

cnf(c_6389,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(sP0_iProver_split,X0)) = k5_xboole_0(sP0_iProver_split,X0) ),
    inference(light_normalisation,[status(thm)],[c_6388,c_5667,c_6361])).

cnf(c_7440,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_7439,c_6389,c_6487,c_7182])).

cnf(c_34330,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_34329,c_6487,c_7440])).

cnf(c_34338,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),sK2)) = k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2440,c_34330])).

cnf(c_35756,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_34338,c_2440])).

cnf(c_68020,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)))) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_66244,c_35756])).

cnf(c_68021,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_66244,c_34338])).

cnf(c_8852,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(X0,sK2)) = k3_xboole_0(k5_xboole_0(sK1,X0),sK2) ),
    inference(superposition,[status(thm)],[c_8310,c_4])).

cnf(c_9319,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8852,c_1567])).

cnf(c_9333,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_9319,c_5667])).

cnf(c_68183,plain,
    ( k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK1,sK2),sP0_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_68021,c_9333])).

cnf(c_3164,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2341,c_0])).

cnf(c_1542,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1539])).

cnf(c_4152,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1542])).

cnf(c_6592,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_4152])).

cnf(c_22631,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3164,c_6592])).

cnf(c_2439,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,X0)),k3_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,X0)),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_2077])).

cnf(c_5091,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),k3_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1056,c_2439])).

cnf(c_5102,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),k3_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),sK2)),X0)) = k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),X0) ),
    inference(superposition,[status(thm)],[c_5091,c_9])).

cnf(c_5779,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),k3_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),sK2))) = k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2218,c_5102])).

cnf(c_5793,plain,
    ( k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),k3_xboole_0(sP0_iProver_split,X0)) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_5779,c_5091,c_5667])).

cnf(c_5939,plain,
    ( k3_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_5793,c_3164])).

cnf(c_5100,plain,
    ( k3_xboole_0(k1_xboole_0,k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2)))) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5091,c_3164])).

cnf(c_5104,plain,
    ( k3_xboole_0(k1_xboole_0,k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2)))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_5100,c_4448])).

cnf(c_5943,plain,
    ( k3_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),sP0_iProver_split) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_5939,c_5104,c_5667])).

cnf(c_5942,plain,
    ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),sP0_iProver_split)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_5793,c_1539])).

cnf(c_5944,plain,
    ( k5_xboole_0(sP0_iProver_split,sP0_iProver_split) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_5943,c_5942])).

cnf(c_13977,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1435,c_2219])).

cnf(c_7399,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sP0_iProver_split),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,sP0_iProver_split)))) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) ),
    inference(superposition,[status(thm)],[c_4152,c_7380])).

cnf(c_7448,plain,
    ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_7399,c_5944,c_7429])).

cnf(c_6445,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X2)) ),
    inference(superposition,[status(thm)],[c_2219,c_6428])).

cnf(c_6447,plain,
    ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X1)) = k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) ),
    inference(superposition,[status(thm)],[c_5571,c_6428])).

cnf(c_6491,plain,
    ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6447,c_5571])).

cnf(c_6494,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_6445,c_6491])).

cnf(c_6495,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,sP0_iProver_split)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6494,c_2219,c_5667])).

cnf(c_7449,plain,
    ( k3_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_7448,c_6495])).

cnf(c_14008,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_13977,c_2341,c_5667,c_7449])).

cnf(c_4417,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_1713])).

cnf(c_1437,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_15305,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1437,c_1713])).

cnf(c_15344,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_15305,c_4417,c_5667])).

cnf(c_15345,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_15344,c_4417,c_7182])).

cnf(c_19814,plain,
    ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_4417,c_5667,c_15345])).

cnf(c_19838,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2341,c_19814])).

cnf(c_19904,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_19814,c_5524])).

cnf(c_19971,plain,
    ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_19904,c_5667,c_19814])).

cnf(c_20031,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_19838,c_19971])).

cnf(c_20032,plain,
    ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_20031,c_3164,c_4448,c_5667])).

cnf(c_22742,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_22631,c_4448,c_5667,c_5944,c_14008,c_20032])).

cnf(c_68184,plain,
    ( k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_68183,c_22742])).

cnf(c_68185,plain,
    ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_68020,c_68184])).

cnf(c_2449,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),sK2)),X0)) = k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)),X0) ),
    inference(superposition,[status(thm)],[c_2440,c_9])).

cnf(c_2818,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(k3_subset_1(sK1,sK2),sK2),X0))) = k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)),X0) ),
    inference(superposition,[status(thm)],[c_9,c_2449])).

cnf(c_3671,plain,
    ( k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_subset_1(sK1,sK2),sK2),X0)),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) ),
    inference(superposition,[status(thm)],[c_1539,c_2818])).

cnf(c_3681,plain,
    ( k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_subset_1(sK1,sK2),sK2),X0)),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3671,c_2440])).

cnf(c_68110,plain,
    ( k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),X0)),k3_xboole_0(k5_xboole_0(sK1,sK2),sK2))) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_66244,c_3681])).

cnf(c_5664,plain,
    ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5571,c_1381])).

cnf(c_5685,plain,
    ( k5_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_5664,c_5571,c_5667])).

cnf(c_68121,plain,
    ( k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),sP0_iProver_split) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_68110,c_5685,c_7429,c_7449,c_9333])).

cnf(c_68190,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sP0_iProver_split) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_68185,c_68121])).

cnf(c_68111,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),X0))) = k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),X0) ),
    inference(demodulation,[status(thm)],[c_66244,c_2818])).

cnf(c_68118,plain,
    ( k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),X0) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) ),
    inference(light_normalisation,[status(thm)],[c_68111,c_7182,c_9333])).

cnf(c_34337,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_9,c_34330])).

cnf(c_54752,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k3_xboole_0(X1,X1),X2) ),
    inference(superposition,[status(thm)],[c_1713,c_34337])).

cnf(c_55791,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,X2))) = k5_xboole_0(k3_xboole_0(X1,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_54752,c_5667])).

cnf(c_4435,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X1)) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_1713,c_1381])).

cnf(c_4447,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_4435,c_1381])).

cnf(c_4450,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,X1)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4448,c_4447])).

cnf(c_55792,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_55791,c_4450,c_6487,c_8129])).

cnf(c_68119,plain,
    ( k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),X0) = k5_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_68118,c_6487,c_55792])).

cnf(c_68191,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),X0) = k5_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_68185,c_68119])).

cnf(c_68195,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,sP0_iProver_split) ),
    inference(demodulation,[status(thm)],[c_68190,c_68191])).

cnf(c_4374,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_1546])).

cnf(c_19638,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_4374])).

cnf(c_23403,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK2,sK2)),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_8130,c_19638])).

cnf(c_9307,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,sK1),sK2) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_8310,c_8852])).

cnf(c_8304,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(X0,sK1)) = k3_xboole_0(k5_xboole_0(sK2,X0),sK1) ),
    inference(superposition,[status(thm)],[c_8130,c_4])).

cnf(c_8986,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8304,c_7])).

cnf(c_8307,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_8130,c_1546])).

cnf(c_8997,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_8986,c_5667,c_8307])).

cnf(c_8998,plain,
    ( k5_xboole_0(sK1,sK1) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_8997,c_1567,c_8129])).

cnf(c_9350,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sP0_iProver_split,sK2) ),
    inference(light_normalisation,[status(thm)],[c_9307,c_8998])).

cnf(c_9351,plain,
    ( k5_xboole_0(sK2,sK2) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_9350,c_7449])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3149,plain,
    ( k3_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_2341])).

cnf(c_12172,plain,
    ( k3_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),sP0_iProver_split) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_3149,c_3149,c_4448,c_5667])).

cnf(c_12176,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),sP0_iProver_split) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_14,c_12172])).

cnf(c_12821,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),sP0_iProver_split) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_8130,c_12176])).

cnf(c_8985,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_8304,c_14])).

cnf(c_8308,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_8130,c_14])).

cnf(c_8999,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_8985,c_8307,c_8308])).

cnf(c_12865,plain,
    ( k3_xboole_0(sK1,sP0_iProver_split) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_12821,c_8999])).

cnf(c_12191,plain,
    ( k3_xboole_0(sP0_iProver_split,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_12172,c_0])).

cnf(c_12209,plain,
    ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_14,c_12191])).

cnf(c_13183,plain,
    ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_8130,c_12209])).

cnf(c_13229,plain,
    ( k3_xboole_0(sP0_iProver_split,sK1) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_13183,c_8999])).

cnf(c_23509,plain,
    ( k5_xboole_0(sK1,sP0_iProver_split) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_23403,c_9351,c_12865,c_13229])).

cnf(c_68196,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_68195,c_23509])).

cnf(c_24,negated_conjecture,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1072,plain,
    ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_24,c_19])).

cnf(c_68115,plain,
    ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_66244,c_1072])).

cnf(c_68194,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_68185,c_68115])).

cnf(c_68199,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_68196,c_68194])).

cnf(c_68201,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_68199])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:08:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.72/3.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.72/3.48  
% 23.72/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.72/3.48  
% 23.72/3.48  ------  iProver source info
% 23.72/3.48  
% 23.72/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.72/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.72/3.48  git: non_committed_changes: false
% 23.72/3.48  git: last_make_outside_of_git: false
% 23.72/3.48  
% 23.72/3.48  ------ 
% 23.72/3.48  
% 23.72/3.48  ------ Input Options
% 23.72/3.48  
% 23.72/3.48  --out_options                           all
% 23.72/3.48  --tptp_safe_out                         true
% 23.72/3.48  --problem_path                          ""
% 23.72/3.48  --include_path                          ""
% 23.72/3.48  --clausifier                            res/vclausify_rel
% 23.72/3.48  --clausifier_options                    ""
% 23.72/3.48  --stdin                                 false
% 23.72/3.48  --stats_out                             all
% 23.72/3.48  
% 23.72/3.48  ------ General Options
% 23.72/3.48  
% 23.72/3.48  --fof                                   false
% 23.72/3.48  --time_out_real                         305.
% 23.72/3.48  --time_out_virtual                      -1.
% 23.72/3.48  --symbol_type_check                     false
% 23.72/3.48  --clausify_out                          false
% 23.72/3.48  --sig_cnt_out                           false
% 23.72/3.48  --trig_cnt_out                          false
% 23.72/3.48  --trig_cnt_out_tolerance                1.
% 23.72/3.48  --trig_cnt_out_sk_spl                   false
% 23.72/3.48  --abstr_cl_out                          false
% 23.72/3.48  
% 23.72/3.48  ------ Global Options
% 23.72/3.48  
% 23.72/3.48  --schedule                              default
% 23.72/3.48  --add_important_lit                     false
% 23.72/3.48  --prop_solver_per_cl                    1000
% 23.72/3.48  --min_unsat_core                        false
% 23.72/3.48  --soft_assumptions                      false
% 23.72/3.48  --soft_lemma_size                       3
% 23.72/3.48  --prop_impl_unit_size                   0
% 23.72/3.48  --prop_impl_unit                        []
% 23.72/3.48  --share_sel_clauses                     true
% 23.72/3.48  --reset_solvers                         false
% 23.72/3.48  --bc_imp_inh                            [conj_cone]
% 23.72/3.48  --conj_cone_tolerance                   3.
% 23.72/3.48  --extra_neg_conj                        none
% 23.72/3.48  --large_theory_mode                     true
% 23.72/3.48  --prolific_symb_bound                   200
% 23.72/3.48  --lt_threshold                          2000
% 23.72/3.48  --clause_weak_htbl                      true
% 23.72/3.48  --gc_record_bc_elim                     false
% 23.72/3.48  
% 23.72/3.48  ------ Preprocessing Options
% 23.72/3.48  
% 23.72/3.48  --preprocessing_flag                    true
% 23.72/3.48  --time_out_prep_mult                    0.1
% 23.72/3.48  --splitting_mode                        input
% 23.72/3.48  --splitting_grd                         true
% 23.72/3.48  --splitting_cvd                         false
% 23.72/3.48  --splitting_cvd_svl                     false
% 23.72/3.48  --splitting_nvd                         32
% 23.72/3.48  --sub_typing                            true
% 23.72/3.48  --prep_gs_sim                           true
% 23.72/3.48  --prep_unflatten                        true
% 23.72/3.48  --prep_res_sim                          true
% 23.72/3.48  --prep_upred                            true
% 23.72/3.48  --prep_sem_filter                       exhaustive
% 23.72/3.48  --prep_sem_filter_out                   false
% 23.72/3.48  --pred_elim                             true
% 23.72/3.48  --res_sim_input                         true
% 23.72/3.48  --eq_ax_congr_red                       true
% 23.72/3.48  --pure_diseq_elim                       true
% 23.72/3.48  --brand_transform                       false
% 23.72/3.48  --non_eq_to_eq                          false
% 23.72/3.48  --prep_def_merge                        true
% 23.72/3.48  --prep_def_merge_prop_impl              false
% 23.72/3.48  --prep_def_merge_mbd                    true
% 23.72/3.48  --prep_def_merge_tr_red                 false
% 23.72/3.48  --prep_def_merge_tr_cl                  false
% 23.72/3.48  --smt_preprocessing                     true
% 23.72/3.48  --smt_ac_axioms                         fast
% 23.72/3.48  --preprocessed_out                      false
% 23.72/3.48  --preprocessed_stats                    false
% 23.72/3.48  
% 23.72/3.48  ------ Abstraction refinement Options
% 23.72/3.48  
% 23.72/3.48  --abstr_ref                             []
% 23.72/3.48  --abstr_ref_prep                        false
% 23.72/3.48  --abstr_ref_until_sat                   false
% 23.72/3.48  --abstr_ref_sig_restrict                funpre
% 23.72/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.72/3.48  --abstr_ref_under                       []
% 23.72/3.48  
% 23.72/3.48  ------ SAT Options
% 23.72/3.48  
% 23.72/3.48  --sat_mode                              false
% 23.72/3.48  --sat_fm_restart_options                ""
% 23.72/3.48  --sat_gr_def                            false
% 23.72/3.48  --sat_epr_types                         true
% 23.72/3.48  --sat_non_cyclic_types                  false
% 23.72/3.48  --sat_finite_models                     false
% 23.72/3.48  --sat_fm_lemmas                         false
% 23.72/3.48  --sat_fm_prep                           false
% 23.72/3.48  --sat_fm_uc_incr                        true
% 23.72/3.48  --sat_out_model                         small
% 23.72/3.48  --sat_out_clauses                       false
% 23.72/3.48  
% 23.72/3.48  ------ QBF Options
% 23.72/3.48  
% 23.72/3.48  --qbf_mode                              false
% 23.72/3.48  --qbf_elim_univ                         false
% 23.72/3.48  --qbf_dom_inst                          none
% 23.72/3.48  --qbf_dom_pre_inst                      false
% 23.72/3.48  --qbf_sk_in                             false
% 23.72/3.48  --qbf_pred_elim                         true
% 23.72/3.48  --qbf_split                             512
% 23.72/3.48  
% 23.72/3.48  ------ BMC1 Options
% 23.72/3.48  
% 23.72/3.48  --bmc1_incremental                      false
% 23.72/3.48  --bmc1_axioms                           reachable_all
% 23.72/3.48  --bmc1_min_bound                        0
% 23.72/3.48  --bmc1_max_bound                        -1
% 23.72/3.48  --bmc1_max_bound_default                -1
% 23.72/3.48  --bmc1_symbol_reachability              true
% 23.72/3.48  --bmc1_property_lemmas                  false
% 23.72/3.48  --bmc1_k_induction                      false
% 23.72/3.48  --bmc1_non_equiv_states                 false
% 23.72/3.48  --bmc1_deadlock                         false
% 23.72/3.48  --bmc1_ucm                              false
% 23.72/3.48  --bmc1_add_unsat_core                   none
% 23.72/3.48  --bmc1_unsat_core_children              false
% 23.72/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.72/3.48  --bmc1_out_stat                         full
% 23.72/3.48  --bmc1_ground_init                      false
% 23.72/3.48  --bmc1_pre_inst_next_state              false
% 23.72/3.48  --bmc1_pre_inst_state                   false
% 23.72/3.48  --bmc1_pre_inst_reach_state             false
% 23.72/3.48  --bmc1_out_unsat_core                   false
% 23.72/3.48  --bmc1_aig_witness_out                  false
% 23.72/3.48  --bmc1_verbose                          false
% 23.72/3.48  --bmc1_dump_clauses_tptp                false
% 23.72/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.72/3.48  --bmc1_dump_file                        -
% 23.72/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.72/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.72/3.48  --bmc1_ucm_extend_mode                  1
% 23.72/3.48  --bmc1_ucm_init_mode                    2
% 23.72/3.48  --bmc1_ucm_cone_mode                    none
% 23.72/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.72/3.48  --bmc1_ucm_relax_model                  4
% 23.72/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.72/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.72/3.48  --bmc1_ucm_layered_model                none
% 23.72/3.48  --bmc1_ucm_max_lemma_size               10
% 23.72/3.48  
% 23.72/3.48  ------ AIG Options
% 23.72/3.48  
% 23.72/3.48  --aig_mode                              false
% 23.72/3.48  
% 23.72/3.48  ------ Instantiation Options
% 23.72/3.48  
% 23.72/3.48  --instantiation_flag                    true
% 23.72/3.48  --inst_sos_flag                         true
% 23.72/3.48  --inst_sos_phase                        true
% 23.72/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.72/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.72/3.48  --inst_lit_sel_side                     num_symb
% 23.72/3.48  --inst_solver_per_active                1400
% 23.72/3.48  --inst_solver_calls_frac                1.
% 23.72/3.48  --inst_passive_queue_type               priority_queues
% 23.72/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.72/3.48  --inst_passive_queues_freq              [25;2]
% 23.72/3.48  --inst_dismatching                      true
% 23.72/3.48  --inst_eager_unprocessed_to_passive     true
% 23.72/3.48  --inst_prop_sim_given                   true
% 23.72/3.48  --inst_prop_sim_new                     false
% 23.72/3.48  --inst_subs_new                         false
% 23.72/3.48  --inst_eq_res_simp                      false
% 23.72/3.48  --inst_subs_given                       false
% 23.72/3.48  --inst_orphan_elimination               true
% 23.72/3.48  --inst_learning_loop_flag               true
% 23.72/3.48  --inst_learning_start                   3000
% 23.72/3.48  --inst_learning_factor                  2
% 23.72/3.48  --inst_start_prop_sim_after_learn       3
% 23.72/3.48  --inst_sel_renew                        solver
% 23.72/3.48  --inst_lit_activity_flag                true
% 23.72/3.48  --inst_restr_to_given                   false
% 23.72/3.48  --inst_activity_threshold               500
% 23.72/3.48  --inst_out_proof                        true
% 23.72/3.48  
% 23.72/3.48  ------ Resolution Options
% 23.72/3.48  
% 23.72/3.48  --resolution_flag                       true
% 23.72/3.48  --res_lit_sel                           adaptive
% 23.72/3.48  --res_lit_sel_side                      none
% 23.72/3.48  --res_ordering                          kbo
% 23.72/3.48  --res_to_prop_solver                    active
% 23.72/3.48  --res_prop_simpl_new                    false
% 23.72/3.48  --res_prop_simpl_given                  true
% 23.72/3.48  --res_passive_queue_type                priority_queues
% 23.72/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.72/3.48  --res_passive_queues_freq               [15;5]
% 23.72/3.48  --res_forward_subs                      full
% 23.72/3.48  --res_backward_subs                     full
% 23.72/3.48  --res_forward_subs_resolution           true
% 23.72/3.48  --res_backward_subs_resolution          true
% 23.72/3.48  --res_orphan_elimination                true
% 23.72/3.48  --res_time_limit                        2.
% 23.72/3.48  --res_out_proof                         true
% 23.72/3.48  
% 23.72/3.48  ------ Superposition Options
% 23.72/3.48  
% 23.72/3.48  --superposition_flag                    true
% 23.72/3.48  --sup_passive_queue_type                priority_queues
% 23.72/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.72/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.72/3.48  --demod_completeness_check              fast
% 23.72/3.48  --demod_use_ground                      true
% 23.72/3.48  --sup_to_prop_solver                    passive
% 23.72/3.48  --sup_prop_simpl_new                    true
% 23.72/3.48  --sup_prop_simpl_given                  true
% 23.72/3.48  --sup_fun_splitting                     true
% 23.72/3.48  --sup_smt_interval                      50000
% 23.72/3.48  
% 23.72/3.48  ------ Superposition Simplification Setup
% 23.72/3.48  
% 23.72/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.72/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.72/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.72/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.72/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.72/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.72/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.72/3.48  --sup_immed_triv                        [TrivRules]
% 23.72/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.72/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.72/3.48  --sup_immed_bw_main                     []
% 23.72/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.72/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.72/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.72/3.48  --sup_input_bw                          []
% 23.72/3.48  
% 23.72/3.48  ------ Combination Options
% 23.72/3.48  
% 23.72/3.48  --comb_res_mult                         3
% 23.72/3.48  --comb_sup_mult                         2
% 23.72/3.48  --comb_inst_mult                        10
% 23.72/3.48  
% 23.72/3.48  ------ Debug Options
% 23.72/3.48  
% 23.72/3.48  --dbg_backtrace                         false
% 23.72/3.48  --dbg_dump_prop_clauses                 false
% 23.72/3.48  --dbg_dump_prop_clauses_file            -
% 23.72/3.48  --dbg_out_stat                          false
% 23.72/3.48  ------ Parsing...
% 23.72/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.72/3.48  
% 23.72/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.72/3.48  
% 23.72/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.72/3.48  
% 23.72/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.72/3.48  ------ Proving...
% 23.72/3.48  ------ Problem Properties 
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  clauses                                 25
% 23.72/3.48  conjectures                             2
% 23.72/3.48  EPR                                     6
% 23.72/3.48  Horn                                    22
% 23.72/3.48  unary                                   12
% 23.72/3.48  binary                                  5
% 23.72/3.48  lits                                    46
% 23.72/3.48  lits eq                                 15
% 23.72/3.48  fd_pure                                 0
% 23.72/3.48  fd_pseudo                               0
% 23.72/3.48  fd_cond                                 0
% 23.72/3.48  fd_pseudo_cond                          3
% 23.72/3.48  AC symbols                              0
% 23.72/3.48  
% 23.72/3.48  ------ Schedule dynamic 5 is on 
% 23.72/3.48  
% 23.72/3.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  ------ 
% 23.72/3.48  Current options:
% 23.72/3.48  ------ 
% 23.72/3.48  
% 23.72/3.48  ------ Input Options
% 23.72/3.48  
% 23.72/3.48  --out_options                           all
% 23.72/3.48  --tptp_safe_out                         true
% 23.72/3.48  --problem_path                          ""
% 23.72/3.48  --include_path                          ""
% 23.72/3.48  --clausifier                            res/vclausify_rel
% 23.72/3.48  --clausifier_options                    ""
% 23.72/3.48  --stdin                                 false
% 23.72/3.48  --stats_out                             all
% 23.72/3.48  
% 23.72/3.48  ------ General Options
% 23.72/3.48  
% 23.72/3.48  --fof                                   false
% 23.72/3.48  --time_out_real                         305.
% 23.72/3.48  --time_out_virtual                      -1.
% 23.72/3.48  --symbol_type_check                     false
% 23.72/3.48  --clausify_out                          false
% 23.72/3.48  --sig_cnt_out                           false
% 23.72/3.48  --trig_cnt_out                          false
% 23.72/3.48  --trig_cnt_out_tolerance                1.
% 23.72/3.48  --trig_cnt_out_sk_spl                   false
% 23.72/3.48  --abstr_cl_out                          false
% 23.72/3.48  
% 23.72/3.48  ------ Global Options
% 23.72/3.48  
% 23.72/3.48  --schedule                              default
% 23.72/3.48  --add_important_lit                     false
% 23.72/3.48  --prop_solver_per_cl                    1000
% 23.72/3.48  --min_unsat_core                        false
% 23.72/3.48  --soft_assumptions                      false
% 23.72/3.48  --soft_lemma_size                       3
% 23.72/3.48  --prop_impl_unit_size                   0
% 23.72/3.48  --prop_impl_unit                        []
% 23.72/3.48  --share_sel_clauses                     true
% 23.72/3.48  --reset_solvers                         false
% 23.72/3.48  --bc_imp_inh                            [conj_cone]
% 23.72/3.48  --conj_cone_tolerance                   3.
% 23.72/3.48  --extra_neg_conj                        none
% 23.72/3.48  --large_theory_mode                     true
% 23.72/3.48  --prolific_symb_bound                   200
% 23.72/3.48  --lt_threshold                          2000
% 23.72/3.48  --clause_weak_htbl                      true
% 23.72/3.48  --gc_record_bc_elim                     false
% 23.72/3.48  
% 23.72/3.48  ------ Preprocessing Options
% 23.72/3.48  
% 23.72/3.48  --preprocessing_flag                    true
% 23.72/3.48  --time_out_prep_mult                    0.1
% 23.72/3.48  --splitting_mode                        input
% 23.72/3.48  --splitting_grd                         true
% 23.72/3.48  --splitting_cvd                         false
% 23.72/3.48  --splitting_cvd_svl                     false
% 23.72/3.48  --splitting_nvd                         32
% 23.72/3.48  --sub_typing                            true
% 23.72/3.48  --prep_gs_sim                           true
% 23.72/3.48  --prep_unflatten                        true
% 23.72/3.48  --prep_res_sim                          true
% 23.72/3.48  --prep_upred                            true
% 23.72/3.48  --prep_sem_filter                       exhaustive
% 23.72/3.48  --prep_sem_filter_out                   false
% 23.72/3.48  --pred_elim                             true
% 23.72/3.48  --res_sim_input                         true
% 23.72/3.48  --eq_ax_congr_red                       true
% 23.72/3.48  --pure_diseq_elim                       true
% 23.72/3.48  --brand_transform                       false
% 23.72/3.48  --non_eq_to_eq                          false
% 23.72/3.48  --prep_def_merge                        true
% 23.72/3.48  --prep_def_merge_prop_impl              false
% 23.72/3.48  --prep_def_merge_mbd                    true
% 23.72/3.48  --prep_def_merge_tr_red                 false
% 23.72/3.48  --prep_def_merge_tr_cl                  false
% 23.72/3.48  --smt_preprocessing                     true
% 23.72/3.48  --smt_ac_axioms                         fast
% 23.72/3.48  --preprocessed_out                      false
% 23.72/3.48  --preprocessed_stats                    false
% 23.72/3.48  
% 23.72/3.48  ------ Abstraction refinement Options
% 23.72/3.48  
% 23.72/3.48  --abstr_ref                             []
% 23.72/3.48  --abstr_ref_prep                        false
% 23.72/3.48  --abstr_ref_until_sat                   false
% 23.72/3.48  --abstr_ref_sig_restrict                funpre
% 23.72/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.72/3.48  --abstr_ref_under                       []
% 23.72/3.48  
% 23.72/3.48  ------ SAT Options
% 23.72/3.48  
% 23.72/3.48  --sat_mode                              false
% 23.72/3.48  --sat_fm_restart_options                ""
% 23.72/3.48  --sat_gr_def                            false
% 23.72/3.48  --sat_epr_types                         true
% 23.72/3.48  --sat_non_cyclic_types                  false
% 23.72/3.48  --sat_finite_models                     false
% 23.72/3.48  --sat_fm_lemmas                         false
% 23.72/3.48  --sat_fm_prep                           false
% 23.72/3.48  --sat_fm_uc_incr                        true
% 23.72/3.48  --sat_out_model                         small
% 23.72/3.48  --sat_out_clauses                       false
% 23.72/3.48  
% 23.72/3.48  ------ QBF Options
% 23.72/3.48  
% 23.72/3.48  --qbf_mode                              false
% 23.72/3.48  --qbf_elim_univ                         false
% 23.72/3.48  --qbf_dom_inst                          none
% 23.72/3.48  --qbf_dom_pre_inst                      false
% 23.72/3.48  --qbf_sk_in                             false
% 23.72/3.48  --qbf_pred_elim                         true
% 23.72/3.48  --qbf_split                             512
% 23.72/3.48  
% 23.72/3.48  ------ BMC1 Options
% 23.72/3.48  
% 23.72/3.48  --bmc1_incremental                      false
% 23.72/3.48  --bmc1_axioms                           reachable_all
% 23.72/3.48  --bmc1_min_bound                        0
% 23.72/3.48  --bmc1_max_bound                        -1
% 23.72/3.48  --bmc1_max_bound_default                -1
% 23.72/3.48  --bmc1_symbol_reachability              true
% 23.72/3.48  --bmc1_property_lemmas                  false
% 23.72/3.48  --bmc1_k_induction                      false
% 23.72/3.48  --bmc1_non_equiv_states                 false
% 23.72/3.48  --bmc1_deadlock                         false
% 23.72/3.48  --bmc1_ucm                              false
% 23.72/3.48  --bmc1_add_unsat_core                   none
% 23.72/3.48  --bmc1_unsat_core_children              false
% 23.72/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.72/3.48  --bmc1_out_stat                         full
% 23.72/3.48  --bmc1_ground_init                      false
% 23.72/3.48  --bmc1_pre_inst_next_state              false
% 23.72/3.48  --bmc1_pre_inst_state                   false
% 23.72/3.48  --bmc1_pre_inst_reach_state             false
% 23.72/3.48  --bmc1_out_unsat_core                   false
% 23.72/3.48  --bmc1_aig_witness_out                  false
% 23.72/3.48  --bmc1_verbose                          false
% 23.72/3.48  --bmc1_dump_clauses_tptp                false
% 23.72/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.72/3.48  --bmc1_dump_file                        -
% 23.72/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.72/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.72/3.48  --bmc1_ucm_extend_mode                  1
% 23.72/3.48  --bmc1_ucm_init_mode                    2
% 23.72/3.48  --bmc1_ucm_cone_mode                    none
% 23.72/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.72/3.48  --bmc1_ucm_relax_model                  4
% 23.72/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.72/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.72/3.48  --bmc1_ucm_layered_model                none
% 23.72/3.48  --bmc1_ucm_max_lemma_size               10
% 23.72/3.48  
% 23.72/3.48  ------ AIG Options
% 23.72/3.48  
% 23.72/3.48  --aig_mode                              false
% 23.72/3.48  
% 23.72/3.48  ------ Instantiation Options
% 23.72/3.48  
% 23.72/3.48  --instantiation_flag                    true
% 23.72/3.48  --inst_sos_flag                         true
% 23.72/3.48  --inst_sos_phase                        true
% 23.72/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.72/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.72/3.48  --inst_lit_sel_side                     none
% 23.72/3.48  --inst_solver_per_active                1400
% 23.72/3.48  --inst_solver_calls_frac                1.
% 23.72/3.48  --inst_passive_queue_type               priority_queues
% 23.72/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.72/3.48  --inst_passive_queues_freq              [25;2]
% 23.72/3.48  --inst_dismatching                      true
% 23.72/3.48  --inst_eager_unprocessed_to_passive     true
% 23.72/3.48  --inst_prop_sim_given                   true
% 23.72/3.48  --inst_prop_sim_new                     false
% 23.72/3.48  --inst_subs_new                         false
% 23.72/3.48  --inst_eq_res_simp                      false
% 23.72/3.48  --inst_subs_given                       false
% 23.72/3.48  --inst_orphan_elimination               true
% 23.72/3.48  --inst_learning_loop_flag               true
% 23.72/3.48  --inst_learning_start                   3000
% 23.72/3.48  --inst_learning_factor                  2
% 23.72/3.48  --inst_start_prop_sim_after_learn       3
% 23.72/3.48  --inst_sel_renew                        solver
% 23.72/3.48  --inst_lit_activity_flag                true
% 23.72/3.48  --inst_restr_to_given                   false
% 23.72/3.48  --inst_activity_threshold               500
% 23.72/3.48  --inst_out_proof                        true
% 23.72/3.48  
% 23.72/3.48  ------ Resolution Options
% 23.72/3.48  
% 23.72/3.48  --resolution_flag                       false
% 23.72/3.48  --res_lit_sel                           adaptive
% 23.72/3.48  --res_lit_sel_side                      none
% 23.72/3.48  --res_ordering                          kbo
% 23.72/3.48  --res_to_prop_solver                    active
% 23.72/3.48  --res_prop_simpl_new                    false
% 23.72/3.48  --res_prop_simpl_given                  true
% 23.72/3.48  --res_passive_queue_type                priority_queues
% 23.72/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.72/3.48  --res_passive_queues_freq               [15;5]
% 23.72/3.48  --res_forward_subs                      full
% 23.72/3.48  --res_backward_subs                     full
% 23.72/3.48  --res_forward_subs_resolution           true
% 23.72/3.48  --res_backward_subs_resolution          true
% 23.72/3.48  --res_orphan_elimination                true
% 23.72/3.48  --res_time_limit                        2.
% 23.72/3.48  --res_out_proof                         true
% 23.72/3.48  
% 23.72/3.48  ------ Superposition Options
% 23.72/3.48  
% 23.72/3.48  --superposition_flag                    true
% 23.72/3.48  --sup_passive_queue_type                priority_queues
% 23.72/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.72/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.72/3.48  --demod_completeness_check              fast
% 23.72/3.48  --demod_use_ground                      true
% 23.72/3.48  --sup_to_prop_solver                    passive
% 23.72/3.48  --sup_prop_simpl_new                    true
% 23.72/3.48  --sup_prop_simpl_given                  true
% 23.72/3.48  --sup_fun_splitting                     true
% 23.72/3.48  --sup_smt_interval                      50000
% 23.72/3.48  
% 23.72/3.48  ------ Superposition Simplification Setup
% 23.72/3.48  
% 23.72/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.72/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.72/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.72/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.72/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.72/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.72/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.72/3.48  --sup_immed_triv                        [TrivRules]
% 23.72/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.72/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.72/3.48  --sup_immed_bw_main                     []
% 23.72/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.72/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.72/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.72/3.48  --sup_input_bw                          []
% 23.72/3.48  
% 23.72/3.48  ------ Combination Options
% 23.72/3.48  
% 23.72/3.48  --comb_res_mult                         3
% 23.72/3.48  --comb_sup_mult                         2
% 23.72/3.48  --comb_inst_mult                        10
% 23.72/3.48  
% 23.72/3.48  ------ Debug Options
% 23.72/3.48  
% 23.72/3.48  --dbg_backtrace                         false
% 23.72/3.48  --dbg_dump_prop_clauses                 false
% 23.72/3.48  --dbg_dump_prop_clauses_file            -
% 23.72/3.48  --dbg_out_stat                          false
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  ------ Proving...
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  % SZS status Theorem for theBenchmark.p
% 23.72/3.48  
% 23.72/3.48   Resolution empty clause
% 23.72/3.48  
% 23.72/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.72/3.48  
% 23.72/3.48  fof(f21,conjecture,(
% 23.72/3.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f22,negated_conjecture,(
% 23.72/3.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 23.72/3.48    inference(negated_conjecture,[],[f21])).
% 23.72/3.48  
% 23.72/3.48  fof(f29,plain,(
% 23.72/3.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.72/3.48    inference(ennf_transformation,[],[f22])).
% 23.72/3.48  
% 23.72/3.48  fof(f37,plain,(
% 23.72/3.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 23.72/3.48    introduced(choice_axiom,[])).
% 23.72/3.48  
% 23.72/3.48  fof(f38,plain,(
% 23.72/3.48    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 23.72/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f37])).
% 23.72/3.48  
% 23.72/3.48  fof(f67,plain,(
% 23.72/3.48    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 23.72/3.48    inference(cnf_transformation,[],[f38])).
% 23.72/3.48  
% 23.72/3.48  fof(f17,axiom,(
% 23.72/3.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f25,plain,(
% 23.72/3.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.72/3.48    inference(ennf_transformation,[],[f17])).
% 23.72/3.48  
% 23.72/3.48  fof(f63,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f25])).
% 23.72/3.48  
% 23.72/3.48  fof(f3,axiom,(
% 23.72/3.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f43,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f3])).
% 23.72/3.48  
% 23.72/3.48  fof(f74,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.72/3.48    inference(definition_unfolding,[],[f63,f43])).
% 23.72/3.48  
% 23.72/3.48  fof(f15,axiom,(
% 23.72/3.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f24,plain,(
% 23.72/3.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 23.72/3.48    inference(ennf_transformation,[],[f15])).
% 23.72/3.48  
% 23.72/3.48  fof(f36,plain,(
% 23.72/3.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 23.72/3.48    inference(nnf_transformation,[],[f24])).
% 23.72/3.48  
% 23.72/3.48  fof(f58,plain,(
% 23.72/3.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f36])).
% 23.72/3.48  
% 23.72/3.48  fof(f19,axiom,(
% 23.72/3.48    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f65,plain,(
% 23.72/3.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f19])).
% 23.72/3.48  
% 23.72/3.48  fof(f13,axiom,(
% 23.72/3.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f32,plain,(
% 23.72/3.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.72/3.48    inference(nnf_transformation,[],[f13])).
% 23.72/3.48  
% 23.72/3.48  fof(f33,plain,(
% 23.72/3.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.72/3.48    inference(rectify,[],[f32])).
% 23.72/3.48  
% 23.72/3.48  fof(f34,plain,(
% 23.72/3.48    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 23.72/3.48    introduced(choice_axiom,[])).
% 23.72/3.48  
% 23.72/3.48  fof(f35,plain,(
% 23.72/3.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.72/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 23.72/3.48  
% 23.72/3.48  fof(f53,plain,(
% 23.72/3.48    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 23.72/3.48    inference(cnf_transformation,[],[f35])).
% 23.72/3.48  
% 23.72/3.48  fof(f79,plain,(
% 23.72/3.48    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 23.72/3.48    inference(equality_resolution,[],[f53])).
% 23.72/3.48  
% 23.72/3.48  fof(f6,axiom,(
% 23.72/3.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f23,plain,(
% 23.72/3.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.72/3.48    inference(ennf_transformation,[],[f6])).
% 23.72/3.48  
% 23.72/3.48  fof(f46,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f23])).
% 23.72/3.48  
% 23.72/3.48  fof(f1,axiom,(
% 23.72/3.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f39,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f1])).
% 23.72/3.48  
% 23.72/3.48  fof(f18,axiom,(
% 23.72/3.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f26,plain,(
% 23.72/3.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.72/3.48    inference(ennf_transformation,[],[f18])).
% 23.72/3.48  
% 23.72/3.48  fof(f64,plain,(
% 23.72/3.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f26])).
% 23.72/3.48  
% 23.72/3.48  fof(f20,axiom,(
% 23.72/3.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f27,plain,(
% 23.72/3.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 23.72/3.48    inference(ennf_transformation,[],[f20])).
% 23.72/3.48  
% 23.72/3.48  fof(f28,plain,(
% 23.72/3.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.72/3.48    inference(flattening,[],[f27])).
% 23.72/3.48  
% 23.72/3.48  fof(f66,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f28])).
% 23.72/3.48  
% 23.72/3.48  fof(f10,axiom,(
% 23.72/3.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f50,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f10])).
% 23.72/3.48  
% 23.72/3.48  fof(f69,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 23.72/3.48    inference(definition_unfolding,[],[f50,f43])).
% 23.72/3.48  
% 23.72/3.48  fof(f75,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.72/3.48    inference(definition_unfolding,[],[f66,f69])).
% 23.72/3.48  
% 23.72/3.48  fof(f4,axiom,(
% 23.72/3.48    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f44,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f4])).
% 23.72/3.48  
% 23.72/3.48  fof(f7,axiom,(
% 23.72/3.48    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f47,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 23.72/3.48    inference(cnf_transformation,[],[f7])).
% 23.72/3.48  
% 23.72/3.48  fof(f72,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 23.72/3.48    inference(definition_unfolding,[],[f47,f43,f69])).
% 23.72/3.48  
% 23.72/3.48  fof(f5,axiom,(
% 23.72/3.48    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f45,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 23.72/3.48    inference(cnf_transformation,[],[f5])).
% 23.72/3.48  
% 23.72/3.48  fof(f71,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) )),
% 23.72/3.48    inference(definition_unfolding,[],[f45,f69])).
% 23.72/3.48  
% 23.72/3.48  fof(f9,axiom,(
% 23.72/3.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f49,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f9])).
% 23.72/3.48  
% 23.72/3.48  fof(f8,axiom,(
% 23.72/3.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f48,plain,(
% 23.72/3.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.72/3.48    inference(cnf_transformation,[],[f8])).
% 23.72/3.48  
% 23.72/3.48  fof(f2,axiom,(
% 23.72/3.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f30,plain,(
% 23.72/3.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.72/3.48    inference(nnf_transformation,[],[f2])).
% 23.72/3.48  
% 23.72/3.48  fof(f31,plain,(
% 23.72/3.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.72/3.48    inference(flattening,[],[f30])).
% 23.72/3.48  
% 23.72/3.48  fof(f40,plain,(
% 23.72/3.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.72/3.48    inference(cnf_transformation,[],[f31])).
% 23.72/3.48  
% 23.72/3.48  fof(f77,plain,(
% 23.72/3.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.72/3.48    inference(equality_resolution,[],[f40])).
% 23.72/3.48  
% 23.72/3.48  fof(f14,axiom,(
% 23.72/3.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f57,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 23.72/3.48    inference(cnf_transformation,[],[f14])).
% 23.72/3.48  
% 23.72/3.48  fof(f11,axiom,(
% 23.72/3.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f51,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f11])).
% 23.72/3.48  
% 23.72/3.48  fof(f12,axiom,(
% 23.72/3.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f52,plain,(
% 23.72/3.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.72/3.48    inference(cnf_transformation,[],[f12])).
% 23.72/3.48  
% 23.72/3.48  fof(f70,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.72/3.48    inference(definition_unfolding,[],[f51,f52])).
% 23.72/3.48  
% 23.72/3.48  fof(f73,plain,(
% 23.72/3.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 23.72/3.48    inference(definition_unfolding,[],[f57,f69,f70])).
% 23.72/3.48  
% 23.72/3.48  fof(f68,plain,(
% 23.72/3.48    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))),
% 23.72/3.48    inference(cnf_transformation,[],[f38])).
% 23.72/3.48  
% 23.72/3.48  fof(f16,axiom,(
% 23.72/3.48    ! [X0] : k2_subset_1(X0) = X0),
% 23.72/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.72/3.48  
% 23.72/3.48  fof(f62,plain,(
% 23.72/3.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 23.72/3.48    inference(cnf_transformation,[],[f16])).
% 23.72/3.48  
% 23.72/3.48  cnf(c_25,negated_conjecture,
% 23.72/3.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 23.72/3.48      inference(cnf_transformation,[],[f67]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1056,plain,
% 23.72/3.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_20,plain,
% 23.72/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.72/3.48      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 23.72/3.48      inference(cnf_transformation,[],[f74]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1060,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 23.72/3.48      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_66243,plain,
% 23.72/3.48      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1056,c_1060]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_18,plain,
% 23.72/3.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.72/3.48      inference(cnf_transformation,[],[f58]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1061,plain,
% 23.72/3.48      ( m1_subset_1(X0,X1) != iProver_top
% 23.72/3.48      | r2_hidden(X0,X1) = iProver_top
% 23.72/3.48      | v1_xboole_0(X1) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_3141,plain,
% 23.72/3.48      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 23.72/3.48      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1056,c_1061]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_22,plain,
% 23.72/3.48      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 23.72/3.48      inference(cnf_transformation,[],[f65]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_30,plain,
% 23.72/3.48      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_32,plain,
% 23.72/3.48      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 23.72/3.48      inference(instantiation,[status(thm)],[c_30]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_3413,plain,
% 23.72/3.48      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.72/3.48      inference(global_propositional_subsumption,[status(thm)],[c_3141,c_32]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_13,plain,
% 23.72/3.48      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.72/3.48      inference(cnf_transformation,[],[f79]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1065,plain,
% 23.72/3.48      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.72/3.48      | r1_tarski(X0,X1) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7081,plain,
% 23.72/3.48      ( r1_tarski(sK2,sK1) = iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_3413,c_1065]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6,plain,
% 23.72/3.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.72/3.48      inference(cnf_transformation,[],[f46]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1069,plain,
% 23.72/3.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8130,plain,
% 23.72/3.48      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_7081,c_1069]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_0,plain,
% 23.72/3.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.72/3.48      inference(cnf_transformation,[],[f39]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8310,plain,
% 23.72/3.48      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8130,c_0]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_66244,plain,
% 23.72/3.48      ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_66243,c_8310]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_21,plain,
% 23.72/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.72/3.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 23.72/3.48      inference(cnf_transformation,[],[f64]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1059,plain,
% 23.72/3.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.72/3.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_23,plain,
% 23.72/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.72/3.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.72/3.48      | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) = k4_subset_1(X1,X0,X2) ),
% 23.72/3.48      inference(cnf_transformation,[],[f75]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1057,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
% 23.72/3.48      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 23.72/3.48      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1431,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k4_subset_1(sK1,sK2,X0)
% 23.72/3.48      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1056,c_1057]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2077,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,X0),k3_xboole_0(k3_subset_1(sK1,X0),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,X0))
% 23.72/3.48      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1059,c_1431]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2440,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1056,c_2077]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4,plain,
% 23.72/3.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
% 23.72/3.48      inference(cnf_transformation,[],[f44]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 23.72/3.48      inference(cnf_transformation,[],[f72]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1558,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) = k1_xboole_0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_4,c_7]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
% 23.72/3.48      inference(cnf_transformation,[],[f71]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1435,plain,
% 23.72/3.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(k5_xboole_0(X1,X2),X0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1539,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),X0)) = X0 ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_5,c_1435]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1546,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)) = X0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_0,c_1539]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1567,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_1558,c_1546]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_9,plain,
% 23.72/3.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.72/3.48      inference(cnf_transformation,[],[f49]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1713,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1567,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4433,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1713,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1715,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1567,c_1539]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1870,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1715,c_1539]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1979,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1870,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.72/3.48      inference(cnf_transformation,[],[f48]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1381,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2208,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1870,c_1381]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2219,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_2208,c_8]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2341,plain,
% 23.72/3.48      ( k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_2219,c_4]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4432,plain,
% 23.72/3.48      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1713,c_2341]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4448,plain,
% 23.72/3.48      ( k3_xboole_0(X0,k1_xboole_0) = sP0_iProver_split ),
% 23.72/3.48      inference(splitting,
% 23.72/3.48                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 23.72/3.48                [c_4432]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5524,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sP0_iProver_split,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_1979,c_1979,c_4448]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5534,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1567,c_5524]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5554,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = k1_xboole_0 ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_5534,c_8]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5570,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = k5_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_5554,c_1381]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5571,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_5570,c_8]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5667,plain,
% 23.72/3.48      ( sP0_iProver_split = k1_xboole_0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_5571,c_1567]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1975,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_0,c_1870]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2209,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1975,c_1381]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2218,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_2209,c_8]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2331,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)) = k5_xboole_0(X0,X2) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_2218,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6428,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP0_iProver_split,X1),X2)) = k5_xboole_0(X0,X2) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_2331,c_2331,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6457,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP0_iProver_split,X2),X3))) = k5_xboole_0(k5_xboole_0(X0,X1),X3) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_6428,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6487,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_6457,c_6428]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f77]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1070,plain,
% 23.72/3.48      ( r1_tarski(X0,X0) = iProver_top ),
% 23.72/3.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8129,plain,
% 23.72/3.48      ( k3_xboole_0(X0,X0) = X0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1070,c_1069]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_34329,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(sP0_iProver_split,X1),X2) ),
% 23.72/3.48      inference(light_normalisation,
% 23.72/3.48                [status(thm)],
% 23.72/3.48                [c_4433,c_4433,c_5667,c_6487,c_8129]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1987,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1975,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6361,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k3_xboole_0(sP0_iProver_split,X0),X1)) = k5_xboole_0(sP0_iProver_split,X1) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_1987,c_1987,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6379,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),X1)) = k5_xboole_0(sP0_iProver_split,X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_0,c_6361]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4425,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) = k5_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1567,c_1713]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4457,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_4425,c_8]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7176,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_4457,c_4457,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7181,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_7176,c_5524]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7182,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,X0) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_7181,c_5667,c_7176]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7380,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),X1)) = X1 ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_6379,c_7182]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7409,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),X1),X2)) = k5_xboole_0(X1,X2) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_7380,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7398,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) = k3_xboole_0(k1_xboole_0,X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_2218,c_7380]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7400,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) = k3_xboole_0(sP0_iProver_split,sP0_iProver_split) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_5571,c_7380]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7179,plain,
% 23.72/3.48      ( k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(sP0_iProver_split,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_7176,c_2341]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7183,plain,
% 23.72/3.48      ( k3_xboole_0(sP0_iProver_split,sP0_iProver_split) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_7179,c_4448,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7423,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_7400,c_7183]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7425,plain,
% 23.72/3.48      ( k3_xboole_0(k1_xboole_0,X0) = sP0_iProver_split ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_7398,c_7423]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7426,plain,
% 23.72/3.48      ( k3_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_7425,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1868,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) = k5_xboole_0(X0,X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1715,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4634,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1567,c_1868]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4679,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_4634,c_8]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7188,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(sP0_iProver_split,X0),k3_xboole_0(sP0_iProver_split,X0))) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_4679,c_4679,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7402,plain,
% 23.72/3.48      ( k3_xboole_0(k3_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)),k3_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split))) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_7188,c_7380]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7420,plain,
% 23.72/3.48      ( k3_xboole_0(k3_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)),k3_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split))) = k3_xboole_0(X0,sP0_iProver_split) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_7402,c_7182]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7428,plain,
% 23.72/3.48      ( k3_xboole_0(X0,sP0_iProver_split) = k3_xboole_0(sP0_iProver_split,sP0_iProver_split) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_7426,c_7420]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7429,plain,
% 23.72/3.48      ( k3_xboole_0(X0,sP0_iProver_split) = sP0_iProver_split ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_7428,c_7426]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7439,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(k5_xboole_0(sP0_iProver_split,X0),X1)) = k5_xboole_0(X0,X1) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_7409,c_7429]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6388,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(sP0_iProver_split,X0),X1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sP0_iProver_split,X1)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_6361,c_5524]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6389,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(sP0_iProver_split,X0)) = k5_xboole_0(sP0_iProver_split,X0) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_6388,c_5667,c_6361]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7440,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_7439,c_6389,c_6487,c_7182]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_34330,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_34329,c_6487,c_7440]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_34338,plain,
% 23.72/3.48      ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),sK2)) = k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_2440,c_34330]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_35756,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_34338,c_2440]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68020,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)))) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_66244,c_35756]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68021,plain,
% 23.72/3.48      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2))) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_66244,c_34338]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8852,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k3_xboole_0(X0,sK2)) = k3_xboole_0(k5_xboole_0(sK1,X0),sK2) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8310,c_4]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_9319,plain,
% 23.72/3.48      ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = k1_xboole_0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8852,c_1567]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_9333,plain,
% 23.72/3.48      ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_9319,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68183,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK1,sK2),sP0_iProver_split) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_68021,c_9333]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_3164,plain,
% 23.72/3.48      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_2341,c_0]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1542,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_0,c_1539]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4152,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_0,c_1542]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6592,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = X0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_4,c_4152]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_22631,plain,
% 23.72/3.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_3164,c_6592]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2439,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,X0)),k3_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,X0)),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,X0)))
% 23.72/3.48      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1059,c_2077]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5091,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),k3_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1056,c_2439]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5102,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),k3_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),sK2)),X0)) = k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),X0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_5091,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5779,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),k3_xboole_0(k3_subset_1(sK1,k3_subset_1(sK1,sK2)),sK2))) = k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),k3_xboole_0(k1_xboole_0,X0)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_2218,c_5102]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5793,plain,
% 23.72/3.48      ( k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),k3_xboole_0(sP0_iProver_split,X0)) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_5779,c_5091,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5939,plain,
% 23.72/3.48      ( k3_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2)))) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_5793,c_3164]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5100,plain,
% 23.72/3.48      ( k3_xboole_0(k1_xboole_0,k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2)))) = k3_xboole_0(sK2,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_5091,c_3164]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5104,plain,
% 23.72/3.48      ( k3_xboole_0(k1_xboole_0,k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2)))) = sP0_iProver_split ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_5100,c_4448]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5943,plain,
% 23.72/3.48      ( k3_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),sP0_iProver_split) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_5939,c_5104,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5942,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,k3_subset_1(sK1,sK2))),sP0_iProver_split)) = sP0_iProver_split ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_5793,c_1539]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5944,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,sP0_iProver_split) = sP0_iProver_split ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_5943,c_5942]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_13977,plain,
% 23.72/3.48      ( k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1435,c_2219]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7399,plain,
% 23.72/3.48      ( k3_xboole_0(k3_xboole_0(X0,sP0_iProver_split),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,sP0_iProver_split)))) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,sP0_iProver_split)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_4152,c_7380]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7448,plain,
% 23.72/3.48      ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split))) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_7399,c_5944,c_7429]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6445,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X2)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_2219,c_6428]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6447,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X1)) = k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_5571,c_6428]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6491,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X1)) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_6447,c_5571]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6494,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = X0 ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_6445,c_6491]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_6495,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(X1,sP0_iProver_split)) = X0 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_6494,c_2219,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_7449,plain,
% 23.72/3.48      ( k3_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_7448,c_6495]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_14008,plain,
% 23.72/3.48      ( k3_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,
% 23.72/3.48                [status(thm)],
% 23.72/3.48                [c_13977,c_2341,c_5667,c_7449]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4417,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_4,c_1713]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1437,plain,
% 23.72/3.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_15305,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1437,c_1713]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_15344,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,X1)) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_15305,c_4417,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_15345,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k3_xboole_0(X0,X1) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_15344,c_4417,c_7182]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_19814,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_4417,c_5667,c_15345]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_19838,plain,
% 23.72/3.48      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,k1_xboole_0)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_2341,c_19814]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_19904,plain,
% 23.72/3.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_19814,c_5524]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_19971,plain,
% 23.72/3.48      ( k5_xboole_0(sP0_iProver_split,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_19904,c_5667,c_19814]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_20031,plain,
% 23.72/3.48      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_19838,c_19971]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_20032,plain,
% 23.72/3.48      ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1)) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,
% 23.72/3.48                [status(thm)],
% 23.72/3.48                [c_20031,c_3164,c_4448,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_22742,plain,
% 23.72/3.48      ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split) = k5_xboole_0(X0,X1) ),
% 23.72/3.48      inference(light_normalisation,
% 23.72/3.48                [status(thm)],
% 23.72/3.48                [c_22631,c_4448,c_5667,c_5944,c_14008,c_20032]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68184,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_68183,c_22742]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68185,plain,
% 23.72/3.48      ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_68020,c_68184]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2449,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),sK2)),X0)) = k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)),X0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_2440,c_9]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_2818,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(k3_subset_1(sK1,sK2),sK2),X0))) = k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)),X0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_9,c_2449]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_3671,plain,
% 23.72/3.48      ( k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_subset_1(sK1,sK2),sK2),X0)),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k5_xboole_0(sK2,k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1539,c_2818]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_3681,plain,
% 23.72/3.48      ( k5_xboole_0(k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_subset_1(sK1,sK2),sK2),X0)),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_3671,c_2440]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68110,plain,
% 23.72/3.48      ( k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),X0)),k3_xboole_0(k5_xboole_0(sK1,sK2),sK2))) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_66244,c_3681]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5664,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,sP0_iProver_split)) = k5_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_5571,c_1381]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_5685,plain,
% 23.72/3.48      ( k5_xboole_0(X0,sP0_iProver_split) = X0 ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_5664,c_5571,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68121,plain,
% 23.72/3.48      ( k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),sP0_iProver_split) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
% 23.72/3.48      inference(light_normalisation,
% 23.72/3.48                [status(thm)],
% 23.72/3.48                [c_68110,c_5685,c_7429,c_7449,c_9333]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68190,plain,
% 23.72/3.48      ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sP0_iProver_split) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_68185,c_68121]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68111,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),X0))) = k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),X0) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_66244,c_2818]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68118,plain,
% 23.72/3.48      ( k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),X0) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_68111,c_7182,c_9333]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_34337,plain,
% 23.72/3.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X2,X3) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_9,c_34330]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_54752,plain,
% 23.72/3.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k3_xboole_0(X1,X1),X2) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1713,c_34337]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_55791,plain,
% 23.72/3.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,X2))) = k5_xboole_0(k3_xboole_0(X1,X1),X2) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_54752,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4435,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X1)) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_1713,c_1381]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4447,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_4435,c_1381]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4450,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,X1)) = k5_xboole_0(X0,X1) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_4448,c_4447]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_55792,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_55791,c_4450,c_6487,c_8129]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68119,plain,
% 23.72/3.48      ( k5_xboole_0(k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)),X0) = k5_xboole_0(sK1,X0) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_68118,c_6487,c_55792]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68191,plain,
% 23.72/3.48      ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),X0) = k5_xboole_0(sK1,X0) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_68185,c_68119]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68195,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,sP0_iProver_split) ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_68190,c_68191]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_4374,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0),X0)) = X0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_4,c_1546]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_19638,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X0)) = X0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_0,c_4374]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_23403,plain,
% 23.72/3.48      ( k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK2,sK2)),sK1)) = sK1 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8130,c_19638]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_9307,plain,
% 23.72/3.48      ( k3_xboole_0(k5_xboole_0(sK1,sK1),sK2) = k5_xboole_0(sK2,sK2) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8310,c_8852]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8304,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k3_xboole_0(X0,sK1)) = k3_xboole_0(k5_xboole_0(sK2,X0),sK1) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8130,c_4]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8986,plain,
% 23.72/3.48      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)))) = k1_xboole_0 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8304,c_7]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8307,plain,
% 23.72/3.48      ( k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)) = sK1 ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8130,c_1546]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8997,plain,
% 23.72/3.48      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_8986,c_5667,c_8307]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8998,plain,
% 23.72/3.48      ( k5_xboole_0(sK1,sK1) = sP0_iProver_split ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_8997,c_1567,c_8129]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_9350,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sP0_iProver_split,sK2) ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_9307,c_8998]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_9351,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,sK2) = sP0_iProver_split ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_9350,c_7449]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_14,plain,
% 23.72/3.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 23.72/3.48      inference(cnf_transformation,[],[f73]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_3149,plain,
% 23.72/3.48      ( k3_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_14,c_2341]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_12172,plain,
% 23.72/3.48      ( k3_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),sP0_iProver_split) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,
% 23.72/3.48                [status(thm)],
% 23.72/3.48                [c_3149,c_3149,c_4448,c_5667]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_12176,plain,
% 23.72/3.48      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),sP0_iProver_split) = sP0_iProver_split ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_14,c_12172]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_12821,plain,
% 23.72/3.48      ( k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),sP0_iProver_split) = sP0_iProver_split ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8130,c_12176]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8985,plain,
% 23.72/3.48      ( k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8304,c_14]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8308,plain,
% 23.72/3.48      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8130,c_14]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_8999,plain,
% 23.72/3.48      ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = sK1 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_8985,c_8307,c_8308]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_12865,plain,
% 23.72/3.48      ( k3_xboole_0(sK1,sP0_iProver_split) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_12821,c_8999]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_12191,plain,
% 23.72/3.48      ( k3_xboole_0(sP0_iProver_split,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = sP0_iProver_split ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_12172,c_0]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_12209,plain,
% 23.72/3.48      ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = sP0_iProver_split ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_14,c_12191]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_13183,plain,
% 23.72/3.48      ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) = sP0_iProver_split ),
% 23.72/3.48      inference(superposition,[status(thm)],[c_8130,c_12209]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_13229,plain,
% 23.72/3.48      ( k3_xboole_0(sP0_iProver_split,sK1) = sP0_iProver_split ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_13183,c_8999]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_23509,plain,
% 23.72/3.48      ( k5_xboole_0(sK1,sP0_iProver_split) = sK1 ),
% 23.72/3.48      inference(light_normalisation,
% 23.72/3.48                [status(thm)],
% 23.72/3.48                [c_23403,c_9351,c_12865,c_13229]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68196,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
% 23.72/3.48      inference(light_normalisation,[status(thm)],[c_68195,c_23509]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_24,negated_conjecture,
% 23.72/3.48      ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
% 23.72/3.48      inference(cnf_transformation,[],[f68]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_19,plain,
% 23.72/3.48      ( k2_subset_1(X0) = X0 ),
% 23.72/3.48      inference(cnf_transformation,[],[f62]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_1072,plain,
% 23.72/3.48      ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_24,c_19]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68115,plain,
% 23.72/3.48      ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) != sK1 ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_66244,c_1072]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68194,plain,
% 23.72/3.48      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) != sK1 ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_68185,c_68115]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68199,plain,
% 23.72/3.48      ( sK1 != sK1 ),
% 23.72/3.48      inference(demodulation,[status(thm)],[c_68196,c_68194]) ).
% 23.72/3.48  
% 23.72/3.48  cnf(c_68201,plain,
% 23.72/3.48      ( $false ),
% 23.72/3.48      inference(equality_resolution_simp,[status(thm)],[c_68199]) ).
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.72/3.48  
% 23.72/3.48  ------                               Statistics
% 23.72/3.48  
% 23.72/3.48  ------ General
% 23.72/3.48  
% 23.72/3.48  abstr_ref_over_cycles:                  0
% 23.72/3.48  abstr_ref_under_cycles:                 0
% 23.72/3.48  gc_basic_clause_elim:                   0
% 23.72/3.48  forced_gc_time:                         0
% 23.72/3.48  parsing_time:                           0.007
% 23.72/3.48  unif_index_cands_time:                  0.
% 23.72/3.48  unif_index_add_time:                    0.
% 23.72/3.48  orderings_time:                         0.
% 23.72/3.48  out_proof_time:                         0.013
% 23.72/3.48  total_time:                             2.903
% 23.72/3.48  num_of_symbols:                         48
% 23.72/3.48  num_of_terms:                           124235
% 23.72/3.48  
% 23.72/3.48  ------ Preprocessing
% 23.72/3.48  
% 23.72/3.48  num_of_splits:                          0
% 23.72/3.48  num_of_split_atoms:                     1
% 23.72/3.48  num_of_reused_defs:                     0
% 23.72/3.48  num_eq_ax_congr_red:                    21
% 23.72/3.48  num_of_sem_filtered_clauses:            1
% 23.72/3.48  num_of_subtypes:                        0
% 23.72/3.48  monotx_restored_types:                  0
% 23.72/3.48  sat_num_of_epr_types:                   0
% 23.72/3.48  sat_num_of_non_cyclic_types:            0
% 23.72/3.48  sat_guarded_non_collapsed_types:        0
% 23.72/3.48  num_pure_diseq_elim:                    0
% 23.72/3.48  simp_replaced_by:                       0
% 23.72/3.48  res_preprocessed:                       127
% 23.72/3.48  prep_upred:                             0
% 23.72/3.48  prep_unflattend:                        24
% 23.72/3.48  smt_new_axioms:                         0
% 23.72/3.48  pred_elim_cands:                        4
% 23.72/3.48  pred_elim:                              0
% 23.72/3.48  pred_elim_cl:                           0
% 23.72/3.48  pred_elim_cycles:                       2
% 23.72/3.48  merged_defs:                            8
% 23.72/3.48  merged_defs_ncl:                        0
% 23.72/3.48  bin_hyper_res:                          8
% 23.72/3.48  prep_cycles:                            4
% 23.72/3.48  pred_elim_time:                         0.002
% 23.72/3.48  splitting_time:                         0.
% 23.72/3.48  sem_filter_time:                        0.
% 23.72/3.48  monotx_time:                            0.
% 23.72/3.48  subtype_inf_time:                       0.
% 23.72/3.48  
% 23.72/3.48  ------ Problem properties
% 23.72/3.48  
% 23.72/3.48  clauses:                                25
% 23.72/3.48  conjectures:                            2
% 23.72/3.48  epr:                                    6
% 23.72/3.48  horn:                                   22
% 23.72/3.48  ground:                                 2
% 23.72/3.48  unary:                                  12
% 23.72/3.48  binary:                                 5
% 23.72/3.48  lits:                                   46
% 23.72/3.48  lits_eq:                                15
% 23.72/3.48  fd_pure:                                0
% 23.72/3.48  fd_pseudo:                              0
% 23.72/3.48  fd_cond:                                0
% 23.72/3.48  fd_pseudo_cond:                         3
% 23.72/3.48  ac_symbols:                             0
% 23.72/3.48  
% 23.72/3.48  ------ Propositional Solver
% 23.72/3.48  
% 23.72/3.48  prop_solver_calls:                      34
% 23.72/3.48  prop_fast_solver_calls:                 1041
% 23.72/3.48  smt_solver_calls:                       0
% 23.72/3.48  smt_fast_solver_calls:                  0
% 23.72/3.48  prop_num_of_clauses:                    20345
% 23.72/3.48  prop_preprocess_simplified:             22857
% 23.72/3.48  prop_fo_subsumed:                       3
% 23.72/3.48  prop_solver_time:                       0.
% 23.72/3.48  smt_solver_time:                        0.
% 23.72/3.48  smt_fast_solver_time:                   0.
% 23.72/3.48  prop_fast_solver_time:                  0.
% 23.72/3.48  prop_unsat_core_time:                   0.
% 23.72/3.48  
% 23.72/3.48  ------ QBF
% 23.72/3.48  
% 23.72/3.48  qbf_q_res:                              0
% 23.72/3.48  qbf_num_tautologies:                    0
% 23.72/3.48  qbf_prep_cycles:                        0
% 23.72/3.48  
% 23.72/3.48  ------ BMC1
% 23.72/3.48  
% 23.72/3.48  bmc1_current_bound:                     -1
% 23.72/3.48  bmc1_last_solved_bound:                 -1
% 23.72/3.48  bmc1_unsat_core_size:                   -1
% 23.72/3.48  bmc1_unsat_core_parents_size:           -1
% 23.72/3.48  bmc1_merge_next_fun:                    0
% 23.72/3.48  bmc1_unsat_core_clauses_time:           0.
% 23.72/3.48  
% 23.72/3.48  ------ Instantiation
% 23.72/3.48  
% 23.72/3.48  inst_num_of_clauses:                    3941
% 23.72/3.48  inst_num_in_passive:                    875
% 23.72/3.48  inst_num_in_active:                     1379
% 23.72/3.48  inst_num_in_unprocessed:                1687
% 23.72/3.48  inst_num_of_loops:                      1780
% 23.72/3.48  inst_num_of_learning_restarts:          0
% 23.72/3.48  inst_num_moves_active_passive:          398
% 23.72/3.48  inst_lit_activity:                      0
% 23.72/3.48  inst_lit_activity_moves:                0
% 23.72/3.48  inst_num_tautologies:                   0
% 23.72/3.48  inst_num_prop_implied:                  0
% 23.72/3.48  inst_num_existing_simplified:           0
% 23.72/3.48  inst_num_eq_res_simplified:             0
% 23.72/3.48  inst_num_child_elim:                    0
% 23.72/3.48  inst_num_of_dismatching_blockings:      2647
% 23.72/3.48  inst_num_of_non_proper_insts:           5847
% 23.72/3.48  inst_num_of_duplicates:                 0
% 23.72/3.48  inst_inst_num_from_inst_to_res:         0
% 23.72/3.48  inst_dismatching_checking_time:         0.
% 23.72/3.48  
% 23.72/3.48  ------ Resolution
% 23.72/3.48  
% 23.72/3.48  res_num_of_clauses:                     0
% 23.72/3.48  res_num_in_passive:                     0
% 23.72/3.48  res_num_in_active:                      0
% 23.72/3.48  res_num_of_loops:                       131
% 23.72/3.48  res_forward_subset_subsumed:            562
% 23.72/3.48  res_backward_subset_subsumed:           0
% 23.72/3.48  res_forward_subsumed:                   0
% 23.72/3.48  res_backward_subsumed:                  0
% 23.72/3.48  res_forward_subsumption_resolution:     2
% 23.72/3.48  res_backward_subsumption_resolution:    0
% 23.72/3.48  res_clause_to_clause_subsumption:       44753
% 23.72/3.48  res_orphan_elimination:                 0
% 23.72/3.48  res_tautology_del:                      486
% 23.72/3.48  res_num_eq_res_simplified:              0
% 23.72/3.48  res_num_sel_changes:                    0
% 23.72/3.48  res_moves_from_active_to_pass:          0
% 23.72/3.48  
% 23.72/3.48  ------ Superposition
% 23.72/3.48  
% 23.72/3.48  sup_time_total:                         0.
% 23.72/3.48  sup_time_generating:                    0.
% 23.72/3.48  sup_time_sim_full:                      0.
% 23.72/3.48  sup_time_sim_immed:                     0.
% 23.72/3.48  
% 23.72/3.48  sup_num_of_clauses:                     4733
% 23.72/3.48  sup_num_in_active:                      114
% 23.72/3.48  sup_num_in_passive:                     4619
% 23.72/3.48  sup_num_of_loops:                       355
% 23.72/3.48  sup_fw_superposition:                   12224
% 23.72/3.48  sup_bw_superposition:                   7663
% 23.72/3.48  sup_immediate_simplified:               13990
% 23.72/3.48  sup_given_eliminated:                   15
% 23.72/3.48  comparisons_done:                       0
% 23.72/3.48  comparisons_avoided:                    0
% 23.72/3.48  
% 23.72/3.48  ------ Simplifications
% 23.72/3.48  
% 23.72/3.48  
% 23.72/3.48  sim_fw_subset_subsumed:                 4
% 23.72/3.48  sim_bw_subset_subsumed:                 0
% 23.72/3.48  sim_fw_subsumed:                        1352
% 23.72/3.48  sim_bw_subsumed:                        265
% 23.72/3.48  sim_fw_subsumption_res:                 0
% 23.72/3.48  sim_bw_subsumption_res:                 0
% 23.72/3.48  sim_tautology_del:                      4
% 23.72/3.49  sim_eq_tautology_del:                   8358
% 23.72/3.49  sim_eq_res_simp:                        0
% 23.72/3.49  sim_fw_demodulated:                     11131
% 23.72/3.49  sim_bw_demodulated:                     418
% 23.72/3.49  sim_light_normalised:                   5220
% 23.72/3.49  sim_joinable_taut:                      0
% 23.72/3.49  sim_joinable_simp:                      0
% 23.72/3.49  sim_ac_normalised:                      0
% 23.72/3.49  sim_smt_subsumption:                    0
% 23.72/3.49  
%------------------------------------------------------------------------------
