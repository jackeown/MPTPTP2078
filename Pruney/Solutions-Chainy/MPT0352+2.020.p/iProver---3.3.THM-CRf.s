%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:34 EST 2020

% Result     : Theorem 51.42s
% Output     : CNFRefutation 51.42s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 368 expanded)
%              Number of clauses        :   78 ( 130 expanded)
%              Number of leaves         :   21 (  82 expanded)
%              Depth                    :   23
%              Number of atoms          :  311 (1187 expanded)
%              Number of equality atoms :  113 ( 204 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f55,f55])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK2) )
        & ( r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK2) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f39,f38])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f55,f55])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f15,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f46,f55])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_734,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_721,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_725,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3377,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_721,c_725])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_722,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3852,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3377,c_722])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_723,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3853,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3377,c_723])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_720,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3378,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_720,c_725])).

cnf(c_3968,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3853,c_3378])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_735,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3971,plain,
    ( r1_tarski(sK1,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3968,c_735])).

cnf(c_3974,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3852,c_3971])).

cnf(c_3978,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3974,c_3378])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_736,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4802,plain,
    ( r1_tarski(X0,k4_xboole_0(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k4_xboole_0(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3978,c_736])).

cnf(c_5616,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),X0),k4_xboole_0(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_4802])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_738,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7324,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5616,c_738])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_739,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8718,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7324,c_739])).

cnf(c_9,plain,
    ( k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_732,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4489,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_732])).

cnf(c_6761,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X1),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_4489])).

cnf(c_10567,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(sK2,sK0))) != iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8718,c_6761])).

cnf(c_217035,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(sK2,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10567,c_3971])).

cnf(c_217042,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_217035])).

cnf(c_12,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_731,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_726,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1067,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_726])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_927,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_928,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_1428,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1067,c_26,c_31,c_928])).

cnf(c_14,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_730,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2007,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_730])).

cnf(c_2151,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1428,c_2007])).

cnf(c_4804,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2151,c_736])).

cnf(c_5593,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_4804])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_733,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6180,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,X0),sK0) != iProver_top
    | v1_xboole_0(k4_xboole_0(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5593,c_733])).

cnf(c_10978,plain,
    ( v1_xboole_0(k4_xboole_0(sK2,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_6180])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_740,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14648,plain,
    ( k4_xboole_0(sK2,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10978,c_740])).

cnf(c_14675,plain,
    ( k3_tarski(k2_tarski(sK0,sK2)) = k3_tarski(k2_tarski(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_14648,c_9])).

cnf(c_5,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14688,plain,
    ( k3_tarski(k2_tarski(sK0,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_14675,c_5])).

cnf(c_217045,plain,
    ( r1_tarski(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_217042,c_14688])).

cnf(c_1068,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_726])).

cnf(c_25,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_930,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_931,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_1434,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1068,c_25,c_31,c_931])).

cnf(c_2152,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1434,c_2007])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_217045,c_2152])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:52:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.42/6.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.42/6.98  
% 51.42/6.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.42/6.98  
% 51.42/6.98  ------  iProver source info
% 51.42/6.98  
% 51.42/6.98  git: date: 2020-06-30 10:37:57 +0100
% 51.42/6.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.42/6.98  git: non_committed_changes: false
% 51.42/6.98  git: last_make_outside_of_git: false
% 51.42/6.98  
% 51.42/6.98  ------ 
% 51.42/6.98  ------ Parsing...
% 51.42/6.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.42/6.98  
% 51.42/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 51.42/6.98  
% 51.42/6.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.42/6.98  
% 51.42/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.42/6.98  ------ Proving...
% 51.42/6.98  ------ Problem Properties 
% 51.42/6.98  
% 51.42/6.98  
% 51.42/6.98  clauses                                 25
% 51.42/6.98  conjectures                             4
% 51.42/6.98  EPR                                     8
% 51.42/6.98  Horn                                    22
% 51.42/6.98  unary                                   9
% 51.42/6.98  binary                                  9
% 51.42/6.98  lits                                    48
% 51.42/6.98  lits eq                                 6
% 51.42/6.98  fd_pure                                 0
% 51.42/6.98  fd_pseudo                               0
% 51.42/6.98  fd_cond                                 1
% 51.42/6.98  fd_pseudo_cond                          0
% 51.42/6.98  AC symbols                              0
% 51.42/6.98  
% 51.42/6.98  ------ Input Options Time Limit: Unbounded
% 51.42/6.98  
% 51.42/6.98  
% 51.42/6.98  ------ 
% 51.42/6.98  Current options:
% 51.42/6.98  ------ 
% 51.42/6.98  
% 51.42/6.98  
% 51.42/6.98  
% 51.42/6.98  
% 51.42/6.98  ------ Proving...
% 51.42/6.98  
% 51.42/6.98  
% 51.42/6.98  % SZS status Theorem for theBenchmark.p
% 51.42/6.98  
% 51.42/6.98  % SZS output start CNFRefutation for theBenchmark.p
% 51.42/6.98  
% 51.42/6.98  fof(f1,axiom,(
% 51.42/6.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f41,plain,(
% 51.42/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f1])).
% 51.42/6.98  
% 51.42/6.98  fof(f14,axiom,(
% 51.42/6.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f55,plain,(
% 51.42/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 51.42/6.98    inference(cnf_transformation,[],[f14])).
% 51.42/6.98  
% 51.42/6.98  fof(f67,plain,(
% 51.42/6.98    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 51.42/6.98    inference(definition_unfolding,[],[f41,f55,f55])).
% 51.42/6.98  
% 51.42/6.98  fof(f8,axiom,(
% 51.42/6.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f49,plain,(
% 51.42/6.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f8])).
% 51.42/6.98  
% 51.42/6.98  fof(f19,conjecture,(
% 51.42/6.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f20,negated_conjecture,(
% 51.42/6.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 51.42/6.98    inference(negated_conjecture,[],[f19])).
% 51.42/6.98  
% 51.42/6.98  fof(f34,plain,(
% 51.42/6.98    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.42/6.98    inference(ennf_transformation,[],[f20])).
% 51.42/6.98  
% 51.42/6.98  fof(f36,plain,(
% 51.42/6.98    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.42/6.98    inference(nnf_transformation,[],[f34])).
% 51.42/6.98  
% 51.42/6.98  fof(f37,plain,(
% 51.42/6.98    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.42/6.98    inference(flattening,[],[f36])).
% 51.42/6.98  
% 51.42/6.98  fof(f39,plain,(
% 51.42/6.98    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK2)) & (r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1)) | r1_tarski(X1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 51.42/6.98    introduced(choice_axiom,[])).
% 51.42/6.98  
% 51.42/6.98  fof(f38,plain,(
% 51.42/6.98    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 51.42/6.98    introduced(choice_axiom,[])).
% 51.42/6.98  
% 51.42/6.98  fof(f40,plain,(
% 51.42/6.98    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 51.42/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f39,f38])).
% 51.42/6.98  
% 51.42/6.98  fof(f64,plain,(
% 51.42/6.98    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 51.42/6.98    inference(cnf_transformation,[],[f40])).
% 51.42/6.98  
% 51.42/6.98  fof(f17,axiom,(
% 51.42/6.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f33,plain,(
% 51.42/6.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.42/6.98    inference(ennf_transformation,[],[f17])).
% 51.42/6.98  
% 51.42/6.98  fof(f61,plain,(
% 51.42/6.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.42/6.98    inference(cnf_transformation,[],[f33])).
% 51.42/6.98  
% 51.42/6.98  fof(f65,plain,(
% 51.42/6.98    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 51.42/6.98    inference(cnf_transformation,[],[f40])).
% 51.42/6.98  
% 51.42/6.98  fof(f66,plain,(
% 51.42/6.98    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 51.42/6.98    inference(cnf_transformation,[],[f40])).
% 51.42/6.98  
% 51.42/6.98  fof(f63,plain,(
% 51.42/6.98    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 51.42/6.98    inference(cnf_transformation,[],[f40])).
% 51.42/6.98  
% 51.42/6.98  fof(f7,axiom,(
% 51.42/6.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f26,plain,(
% 51.42/6.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 51.42/6.98    inference(ennf_transformation,[],[f7])).
% 51.42/6.98  
% 51.42/6.98  fof(f48,plain,(
% 51.42/6.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f26])).
% 51.42/6.98  
% 51.42/6.98  fof(f6,axiom,(
% 51.42/6.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f24,plain,(
% 51.42/6.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 51.42/6.98    inference(ennf_transformation,[],[f6])).
% 51.42/6.98  
% 51.42/6.98  fof(f25,plain,(
% 51.42/6.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 51.42/6.98    inference(flattening,[],[f24])).
% 51.42/6.98  
% 51.42/6.98  fof(f47,plain,(
% 51.42/6.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f25])).
% 51.42/6.98  
% 51.42/6.98  fof(f4,axiom,(
% 51.42/6.98    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f23,plain,(
% 51.42/6.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 51.42/6.98    inference(ennf_transformation,[],[f4])).
% 51.42/6.98  
% 51.42/6.98  fof(f45,plain,(
% 51.42/6.98    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 51.42/6.98    inference(cnf_transformation,[],[f23])).
% 51.42/6.98  
% 51.42/6.98  fof(f3,axiom,(
% 51.42/6.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f22,plain,(
% 51.42/6.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 51.42/6.98    inference(ennf_transformation,[],[f3])).
% 51.42/6.98  
% 51.42/6.98  fof(f43,plain,(
% 51.42/6.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f22])).
% 51.42/6.98  
% 51.42/6.98  fof(f9,axiom,(
% 51.42/6.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f50,plain,(
% 51.42/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 51.42/6.98    inference(cnf_transformation,[],[f9])).
% 51.42/6.98  
% 51.42/6.98  fof(f69,plain,(
% 51.42/6.98    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 51.42/6.98    inference(definition_unfolding,[],[f50,f55,f55])).
% 51.42/6.98  
% 51.42/6.98  fof(f11,axiom,(
% 51.42/6.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f29,plain,(
% 51.42/6.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 51.42/6.98    inference(ennf_transformation,[],[f11])).
% 51.42/6.98  
% 51.42/6.98  fof(f30,plain,(
% 51.42/6.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 51.42/6.98    inference(flattening,[],[f29])).
% 51.42/6.98  
% 51.42/6.98  fof(f52,plain,(
% 51.42/6.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 51.42/6.98    inference(cnf_transformation,[],[f30])).
% 51.42/6.98  
% 51.42/6.98  fof(f70,plain,(
% 51.42/6.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 51.42/6.98    inference(definition_unfolding,[],[f52,f55])).
% 51.42/6.98  
% 51.42/6.98  fof(f12,axiom,(
% 51.42/6.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f53,plain,(
% 51.42/6.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f12])).
% 51.42/6.98  
% 51.42/6.98  fof(f16,axiom,(
% 51.42/6.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f32,plain,(
% 51.42/6.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 51.42/6.98    inference(ennf_transformation,[],[f16])).
% 51.42/6.98  
% 51.42/6.98  fof(f35,plain,(
% 51.42/6.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 51.42/6.98    inference(nnf_transformation,[],[f32])).
% 51.42/6.98  
% 51.42/6.98  fof(f57,plain,(
% 51.42/6.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f35])).
% 51.42/6.98  
% 51.42/6.98  fof(f18,axiom,(
% 51.42/6.98    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f62,plain,(
% 51.42/6.98    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 51.42/6.98    inference(cnf_transformation,[],[f18])).
% 51.42/6.98  
% 51.42/6.98  fof(f15,axiom,(
% 51.42/6.98    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f56,plain,(
% 51.42/6.98    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 51.42/6.98    inference(cnf_transformation,[],[f15])).
% 51.42/6.98  
% 51.42/6.98  fof(f13,axiom,(
% 51.42/6.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f31,plain,(
% 51.42/6.98    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 51.42/6.98    inference(ennf_transformation,[],[f13])).
% 51.42/6.98  
% 51.42/6.98  fof(f54,plain,(
% 51.42/6.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f31])).
% 51.42/6.98  
% 51.42/6.98  fof(f10,axiom,(
% 51.42/6.98    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f27,plain,(
% 51.42/6.98    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 51.42/6.98    inference(ennf_transformation,[],[f10])).
% 51.42/6.98  
% 51.42/6.98  fof(f28,plain,(
% 51.42/6.98    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 51.42/6.98    inference(flattening,[],[f27])).
% 51.42/6.98  
% 51.42/6.98  fof(f51,plain,(
% 51.42/6.98    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f28])).
% 51.42/6.98  
% 51.42/6.98  fof(f2,axiom,(
% 51.42/6.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f21,plain,(
% 51.42/6.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 51.42/6.98    inference(ennf_transformation,[],[f2])).
% 51.42/6.98  
% 51.42/6.98  fof(f42,plain,(
% 51.42/6.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 51.42/6.98    inference(cnf_transformation,[],[f21])).
% 51.42/6.98  
% 51.42/6.98  fof(f5,axiom,(
% 51.42/6.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 51.42/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.42/6.98  
% 51.42/6.98  fof(f46,plain,(
% 51.42/6.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.42/6.98    inference(cnf_transformation,[],[f5])).
% 51.42/6.98  
% 51.42/6.98  fof(f68,plain,(
% 51.42/6.98    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 51.42/6.98    inference(definition_unfolding,[],[f46,f55])).
% 51.42/6.98  
% 51.42/6.98  cnf(c_0,plain,
% 51.42/6.98      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 51.42/6.98      inference(cnf_transformation,[],[f67]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_8,plain,
% 51.42/6.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 51.42/6.98      inference(cnf_transformation,[],[f49]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_734,plain,
% 51.42/6.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_23,negated_conjecture,
% 51.42/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 51.42/6.98      inference(cnf_transformation,[],[f64]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_721,plain,
% 51.42/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_19,plain,
% 51.42/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.42/6.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 51.42/6.98      inference(cnf_transformation,[],[f61]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_725,plain,
% 51.42/6.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 51.42/6.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_3377,plain,
% 51.42/6.98      ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_721,c_725]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_22,negated_conjecture,
% 51.42/6.98      ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
% 51.42/6.98      | r1_tarski(sK1,sK2) ),
% 51.42/6.98      inference(cnf_transformation,[],[f65]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_722,plain,
% 51.42/6.98      ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
% 51.42/6.98      | r1_tarski(sK1,sK2) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_3852,plain,
% 51.42/6.98      ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
% 51.42/6.98      | r1_tarski(sK1,sK2) = iProver_top ),
% 51.42/6.98      inference(demodulation,[status(thm)],[c_3377,c_722]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_21,negated_conjecture,
% 51.42/6.98      ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
% 51.42/6.98      | ~ r1_tarski(sK1,sK2) ),
% 51.42/6.98      inference(cnf_transformation,[],[f66]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_723,plain,
% 51.42/6.98      ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
% 51.42/6.98      | r1_tarski(sK1,sK2) != iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_3853,plain,
% 51.42/6.98      ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
% 51.42/6.98      | r1_tarski(sK1,sK2) != iProver_top ),
% 51.42/6.98      inference(demodulation,[status(thm)],[c_3377,c_723]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_24,negated_conjecture,
% 51.42/6.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 51.42/6.98      inference(cnf_transformation,[],[f63]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_720,plain,
% 51.42/6.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_3378,plain,
% 51.42/6.98      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_720,c_725]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_3968,plain,
% 51.42/6.98      ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) != iProver_top
% 51.42/6.98      | r1_tarski(sK1,sK2) != iProver_top ),
% 51.42/6.98      inference(light_normalisation,[status(thm)],[c_3853,c_3378]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_7,plain,
% 51.42/6.98      ( ~ r1_tarski(X0,X1)
% 51.42/6.98      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 51.42/6.98      inference(cnf_transformation,[],[f48]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_735,plain,
% 51.42/6.98      ( r1_tarski(X0,X1) != iProver_top
% 51.42/6.98      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_3971,plain,
% 51.42/6.98      ( r1_tarski(sK1,sK2) != iProver_top ),
% 51.42/6.98      inference(forward_subsumption_resolution,
% 51.42/6.98                [status(thm)],
% 51.42/6.98                [c_3968,c_735]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_3974,plain,
% 51.42/6.98      ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top ),
% 51.42/6.98      inference(global_propositional_subsumption,
% 51.42/6.98                [status(thm)],
% 51.42/6.98                [c_3852,c_3971]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_3978,plain,
% 51.42/6.98      ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) = iProver_top ),
% 51.42/6.98      inference(light_normalisation,[status(thm)],[c_3974,c_3378]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_6,plain,
% 51.42/6.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 51.42/6.98      inference(cnf_transformation,[],[f47]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_736,plain,
% 51.42/6.98      ( r1_tarski(X0,X1) != iProver_top
% 51.42/6.98      | r1_tarski(X2,X0) != iProver_top
% 51.42/6.98      | r1_tarski(X2,X1) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_4802,plain,
% 51.42/6.98      ( r1_tarski(X0,k4_xboole_0(sK0,sK1)) = iProver_top
% 51.42/6.98      | r1_tarski(X0,k4_xboole_0(sK0,sK2)) != iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_3978,c_736]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_5616,plain,
% 51.42/6.98      ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),X0),k4_xboole_0(sK0,sK1)) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_734,c_4802]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_3,plain,
% 51.42/6.98      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 51.42/6.98      inference(cnf_transformation,[],[f45]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_738,plain,
% 51.42/6.98      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 51.42/6.98      | r1_xboole_0(X0,X2) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_7324,plain,
% 51.42/6.98      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),X0),sK1) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_5616,c_738]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_2,plain,
% 51.42/6.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 51.42/6.98      inference(cnf_transformation,[],[f43]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_739,plain,
% 51.42/6.98      ( r1_xboole_0(X0,X1) != iProver_top
% 51.42/6.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_8718,plain,
% 51.42/6.98      ( r1_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),X0)) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_7324,c_739]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_9,plain,
% 51.42/6.98      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 51.42/6.98      inference(cnf_transformation,[],[f69]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_11,plain,
% 51.42/6.98      ( r1_tarski(X0,X1)
% 51.42/6.98      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 51.42/6.98      | ~ r1_xboole_0(X0,X2) ),
% 51.42/6.98      inference(cnf_transformation,[],[f70]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_732,plain,
% 51.42/6.98      ( r1_tarski(X0,X1) = iProver_top
% 51.42/6.98      | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
% 51.42/6.98      | r1_xboole_0(X0,X2) != iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_4489,plain,
% 51.42/6.98      ( r1_tarski(X0,X1) = iProver_top
% 51.42/6.98      | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
% 51.42/6.98      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_9,c_732]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_6761,plain,
% 51.42/6.98      ( r1_tarski(X0,X1) = iProver_top
% 51.42/6.98      | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
% 51.42/6.98      | r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X1),X1)) != iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_9,c_4489]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_10567,plain,
% 51.42/6.98      ( r1_tarski(sK1,k3_tarski(k2_tarski(sK2,sK0))) != iProver_top
% 51.42/6.98      | r1_tarski(sK1,sK2) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_8718,c_6761]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_217035,plain,
% 51.42/6.98      ( r1_tarski(sK1,k3_tarski(k2_tarski(sK2,sK0))) != iProver_top ),
% 51.42/6.98      inference(global_propositional_subsumption,
% 51.42/6.98                [status(thm)],
% 51.42/6.98                [c_10567,c_3971]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_217042,plain,
% 51.42/6.98      ( r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK2))) != iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_0,c_217035]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_12,plain,
% 51.42/6.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 51.42/6.98      inference(cnf_transformation,[],[f53]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_731,plain,
% 51.42/6.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_18,plain,
% 51.42/6.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 51.42/6.98      inference(cnf_transformation,[],[f57]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_726,plain,
% 51.42/6.98      ( m1_subset_1(X0,X1) != iProver_top
% 51.42/6.98      | r2_hidden(X0,X1) = iProver_top
% 51.42/6.98      | v1_xboole_0(X1) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_1067,plain,
% 51.42/6.98      ( r2_hidden(sK2,k1_zfmisc_1(sK0)) = iProver_top
% 51.42/6.98      | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_721,c_726]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_26,plain,
% 51.42/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_20,plain,
% 51.42/6.98      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 51.42/6.98      inference(cnf_transformation,[],[f62]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_29,plain,
% 51.42/6.98      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_31,plain,
% 51.42/6.98      ( v1_xboole_0(k1_zfmisc_1(sK0)) != iProver_top ),
% 51.42/6.98      inference(instantiation,[status(thm)],[c_29]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_927,plain,
% 51.42/6.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 51.42/6.98      | r2_hidden(sK2,k1_zfmisc_1(sK0))
% 51.42/6.98      | v1_xboole_0(k1_zfmisc_1(sK0)) ),
% 51.42/6.98      inference(instantiation,[status(thm)],[c_18]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_928,plain,
% 51.42/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 51.42/6.98      | r2_hidden(sK2,k1_zfmisc_1(sK0)) = iProver_top
% 51.42/6.98      | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_1428,plain,
% 51.42/6.98      ( r2_hidden(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(global_propositional_subsumption,
% 51.42/6.98                [status(thm)],
% 51.42/6.98                [c_1067,c_26,c_31,c_928]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_14,plain,
% 51.42/6.98      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 51.42/6.98      inference(cnf_transformation,[],[f56]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_13,plain,
% 51.42/6.98      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 51.42/6.98      inference(cnf_transformation,[],[f54]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_730,plain,
% 51.42/6.98      ( r2_hidden(X0,X1) != iProver_top
% 51.42/6.98      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_2007,plain,
% 51.42/6.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.42/6.98      | r1_tarski(X0,X1) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_14,c_730]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_2151,plain,
% 51.42/6.98      ( r1_tarski(sK2,sK0) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_1428,c_2007]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_4804,plain,
% 51.42/6.98      ( r1_tarski(X0,sK2) != iProver_top
% 51.42/6.98      | r1_tarski(X0,sK0) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_2151,c_736]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_5593,plain,
% 51.42/6.98      ( r1_tarski(k4_xboole_0(sK2,X0),sK0) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_734,c_4804]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_10,plain,
% 51.42/6.98      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 51.42/6.98      inference(cnf_transformation,[],[f51]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_733,plain,
% 51.42/6.98      ( r1_tarski(X0,X1) != iProver_top
% 51.42/6.98      | r1_xboole_0(X0,X1) != iProver_top
% 51.42/6.98      | v1_xboole_0(X0) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_6180,plain,
% 51.42/6.98      ( r1_xboole_0(k4_xboole_0(sK2,X0),sK0) != iProver_top
% 51.42/6.98      | v1_xboole_0(k4_xboole_0(sK2,X0)) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_5593,c_733]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_10978,plain,
% 51.42/6.98      ( v1_xboole_0(k4_xboole_0(sK2,sK0)) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_731,c_6180]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_1,plain,
% 51.42/6.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 51.42/6.98      inference(cnf_transformation,[],[f42]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_740,plain,
% 51.42/6.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_14648,plain,
% 51.42/6.98      ( k4_xboole_0(sK2,sK0) = k1_xboole_0 ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_10978,c_740]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_14675,plain,
% 51.42/6.98      ( k3_tarski(k2_tarski(sK0,sK2)) = k3_tarski(k2_tarski(sK0,k1_xboole_0)) ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_14648,c_9]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_5,plain,
% 51.42/6.98      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 51.42/6.98      inference(cnf_transformation,[],[f68]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_14688,plain,
% 51.42/6.98      ( k3_tarski(k2_tarski(sK0,sK2)) = sK0 ),
% 51.42/6.98      inference(demodulation,[status(thm)],[c_14675,c_5]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_217045,plain,
% 51.42/6.98      ( r1_tarski(sK1,sK0) != iProver_top ),
% 51.42/6.98      inference(light_normalisation,[status(thm)],[c_217042,c_14688]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_1068,plain,
% 51.42/6.98      ( r2_hidden(sK1,k1_zfmisc_1(sK0)) = iProver_top
% 51.42/6.98      | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_720,c_726]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_25,plain,
% 51.42/6.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_930,plain,
% 51.42/6.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
% 51.42/6.98      | r2_hidden(sK1,k1_zfmisc_1(sK0))
% 51.42/6.98      | v1_xboole_0(k1_zfmisc_1(sK0)) ),
% 51.42/6.98      inference(instantiation,[status(thm)],[c_18]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_931,plain,
% 51.42/6.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 51.42/6.98      | r2_hidden(sK1,k1_zfmisc_1(sK0)) = iProver_top
% 51.42/6.98      | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_1434,plain,
% 51.42/6.98      ( r2_hidden(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 51.42/6.98      inference(global_propositional_subsumption,
% 51.42/6.98                [status(thm)],
% 51.42/6.98                [c_1068,c_25,c_31,c_931]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(c_2152,plain,
% 51.42/6.98      ( r1_tarski(sK1,sK0) = iProver_top ),
% 51.42/6.98      inference(superposition,[status(thm)],[c_1434,c_2007]) ).
% 51.42/6.98  
% 51.42/6.98  cnf(contradiction,plain,
% 51.42/6.98      ( $false ),
% 51.42/6.98      inference(minisat,[status(thm)],[c_217045,c_2152]) ).
% 51.42/6.98  
% 51.42/6.98  
% 51.42/6.98  % SZS output end CNFRefutation for theBenchmark.p
% 51.42/6.98  
% 51.42/6.98  ------                               Statistics
% 51.42/6.98  
% 51.42/6.98  ------ Selected
% 51.42/6.98  
% 51.42/6.98  total_time:                             6.058
% 51.42/6.98  
%------------------------------------------------------------------------------
