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
% DateTime   : Thu Dec  3 11:40:37 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 451 expanded)
%              Number of clauses        :   64 ( 143 expanded)
%              Number of leaves         :   25 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  297 (1415 expanded)
%              Number of equality atoms :  122 ( 273 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(X1,k3_subset_1(X0,sK2))
          | ~ r1_xboole_0(X1,sK2) )
        & ( r1_tarski(X1,k3_subset_1(X0,sK2))
          | r1_xboole_0(X1,sK2) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
            | ~ r1_xboole_0(sK1,X2) )
          & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
            | r1_xboole_0(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f39,f38])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f18,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

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
    inference(nnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f63,f43])).

fof(f68,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f46,f43,f75])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f44,f75])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_803,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,X1)
    | r1_tarski(X0,k3_tarski(X1))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_13,c_8])).

cnf(c_802,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_1100,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_802])).

cnf(c_15,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_808,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1868,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1100,c_808])).

cnf(c_1874,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_1868])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_815,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1936,plain,
    ( k3_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_1874,c_815])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_809,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1437,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_803,c_809])).

cnf(c_1559,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_1437])).

cnf(c_2138,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1936,c_1559])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_805,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) = iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_807,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1631,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK2,k3_subset_1(sK0,sK1)) = iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_807])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1938,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1)) = iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1631,c_21,c_22])).

cnf(c_1944,plain,
    ( k3_xboole_0(sK2,k3_subset_1(sK0,sK1)) = sK2
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_815])).

cnf(c_804,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1873,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_1868])).

cnf(c_1886,plain,
    ( k3_xboole_0(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_1873,c_815])).

cnf(c_2127,plain,
    ( k3_xboole_0(sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1886,c_0])).

cnf(c_1436,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_subset_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_804,c_809])).

cnf(c_2482,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_2127,c_1436])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_806,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) != iProver_top
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2917,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK0,sK2)) != iProver_top
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2482,c_806])).

cnf(c_24,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) != iProver_top
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_812,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2328,plain,
    ( r1_tarski(X0,k3_subset_1(sK0,sK2)) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_812])).

cnf(c_2382,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK1,sK0) != iProver_top
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2328])).

cnf(c_2938,plain,
    ( r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2917,c_24,c_1874,c_2382])).

cnf(c_3961,plain,
    ( k3_xboole_0(sK2,k3_subset_1(sK0,sK1)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1944,c_24,c_1874,c_2382])).

cnf(c_4011,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK0,sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2138,c_3961])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_813,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4523,plain,
    ( r1_xboole_0(X0,k5_xboole_0(sK2,sK2)) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(sK0,sK1)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_813])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_845,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_2])).

cnf(c_4527,plain,
    ( r1_xboole_0(X0,k5_xboole_0(sK0,sK1)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4523,c_845])).

cnf(c_4559,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) != iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top
    | r1_xboole_0(sK1,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4527])).

cnf(c_1,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_816,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1214,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_816])).

cnf(c_2139,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_1214])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_50,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_52,plain,
    ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4559,c_2938,c_2139,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 2.43/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/1.01  
% 2.43/1.01  ------  iProver source info
% 2.43/1.01  
% 2.43/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.43/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/1.01  git: non_committed_changes: false
% 2.43/1.01  git: last_make_outside_of_git: false
% 2.43/1.01  
% 2.43/1.01  ------ 
% 2.43/1.01  
% 2.43/1.01  ------ Input Options
% 2.43/1.01  
% 2.43/1.01  --out_options                           all
% 2.43/1.01  --tptp_safe_out                         true
% 2.43/1.01  --problem_path                          ""
% 2.43/1.01  --include_path                          ""
% 2.43/1.01  --clausifier                            res/vclausify_rel
% 2.43/1.01  --clausifier_options                    --mode clausify
% 2.43/1.01  --stdin                                 false
% 2.43/1.01  --stats_out                             all
% 2.43/1.01  
% 2.43/1.01  ------ General Options
% 2.43/1.01  
% 2.43/1.01  --fof                                   false
% 2.43/1.01  --time_out_real                         305.
% 2.43/1.01  --time_out_virtual                      -1.
% 2.43/1.01  --symbol_type_check                     false
% 2.43/1.01  --clausify_out                          false
% 2.43/1.01  --sig_cnt_out                           false
% 2.43/1.01  --trig_cnt_out                          false
% 2.43/1.01  --trig_cnt_out_tolerance                1.
% 2.43/1.01  --trig_cnt_out_sk_spl                   false
% 2.43/1.01  --abstr_cl_out                          false
% 2.43/1.01  
% 2.43/1.01  ------ Global Options
% 2.43/1.01  
% 2.43/1.01  --schedule                              default
% 2.43/1.01  --add_important_lit                     false
% 2.43/1.01  --prop_solver_per_cl                    1000
% 2.43/1.01  --min_unsat_core                        false
% 2.43/1.01  --soft_assumptions                      false
% 2.43/1.01  --soft_lemma_size                       3
% 2.43/1.01  --prop_impl_unit_size                   0
% 2.43/1.01  --prop_impl_unit                        []
% 2.43/1.01  --share_sel_clauses                     true
% 2.43/1.01  --reset_solvers                         false
% 2.43/1.01  --bc_imp_inh                            [conj_cone]
% 2.43/1.01  --conj_cone_tolerance                   3.
% 2.43/1.01  --extra_neg_conj                        none
% 2.43/1.01  --large_theory_mode                     true
% 2.43/1.01  --prolific_symb_bound                   200
% 2.43/1.01  --lt_threshold                          2000
% 2.43/1.01  --clause_weak_htbl                      true
% 2.43/1.01  --gc_record_bc_elim                     false
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing Options
% 2.43/1.01  
% 2.43/1.01  --preprocessing_flag                    true
% 2.43/1.01  --time_out_prep_mult                    0.1
% 2.43/1.01  --splitting_mode                        input
% 2.43/1.01  --splitting_grd                         true
% 2.43/1.01  --splitting_cvd                         false
% 2.43/1.01  --splitting_cvd_svl                     false
% 2.43/1.01  --splitting_nvd                         32
% 2.43/1.01  --sub_typing                            true
% 2.43/1.01  --prep_gs_sim                           true
% 2.43/1.01  --prep_unflatten                        true
% 2.43/1.01  --prep_res_sim                          true
% 2.43/1.01  --prep_upred                            true
% 2.43/1.01  --prep_sem_filter                       exhaustive
% 2.43/1.01  --prep_sem_filter_out                   false
% 2.43/1.01  --pred_elim                             true
% 2.43/1.01  --res_sim_input                         true
% 2.43/1.01  --eq_ax_congr_red                       true
% 2.43/1.01  --pure_diseq_elim                       true
% 2.43/1.01  --brand_transform                       false
% 2.43/1.01  --non_eq_to_eq                          false
% 2.43/1.01  --prep_def_merge                        true
% 2.43/1.01  --prep_def_merge_prop_impl              false
% 2.43/1.01  --prep_def_merge_mbd                    true
% 2.43/1.01  --prep_def_merge_tr_red                 false
% 2.43/1.01  --prep_def_merge_tr_cl                  false
% 2.43/1.01  --smt_preprocessing                     true
% 2.43/1.01  --smt_ac_axioms                         fast
% 2.43/1.01  --preprocessed_out                      false
% 2.43/1.01  --preprocessed_stats                    false
% 2.43/1.01  
% 2.43/1.01  ------ Abstraction refinement Options
% 2.43/1.01  
% 2.43/1.01  --abstr_ref                             []
% 2.43/1.01  --abstr_ref_prep                        false
% 2.43/1.01  --abstr_ref_until_sat                   false
% 2.43/1.01  --abstr_ref_sig_restrict                funpre
% 2.43/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.01  --abstr_ref_under                       []
% 2.43/1.01  
% 2.43/1.01  ------ SAT Options
% 2.43/1.01  
% 2.43/1.01  --sat_mode                              false
% 2.43/1.01  --sat_fm_restart_options                ""
% 2.43/1.01  --sat_gr_def                            false
% 2.43/1.01  --sat_epr_types                         true
% 2.43/1.01  --sat_non_cyclic_types                  false
% 2.43/1.01  --sat_finite_models                     false
% 2.43/1.01  --sat_fm_lemmas                         false
% 2.43/1.01  --sat_fm_prep                           false
% 2.43/1.01  --sat_fm_uc_incr                        true
% 2.43/1.01  --sat_out_model                         small
% 2.43/1.01  --sat_out_clauses                       false
% 2.43/1.01  
% 2.43/1.01  ------ QBF Options
% 2.43/1.01  
% 2.43/1.01  --qbf_mode                              false
% 2.43/1.01  --qbf_elim_univ                         false
% 2.43/1.01  --qbf_dom_inst                          none
% 2.43/1.01  --qbf_dom_pre_inst                      false
% 2.43/1.01  --qbf_sk_in                             false
% 2.43/1.01  --qbf_pred_elim                         true
% 2.43/1.01  --qbf_split                             512
% 2.43/1.01  
% 2.43/1.01  ------ BMC1 Options
% 2.43/1.01  
% 2.43/1.01  --bmc1_incremental                      false
% 2.43/1.01  --bmc1_axioms                           reachable_all
% 2.43/1.01  --bmc1_min_bound                        0
% 2.43/1.01  --bmc1_max_bound                        -1
% 2.43/1.01  --bmc1_max_bound_default                -1
% 2.43/1.01  --bmc1_symbol_reachability              true
% 2.43/1.01  --bmc1_property_lemmas                  false
% 2.43/1.01  --bmc1_k_induction                      false
% 2.43/1.01  --bmc1_non_equiv_states                 false
% 2.43/1.01  --bmc1_deadlock                         false
% 2.43/1.01  --bmc1_ucm                              false
% 2.43/1.01  --bmc1_add_unsat_core                   none
% 2.43/1.01  --bmc1_unsat_core_children              false
% 2.43/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.01  --bmc1_out_stat                         full
% 2.43/1.01  --bmc1_ground_init                      false
% 2.43/1.01  --bmc1_pre_inst_next_state              false
% 2.43/1.01  --bmc1_pre_inst_state                   false
% 2.43/1.01  --bmc1_pre_inst_reach_state             false
% 2.43/1.01  --bmc1_out_unsat_core                   false
% 2.43/1.01  --bmc1_aig_witness_out                  false
% 2.43/1.01  --bmc1_verbose                          false
% 2.43/1.01  --bmc1_dump_clauses_tptp                false
% 2.43/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.01  --bmc1_dump_file                        -
% 2.43/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.01  --bmc1_ucm_extend_mode                  1
% 2.43/1.01  --bmc1_ucm_init_mode                    2
% 2.43/1.01  --bmc1_ucm_cone_mode                    none
% 2.43/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.01  --bmc1_ucm_relax_model                  4
% 2.43/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.01  --bmc1_ucm_layered_model                none
% 2.43/1.01  --bmc1_ucm_max_lemma_size               10
% 2.43/1.01  
% 2.43/1.01  ------ AIG Options
% 2.43/1.01  
% 2.43/1.01  --aig_mode                              false
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation Options
% 2.43/1.01  
% 2.43/1.01  --instantiation_flag                    true
% 2.43/1.01  --inst_sos_flag                         false
% 2.43/1.01  --inst_sos_phase                        true
% 2.43/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel_side                     num_symb
% 2.43/1.01  --inst_solver_per_active                1400
% 2.43/1.01  --inst_solver_calls_frac                1.
% 2.43/1.01  --inst_passive_queue_type               priority_queues
% 2.43/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.01  --inst_passive_queues_freq              [25;2]
% 2.43/1.01  --inst_dismatching                      true
% 2.43/1.01  --inst_eager_unprocessed_to_passive     true
% 2.43/1.01  --inst_prop_sim_given                   true
% 2.43/1.01  --inst_prop_sim_new                     false
% 2.43/1.01  --inst_subs_new                         false
% 2.43/1.01  --inst_eq_res_simp                      false
% 2.43/1.01  --inst_subs_given                       false
% 2.43/1.01  --inst_orphan_elimination               true
% 2.43/1.01  --inst_learning_loop_flag               true
% 2.43/1.01  --inst_learning_start                   3000
% 2.43/1.01  --inst_learning_factor                  2
% 2.43/1.01  --inst_start_prop_sim_after_learn       3
% 2.43/1.01  --inst_sel_renew                        solver
% 2.43/1.01  --inst_lit_activity_flag                true
% 2.43/1.01  --inst_restr_to_given                   false
% 2.43/1.01  --inst_activity_threshold               500
% 2.43/1.01  --inst_out_proof                        true
% 2.43/1.01  
% 2.43/1.01  ------ Resolution Options
% 2.43/1.01  
% 2.43/1.01  --resolution_flag                       true
% 2.43/1.01  --res_lit_sel                           adaptive
% 2.43/1.01  --res_lit_sel_side                      none
% 2.43/1.01  --res_ordering                          kbo
% 2.43/1.01  --res_to_prop_solver                    active
% 2.43/1.01  --res_prop_simpl_new                    false
% 2.43/1.01  --res_prop_simpl_given                  true
% 2.43/1.01  --res_passive_queue_type                priority_queues
% 2.43/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.01  --res_passive_queues_freq               [15;5]
% 2.43/1.01  --res_forward_subs                      full
% 2.43/1.01  --res_backward_subs                     full
% 2.43/1.01  --res_forward_subs_resolution           true
% 2.43/1.01  --res_backward_subs_resolution          true
% 2.43/1.01  --res_orphan_elimination                true
% 2.43/1.01  --res_time_limit                        2.
% 2.43/1.01  --res_out_proof                         true
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Options
% 2.43/1.01  
% 2.43/1.01  --superposition_flag                    true
% 2.43/1.01  --sup_passive_queue_type                priority_queues
% 2.43/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.01  --demod_completeness_check              fast
% 2.43/1.01  --demod_use_ground                      true
% 2.43/1.01  --sup_to_prop_solver                    passive
% 2.43/1.01  --sup_prop_simpl_new                    true
% 2.43/1.01  --sup_prop_simpl_given                  true
% 2.43/1.01  --sup_fun_splitting                     false
% 2.43/1.01  --sup_smt_interval                      50000
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Simplification Setup
% 2.43/1.01  
% 2.43/1.01  --sup_indices_passive                   []
% 2.43/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_full_bw                           [BwDemod]
% 2.43/1.01  --sup_immed_triv                        [TrivRules]
% 2.43/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_immed_bw_main                     []
% 2.43/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  
% 2.43/1.01  ------ Combination Options
% 2.43/1.01  
% 2.43/1.01  --comb_res_mult                         3
% 2.43/1.01  --comb_sup_mult                         2
% 2.43/1.01  --comb_inst_mult                        10
% 2.43/1.01  
% 2.43/1.01  ------ Debug Options
% 2.43/1.01  
% 2.43/1.01  --dbg_backtrace                         false
% 2.43/1.01  --dbg_dump_prop_clauses                 false
% 2.43/1.01  --dbg_dump_prop_clauses_file            -
% 2.43/1.01  --dbg_out_stat                          false
% 2.43/1.01  ------ Parsing...
% 2.43/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/1.01  ------ Proving...
% 2.43/1.01  ------ Problem Properties 
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  clauses                                 19
% 2.43/1.01  conjectures                             4
% 2.43/1.01  EPR                                     3
% 2.43/1.01  Horn                                    17
% 2.43/1.01  unary                                   9
% 2.43/1.01  binary                                  4
% 2.43/1.01  lits                                    36
% 2.43/1.01  lits eq                                 6
% 2.43/1.01  fd_pure                                 0
% 2.43/1.01  fd_pseudo                               0
% 2.43/1.01  fd_cond                                 0
% 2.43/1.01  fd_pseudo_cond                          0
% 2.43/1.01  AC symbols                              0
% 2.43/1.01  
% 2.43/1.01  ------ Schedule dynamic 5 is on 
% 2.43/1.01  
% 2.43/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  ------ 
% 2.43/1.01  Current options:
% 2.43/1.01  ------ 
% 2.43/1.01  
% 2.43/1.01  ------ Input Options
% 2.43/1.01  
% 2.43/1.01  --out_options                           all
% 2.43/1.01  --tptp_safe_out                         true
% 2.43/1.01  --problem_path                          ""
% 2.43/1.01  --include_path                          ""
% 2.43/1.01  --clausifier                            res/vclausify_rel
% 2.43/1.01  --clausifier_options                    --mode clausify
% 2.43/1.01  --stdin                                 false
% 2.43/1.01  --stats_out                             all
% 2.43/1.01  
% 2.43/1.01  ------ General Options
% 2.43/1.01  
% 2.43/1.01  --fof                                   false
% 2.43/1.01  --time_out_real                         305.
% 2.43/1.01  --time_out_virtual                      -1.
% 2.43/1.01  --symbol_type_check                     false
% 2.43/1.01  --clausify_out                          false
% 2.43/1.01  --sig_cnt_out                           false
% 2.43/1.01  --trig_cnt_out                          false
% 2.43/1.01  --trig_cnt_out_tolerance                1.
% 2.43/1.01  --trig_cnt_out_sk_spl                   false
% 2.43/1.01  --abstr_cl_out                          false
% 2.43/1.01  
% 2.43/1.01  ------ Global Options
% 2.43/1.01  
% 2.43/1.01  --schedule                              default
% 2.43/1.01  --add_important_lit                     false
% 2.43/1.01  --prop_solver_per_cl                    1000
% 2.43/1.01  --min_unsat_core                        false
% 2.43/1.01  --soft_assumptions                      false
% 2.43/1.01  --soft_lemma_size                       3
% 2.43/1.01  --prop_impl_unit_size                   0
% 2.43/1.01  --prop_impl_unit                        []
% 2.43/1.01  --share_sel_clauses                     true
% 2.43/1.01  --reset_solvers                         false
% 2.43/1.01  --bc_imp_inh                            [conj_cone]
% 2.43/1.01  --conj_cone_tolerance                   3.
% 2.43/1.01  --extra_neg_conj                        none
% 2.43/1.01  --large_theory_mode                     true
% 2.43/1.01  --prolific_symb_bound                   200
% 2.43/1.01  --lt_threshold                          2000
% 2.43/1.01  --clause_weak_htbl                      true
% 2.43/1.01  --gc_record_bc_elim                     false
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing Options
% 2.43/1.01  
% 2.43/1.01  --preprocessing_flag                    true
% 2.43/1.01  --time_out_prep_mult                    0.1
% 2.43/1.01  --splitting_mode                        input
% 2.43/1.01  --splitting_grd                         true
% 2.43/1.01  --splitting_cvd                         false
% 2.43/1.01  --splitting_cvd_svl                     false
% 2.43/1.01  --splitting_nvd                         32
% 2.43/1.01  --sub_typing                            true
% 2.43/1.01  --prep_gs_sim                           true
% 2.43/1.01  --prep_unflatten                        true
% 2.43/1.01  --prep_res_sim                          true
% 2.43/1.01  --prep_upred                            true
% 2.43/1.01  --prep_sem_filter                       exhaustive
% 2.43/1.01  --prep_sem_filter_out                   false
% 2.43/1.01  --pred_elim                             true
% 2.43/1.01  --res_sim_input                         true
% 2.43/1.01  --eq_ax_congr_red                       true
% 2.43/1.01  --pure_diseq_elim                       true
% 2.43/1.01  --brand_transform                       false
% 2.43/1.01  --non_eq_to_eq                          false
% 2.43/1.01  --prep_def_merge                        true
% 2.43/1.01  --prep_def_merge_prop_impl              false
% 2.43/1.01  --prep_def_merge_mbd                    true
% 2.43/1.01  --prep_def_merge_tr_red                 false
% 2.43/1.01  --prep_def_merge_tr_cl                  false
% 2.43/1.01  --smt_preprocessing                     true
% 2.43/1.01  --smt_ac_axioms                         fast
% 2.43/1.01  --preprocessed_out                      false
% 2.43/1.01  --preprocessed_stats                    false
% 2.43/1.01  
% 2.43/1.01  ------ Abstraction refinement Options
% 2.43/1.01  
% 2.43/1.01  --abstr_ref                             []
% 2.43/1.01  --abstr_ref_prep                        false
% 2.43/1.01  --abstr_ref_until_sat                   false
% 2.43/1.01  --abstr_ref_sig_restrict                funpre
% 2.43/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.01  --abstr_ref_under                       []
% 2.43/1.01  
% 2.43/1.01  ------ SAT Options
% 2.43/1.01  
% 2.43/1.01  --sat_mode                              false
% 2.43/1.01  --sat_fm_restart_options                ""
% 2.43/1.01  --sat_gr_def                            false
% 2.43/1.01  --sat_epr_types                         true
% 2.43/1.01  --sat_non_cyclic_types                  false
% 2.43/1.01  --sat_finite_models                     false
% 2.43/1.01  --sat_fm_lemmas                         false
% 2.43/1.01  --sat_fm_prep                           false
% 2.43/1.01  --sat_fm_uc_incr                        true
% 2.43/1.01  --sat_out_model                         small
% 2.43/1.01  --sat_out_clauses                       false
% 2.43/1.01  
% 2.43/1.01  ------ QBF Options
% 2.43/1.01  
% 2.43/1.01  --qbf_mode                              false
% 2.43/1.01  --qbf_elim_univ                         false
% 2.43/1.01  --qbf_dom_inst                          none
% 2.43/1.01  --qbf_dom_pre_inst                      false
% 2.43/1.01  --qbf_sk_in                             false
% 2.43/1.01  --qbf_pred_elim                         true
% 2.43/1.01  --qbf_split                             512
% 2.43/1.01  
% 2.43/1.01  ------ BMC1 Options
% 2.43/1.01  
% 2.43/1.01  --bmc1_incremental                      false
% 2.43/1.01  --bmc1_axioms                           reachable_all
% 2.43/1.01  --bmc1_min_bound                        0
% 2.43/1.01  --bmc1_max_bound                        -1
% 2.43/1.01  --bmc1_max_bound_default                -1
% 2.43/1.01  --bmc1_symbol_reachability              true
% 2.43/1.01  --bmc1_property_lemmas                  false
% 2.43/1.01  --bmc1_k_induction                      false
% 2.43/1.01  --bmc1_non_equiv_states                 false
% 2.43/1.01  --bmc1_deadlock                         false
% 2.43/1.01  --bmc1_ucm                              false
% 2.43/1.01  --bmc1_add_unsat_core                   none
% 2.43/1.01  --bmc1_unsat_core_children              false
% 2.43/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.01  --bmc1_out_stat                         full
% 2.43/1.01  --bmc1_ground_init                      false
% 2.43/1.01  --bmc1_pre_inst_next_state              false
% 2.43/1.01  --bmc1_pre_inst_state                   false
% 2.43/1.01  --bmc1_pre_inst_reach_state             false
% 2.43/1.01  --bmc1_out_unsat_core                   false
% 2.43/1.01  --bmc1_aig_witness_out                  false
% 2.43/1.01  --bmc1_verbose                          false
% 2.43/1.01  --bmc1_dump_clauses_tptp                false
% 2.43/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.01  --bmc1_dump_file                        -
% 2.43/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.01  --bmc1_ucm_extend_mode                  1
% 2.43/1.01  --bmc1_ucm_init_mode                    2
% 2.43/1.01  --bmc1_ucm_cone_mode                    none
% 2.43/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.01  --bmc1_ucm_relax_model                  4
% 2.43/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.01  --bmc1_ucm_layered_model                none
% 2.43/1.01  --bmc1_ucm_max_lemma_size               10
% 2.43/1.01  
% 2.43/1.01  ------ AIG Options
% 2.43/1.01  
% 2.43/1.01  --aig_mode                              false
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation Options
% 2.43/1.01  
% 2.43/1.01  --instantiation_flag                    true
% 2.43/1.01  --inst_sos_flag                         false
% 2.43/1.01  --inst_sos_phase                        true
% 2.43/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel_side                     none
% 2.43/1.01  --inst_solver_per_active                1400
% 2.43/1.01  --inst_solver_calls_frac                1.
% 2.43/1.01  --inst_passive_queue_type               priority_queues
% 2.43/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.01  --inst_passive_queues_freq              [25;2]
% 2.43/1.01  --inst_dismatching                      true
% 2.43/1.01  --inst_eager_unprocessed_to_passive     true
% 2.43/1.01  --inst_prop_sim_given                   true
% 2.43/1.01  --inst_prop_sim_new                     false
% 2.43/1.01  --inst_subs_new                         false
% 2.43/1.01  --inst_eq_res_simp                      false
% 2.43/1.01  --inst_subs_given                       false
% 2.43/1.01  --inst_orphan_elimination               true
% 2.43/1.01  --inst_learning_loop_flag               true
% 2.43/1.01  --inst_learning_start                   3000
% 2.43/1.01  --inst_learning_factor                  2
% 2.43/1.01  --inst_start_prop_sim_after_learn       3
% 2.43/1.01  --inst_sel_renew                        solver
% 2.43/1.01  --inst_lit_activity_flag                true
% 2.43/1.01  --inst_restr_to_given                   false
% 2.43/1.01  --inst_activity_threshold               500
% 2.43/1.01  --inst_out_proof                        true
% 2.43/1.01  
% 2.43/1.01  ------ Resolution Options
% 2.43/1.01  
% 2.43/1.01  --resolution_flag                       false
% 2.43/1.01  --res_lit_sel                           adaptive
% 2.43/1.01  --res_lit_sel_side                      none
% 2.43/1.01  --res_ordering                          kbo
% 2.43/1.01  --res_to_prop_solver                    active
% 2.43/1.01  --res_prop_simpl_new                    false
% 2.43/1.01  --res_prop_simpl_given                  true
% 2.43/1.01  --res_passive_queue_type                priority_queues
% 2.43/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.01  --res_passive_queues_freq               [15;5]
% 2.43/1.01  --res_forward_subs                      full
% 2.43/1.01  --res_backward_subs                     full
% 2.43/1.01  --res_forward_subs_resolution           true
% 2.43/1.01  --res_backward_subs_resolution          true
% 2.43/1.01  --res_orphan_elimination                true
% 2.43/1.01  --res_time_limit                        2.
% 2.43/1.01  --res_out_proof                         true
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Options
% 2.43/1.01  
% 2.43/1.01  --superposition_flag                    true
% 2.43/1.01  --sup_passive_queue_type                priority_queues
% 2.43/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.01  --demod_completeness_check              fast
% 2.43/1.01  --demod_use_ground                      true
% 2.43/1.01  --sup_to_prop_solver                    passive
% 2.43/1.01  --sup_prop_simpl_new                    true
% 2.43/1.01  --sup_prop_simpl_given                  true
% 2.43/1.01  --sup_fun_splitting                     false
% 2.43/1.01  --sup_smt_interval                      50000
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Simplification Setup
% 2.43/1.01  
% 2.43/1.01  --sup_indices_passive                   []
% 2.43/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_full_bw                           [BwDemod]
% 2.43/1.01  --sup_immed_triv                        [TrivRules]
% 2.43/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_immed_bw_main                     []
% 2.43/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  
% 2.43/1.01  ------ Combination Options
% 2.43/1.01  
% 2.43/1.01  --comb_res_mult                         3
% 2.43/1.01  --comb_sup_mult                         2
% 2.43/1.01  --comb_inst_mult                        10
% 2.43/1.01  
% 2.43/1.01  ------ Debug Options
% 2.43/1.01  
% 2.43/1.01  --dbg_backtrace                         false
% 2.43/1.01  --dbg_dump_prop_clauses                 false
% 2.43/1.01  --dbg_dump_prop_clauses_file            -
% 2.43/1.01  --dbg_out_stat                          false
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  ------ Proving...
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  % SZS status Theorem for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  fof(f23,conjecture,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f24,negated_conjecture,(
% 2.43/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 2.43/1.01    inference(negated_conjecture,[],[f23])).
% 2.43/1.01  
% 2.43/1.01  fof(f34,plain,(
% 2.43/1.01    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f24])).
% 2.43/1.01  
% 2.43/1.01  fof(f36,plain,(
% 2.43/1.01    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.43/1.01    inference(nnf_transformation,[],[f34])).
% 2.43/1.01  
% 2.43/1.01  fof(f37,plain,(
% 2.43/1.01    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.43/1.01    inference(flattening,[],[f36])).
% 2.43/1.01  
% 2.43/1.01  fof(f39,plain,(
% 2.43/1.01    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(X1,k3_subset_1(X0,sK2)) | ~r1_xboole_0(X1,sK2)) & (r1_tarski(X1,k3_subset_1(X0,sK2)) | r1_xboole_0(X1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f38,plain,(
% 2.43/1.01    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f40,plain,(
% 2.43/1.01    ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f39,f38])).
% 2.43/1.01  
% 2.43/1.01  fof(f66,plain,(
% 2.43/1.01    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.43/1.01    inference(cnf_transformation,[],[f40])).
% 2.43/1.01  
% 2.43/1.01  fof(f18,axiom,(
% 2.43/1.01    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f58,plain,(
% 2.43/1.01    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.43/1.01    inference(cnf_transformation,[],[f18])).
% 2.43/1.01  
% 2.43/1.01  fof(f19,axiom,(
% 2.43/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f30,plain,(
% 2.43/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f19])).
% 2.43/1.01  
% 2.43/1.01  fof(f35,plain,(
% 2.43/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.43/1.01    inference(nnf_transformation,[],[f30])).
% 2.43/1.01  
% 2.43/1.01  fof(f59,plain,(
% 2.43/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f35])).
% 2.43/1.01  
% 2.43/1.01  fof(f16,axiom,(
% 2.43/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f29,plain,(
% 2.43/1.01    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 2.43/1.01    inference(ennf_transformation,[],[f16])).
% 2.43/1.01  
% 2.43/1.01  fof(f56,plain,(
% 2.43/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f29])).
% 2.43/1.01  
% 2.43/1.01  fof(f21,axiom,(
% 2.43/1.01    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f64,plain,(
% 2.43/1.01    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f21])).
% 2.43/1.01  
% 2.43/1.01  fof(f5,axiom,(
% 2.43/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f25,plain,(
% 2.43/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.43/1.01    inference(ennf_transformation,[],[f5])).
% 2.43/1.01  
% 2.43/1.01  fof(f45,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f25])).
% 2.43/1.01  
% 2.43/1.01  fof(f1,axiom,(
% 2.43/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f41,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f1])).
% 2.43/1.01  
% 2.43/1.01  fof(f20,axiom,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f31,plain,(
% 2.43/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f20])).
% 2.43/1.01  
% 2.43/1.01  fof(f63,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f31])).
% 2.43/1.01  
% 2.43/1.01  fof(f3,axiom,(
% 2.43/1.01    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f43,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f3])).
% 2.43/1.01  
% 2.43/1.01  fof(f80,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.43/1.01    inference(definition_unfolding,[],[f63,f43])).
% 2.43/1.01  
% 2.43/1.01  fof(f68,plain,(
% 2.43/1.01    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 2.43/1.01    inference(cnf_transformation,[],[f40])).
% 2.43/1.01  
% 2.43/1.01  fof(f22,axiom,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f32,plain,(
% 2.43/1.01    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f22])).
% 2.43/1.01  
% 2.43/1.01  fof(f33,plain,(
% 2.43/1.01    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.43/1.01    inference(flattening,[],[f32])).
% 2.43/1.01  
% 2.43/1.01  fof(f65,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f33])).
% 2.43/1.01  
% 2.43/1.01  fof(f67,plain,(
% 2.43/1.01    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.43/1.01    inference(cnf_transformation,[],[f40])).
% 2.43/1.01  
% 2.43/1.01  fof(f69,plain,(
% 2.43/1.01    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 2.43/1.01    inference(cnf_transformation,[],[f40])).
% 2.43/1.01  
% 2.43/1.01  fof(f9,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f27,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.43/1.01    inference(ennf_transformation,[],[f9])).
% 2.43/1.01  
% 2.43/1.01  fof(f28,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 2.43/1.01    inference(flattening,[],[f27])).
% 2.43/1.01  
% 2.43/1.01  fof(f49,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f28])).
% 2.43/1.01  
% 2.43/1.01  fof(f79,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.43/1.01    inference(definition_unfolding,[],[f49,f43])).
% 2.43/1.01  
% 2.43/1.01  fof(f8,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f26,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1))),
% 2.43/1.01    inference(ennf_transformation,[],[f8])).
% 2.43/1.01  
% 2.43/1.01  fof(f48,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f26])).
% 2.43/1.01  
% 2.43/1.01  fof(f78,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1)) )),
% 2.43/1.01    inference(definition_unfolding,[],[f48,f43])).
% 2.43/1.01  
% 2.43/1.01  fof(f6,axiom,(
% 2.43/1.01    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f46,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.43/1.01    inference(cnf_transformation,[],[f6])).
% 2.43/1.01  
% 2.43/1.01  fof(f17,axiom,(
% 2.43/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f57,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f17])).
% 2.43/1.01  
% 2.43/1.01  fof(f10,axiom,(
% 2.43/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f50,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f10])).
% 2.43/1.01  
% 2.43/1.01  fof(f11,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f51,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f11])).
% 2.43/1.01  
% 2.43/1.01  fof(f12,axiom,(
% 2.43/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f52,plain,(
% 2.43/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f12])).
% 2.43/1.01  
% 2.43/1.01  fof(f13,axiom,(
% 2.43/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f53,plain,(
% 2.43/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f13])).
% 2.43/1.01  
% 2.43/1.01  fof(f14,axiom,(
% 2.43/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f54,plain,(
% 2.43/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f14])).
% 2.43/1.01  
% 2.43/1.01  fof(f15,axiom,(
% 2.43/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f55,plain,(
% 2.43/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f15])).
% 2.43/1.01  
% 2.43/1.01  fof(f70,plain,(
% 2.43/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.43/1.01    inference(definition_unfolding,[],[f54,f55])).
% 2.43/1.01  
% 2.43/1.01  fof(f71,plain,(
% 2.43/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.43/1.01    inference(definition_unfolding,[],[f53,f70])).
% 2.43/1.01  
% 2.43/1.01  fof(f72,plain,(
% 2.43/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.43/1.01    inference(definition_unfolding,[],[f52,f71])).
% 2.43/1.01  
% 2.43/1.01  fof(f73,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.43/1.01    inference(definition_unfolding,[],[f51,f72])).
% 2.43/1.01  
% 2.43/1.01  fof(f74,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.43/1.01    inference(definition_unfolding,[],[f50,f73])).
% 2.43/1.01  
% 2.43/1.01  fof(f75,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.43/1.01    inference(definition_unfolding,[],[f57,f74])).
% 2.43/1.01  
% 2.43/1.01  fof(f77,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0) )),
% 2.43/1.01    inference(definition_unfolding,[],[f46,f43,f75])).
% 2.43/1.01  
% 2.43/1.01  fof(f4,axiom,(
% 2.43/1.01    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f44,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.43/1.01    inference(cnf_transformation,[],[f4])).
% 2.43/1.01  
% 2.43/1.01  fof(f76,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 2.43/1.01    inference(definition_unfolding,[],[f44,f75])).
% 2.43/1.01  
% 2.43/1.01  fof(f2,axiom,(
% 2.43/1.01    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f42,plain,(
% 2.43/1.01    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f2])).
% 2.43/1.01  
% 2.43/1.01  fof(f7,axiom,(
% 2.43/1.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.43/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f47,plain,(
% 2.43/1.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f7])).
% 2.43/1.01  
% 2.43/1.01  cnf(c_20,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_803,plain,
% 2.43/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_9,plain,
% 2.43/1.01      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 2.43/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_13,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_8,plain,
% 2.43/1.01      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_239,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,X1)
% 2.43/1.01      | r1_tarski(X0,k3_tarski(X1))
% 2.43/1.01      | v1_xboole_0(X1) ),
% 2.43/1.01      inference(resolution,[status(thm)],[c_13,c_8]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_802,plain,
% 2.43/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.43/1.01      | r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 2.43/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1100,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.43/1.01      | r1_tarski(X0,X1) = iProver_top
% 2.43/1.01      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_9,c_802]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_15,plain,
% 2.43/1.01      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_808,plain,
% 2.43/1.01      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1868,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.43/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.43/1.01      inference(forward_subsumption_resolution,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_1100,c_808]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1874,plain,
% 2.43/1.01      ( r1_tarski(sK1,sK0) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_803,c_1868]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.43/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_815,plain,
% 2.43/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1936,plain,
% 2.43/1.01      ( k3_xboole_0(sK1,sK0) = sK1 ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1874,c_815]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_0,plain,
% 2.43/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_14,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.43/1.01      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_809,plain,
% 2.43/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.43/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1437,plain,
% 2.43/1.01      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_803,c_809]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1559,plain,
% 2.43/1.01      ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = k3_subset_1(sK0,sK1) ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_0,c_1437]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2138,plain,
% 2.43/1.01      ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_1936,c_1559]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_18,negated_conjecture,
% 2.43/1.01      ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2) ),
% 2.43/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_805,plain,
% 2.43/1.01      ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) = iProver_top
% 2.43/1.01      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_16,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.43/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.43/1.01      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 2.43/1.01      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_807,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.43/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.43/1.01      | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
% 2.43/1.01      | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1631,plain,
% 2.43/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 2.43/1.01      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 2.43/1.01      | r1_tarski(sK2,k3_subset_1(sK0,sK1)) = iProver_top
% 2.43/1.01      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_805,c_807]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_21,plain,
% 2.43/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_19,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_22,plain,
% 2.43/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1938,plain,
% 2.43/1.01      ( r1_tarski(sK2,k3_subset_1(sK0,sK1)) = iProver_top
% 2.43/1.01      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_1631,c_21,c_22]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1944,plain,
% 2.43/1.01      ( k3_xboole_0(sK2,k3_subset_1(sK0,sK1)) = sK2
% 2.43/1.01      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1938,c_815]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_804,plain,
% 2.43/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1873,plain,
% 2.43/1.01      ( r1_tarski(sK2,sK0) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_804,c_1868]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1886,plain,
% 2.43/1.01      ( k3_xboole_0(sK2,sK0) = sK2 ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1873,c_815]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2127,plain,
% 2.43/1.01      ( k3_xboole_0(sK0,sK2) = sK2 ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1886,c_0]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1436,plain,
% 2.43/1.01      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_subset_1(sK0,sK2) ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_804,c_809]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2482,plain,
% 2.43/1.01      ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_2127,c_1436]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_17,negated_conjecture,
% 2.43/1.01      ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~ r1_xboole_0(sK1,sK2) ),
% 2.43/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_806,plain,
% 2.43/1.01      ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) != iProver_top
% 2.43/1.01      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2917,plain,
% 2.43/1.01      ( r1_tarski(sK1,k5_xboole_0(sK0,sK2)) != iProver_top
% 2.43/1.01      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_2482,c_806]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_24,plain,
% 2.43/1.01      ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) != iProver_top
% 2.43/1.01      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_7,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1)
% 2.43/1.01      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 2.43/1.01      | ~ r1_xboole_0(X0,X2) ),
% 2.43/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_812,plain,
% 2.43/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.43/1.01      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 2.43/1.01      | r1_xboole_0(X0,X2) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2328,plain,
% 2.43/1.01      ( r1_tarski(X0,k3_subset_1(sK0,sK2)) = iProver_top
% 2.43/1.01      | r1_tarski(X0,sK0) != iProver_top
% 2.43/1.01      | r1_xboole_0(X0,sK2) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1436,c_812]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2382,plain,
% 2.43/1.01      ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) = iProver_top
% 2.43/1.01      | r1_tarski(sK1,sK0) != iProver_top
% 2.43/1.01      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2328]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2938,plain,
% 2.43/1.01      ( r1_xboole_0(sK1,sK2) != iProver_top ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_2917,c_24,c_1874,c_2382]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3961,plain,
% 2.43/1.01      ( k3_xboole_0(sK2,k3_subset_1(sK0,sK1)) = sK2 ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_1944,c_24,c_1874,c_2382]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4011,plain,
% 2.43/1.01      ( k3_xboole_0(sK2,k5_xboole_0(sK0,sK1)) = sK2 ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_2138,c_3961]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_6,plain,
% 2.43/1.01      ( ~ r1_xboole_0(X0,X1)
% 2.43/1.01      | r1_xboole_0(X0,X2)
% 2.43/1.01      | ~ r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 2.43/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_813,plain,
% 2.43/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 2.43/1.01      | r1_xboole_0(X0,X2) = iProver_top
% 2.43/1.01      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4523,plain,
% 2.43/1.01      ( r1_xboole_0(X0,k5_xboole_0(sK2,sK2)) != iProver_top
% 2.43/1.01      | r1_xboole_0(X0,k5_xboole_0(sK0,sK1)) != iProver_top
% 2.43/1.01      | r1_xboole_0(X0,sK2) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_4011,c_813]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4,plain,
% 2.43/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
% 2.43/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2,plain,
% 2.43/1.01      ( k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
% 2.43/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_845,plain,
% 2.43/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.43/1.01      inference(light_normalisation,[status(thm)],[c_4,c_2]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4527,plain,
% 2.43/1.01      ( r1_xboole_0(X0,k5_xboole_0(sK0,sK1)) != iProver_top
% 2.43/1.01      | r1_xboole_0(X0,sK2) = iProver_top
% 2.43/1.01      | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_4523,c_845]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4559,plain,
% 2.43/1.01      ( r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) != iProver_top
% 2.43/1.01      | r1_xboole_0(sK1,sK2) = iProver_top
% 2.43/1.01      | r1_xboole_0(sK1,k1_xboole_0) != iProver_top ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_4527]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1,plain,
% 2.43/1.01      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_816,plain,
% 2.43/1.01      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1214,plain,
% 2.43/1.01      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_0,c_816]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2139,plain,
% 2.43/1.01      ( r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1936,c_1214]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5,plain,
% 2.43/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_50,plain,
% 2.43/1.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_52,plain,
% 2.43/1.01      ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_50]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(contradiction,plain,
% 2.43/1.01      ( $false ),
% 2.43/1.01      inference(minisat,[status(thm)],[c_4559,c_2938,c_2139,c_52]) ).
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  ------                               Statistics
% 2.43/1.01  
% 2.43/1.01  ------ General
% 2.43/1.01  
% 2.43/1.01  abstr_ref_over_cycles:                  0
% 2.43/1.01  abstr_ref_under_cycles:                 0
% 2.43/1.01  gc_basic_clause_elim:                   0
% 2.43/1.01  forced_gc_time:                         0
% 2.43/1.01  parsing_time:                           0.013
% 2.43/1.01  unif_index_cands_time:                  0.
% 2.43/1.01  unif_index_add_time:                    0.
% 2.43/1.01  orderings_time:                         0.
% 2.43/1.01  out_proof_time:                         0.016
% 2.43/1.01  total_time:                             0.226
% 2.43/1.01  num_of_symbols:                         46
% 2.43/1.01  num_of_terms:                           5214
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing
% 2.43/1.01  
% 2.43/1.01  num_of_splits:                          0
% 2.43/1.01  num_of_split_atoms:                     0
% 2.43/1.01  num_of_reused_defs:                     0
% 2.43/1.01  num_eq_ax_congr_red:                    32
% 2.43/1.01  num_of_sem_filtered_clauses:            1
% 2.43/1.01  num_of_subtypes:                        0
% 2.43/1.01  monotx_restored_types:                  0
% 2.43/1.01  sat_num_of_epr_types:                   0
% 2.43/1.01  sat_num_of_non_cyclic_types:            0
% 2.43/1.01  sat_guarded_non_collapsed_types:        0
% 2.43/1.01  num_pure_diseq_elim:                    0
% 2.43/1.01  simp_replaced_by:                       0
% 2.43/1.01  res_preprocessed:                       101
% 2.43/1.01  prep_upred:                             0
% 2.43/1.01  prep_unflattend:                        0
% 2.43/1.01  smt_new_axioms:                         0
% 2.43/1.01  pred_elim_cands:                        4
% 2.43/1.01  pred_elim:                              1
% 2.43/1.01  pred_elim_cl:                           2
% 2.43/1.01  pred_elim_cycles:                       3
% 2.43/1.01  merged_defs:                            8
% 2.43/1.01  merged_defs_ncl:                        0
% 2.43/1.01  bin_hyper_res:                          8
% 2.43/1.01  prep_cycles:                            4
% 2.43/1.01  pred_elim_time:                         0.001
% 2.43/1.01  splitting_time:                         0.
% 2.43/1.01  sem_filter_time:                        0.
% 2.43/1.01  monotx_time:                            0.001
% 2.43/1.01  subtype_inf_time:                       0.
% 2.43/1.01  
% 2.43/1.01  ------ Problem properties
% 2.43/1.01  
% 2.43/1.01  clauses:                                19
% 2.43/1.01  conjectures:                            4
% 2.43/1.01  epr:                                    3
% 2.43/1.01  horn:                                   17
% 2.43/1.01  ground:                                 4
% 2.43/1.01  unary:                                  9
% 2.43/1.01  binary:                                 4
% 2.43/1.01  lits:                                   36
% 2.43/1.01  lits_eq:                                6
% 2.43/1.01  fd_pure:                                0
% 2.43/1.01  fd_pseudo:                              0
% 2.43/1.01  fd_cond:                                0
% 2.43/1.01  fd_pseudo_cond:                         0
% 2.43/1.01  ac_symbols:                             0
% 2.43/1.01  
% 2.43/1.01  ------ Propositional Solver
% 2.43/1.01  
% 2.43/1.01  prop_solver_calls:                      29
% 2.43/1.01  prop_fast_solver_calls:                 532
% 2.43/1.01  smt_solver_calls:                       0
% 2.43/1.01  smt_fast_solver_calls:                  0
% 2.43/1.01  prop_num_of_clauses:                    1879
% 2.43/1.01  prop_preprocess_simplified:             5448
% 2.43/1.01  prop_fo_subsumed:                       6
% 2.43/1.01  prop_solver_time:                       0.
% 2.43/1.01  smt_solver_time:                        0.
% 2.43/1.01  smt_fast_solver_time:                   0.
% 2.43/1.01  prop_fast_solver_time:                  0.
% 2.43/1.01  prop_unsat_core_time:                   0.
% 2.43/1.01  
% 2.43/1.01  ------ QBF
% 2.43/1.01  
% 2.43/1.01  qbf_q_res:                              0
% 2.43/1.01  qbf_num_tautologies:                    0
% 2.43/1.01  qbf_prep_cycles:                        0
% 2.43/1.01  
% 2.43/1.01  ------ BMC1
% 2.43/1.01  
% 2.43/1.01  bmc1_current_bound:                     -1
% 2.43/1.01  bmc1_last_solved_bound:                 -1
% 2.43/1.01  bmc1_unsat_core_size:                   -1
% 2.43/1.01  bmc1_unsat_core_parents_size:           -1
% 2.43/1.01  bmc1_merge_next_fun:                    0
% 2.43/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation
% 2.43/1.01  
% 2.43/1.01  inst_num_of_clauses:                    589
% 2.43/1.01  inst_num_in_passive:                    310
% 2.43/1.01  inst_num_in_active:                     251
% 2.43/1.01  inst_num_in_unprocessed:                28
% 2.43/1.01  inst_num_of_loops:                      290
% 2.43/1.01  inst_num_of_learning_restarts:          0
% 2.43/1.01  inst_num_moves_active_passive:          36
% 2.43/1.01  inst_lit_activity:                      0
% 2.43/1.01  inst_lit_activity_moves:                0
% 2.43/1.01  inst_num_tautologies:                   0
% 2.43/1.01  inst_num_prop_implied:                  0
% 2.43/1.01  inst_num_existing_simplified:           0
% 2.43/1.01  inst_num_eq_res_simplified:             0
% 2.43/1.01  inst_num_child_elim:                    0
% 2.43/1.01  inst_num_of_dismatching_blockings:      98
% 2.43/1.01  inst_num_of_non_proper_insts:           371
% 2.43/1.01  inst_num_of_duplicates:                 0
% 2.43/1.01  inst_inst_num_from_inst_to_res:         0
% 2.43/1.01  inst_dismatching_checking_time:         0.
% 2.43/1.01  
% 2.43/1.01  ------ Resolution
% 2.43/1.01  
% 2.43/1.01  res_num_of_clauses:                     0
% 2.43/1.01  res_num_in_passive:                     0
% 2.43/1.01  res_num_in_active:                      0
% 2.43/1.01  res_num_of_loops:                       105
% 2.43/1.01  res_forward_subset_subsumed:            16
% 2.43/1.01  res_backward_subset_subsumed:           0
% 2.43/1.01  res_forward_subsumed:                   0
% 2.43/1.01  res_backward_subsumed:                  0
% 2.43/1.01  res_forward_subsumption_resolution:     0
% 2.43/1.01  res_backward_subsumption_resolution:    0
% 2.43/1.01  res_clause_to_clause_subsumption:       176
% 2.43/1.01  res_orphan_elimination:                 0
% 2.43/1.01  res_tautology_del:                      44
% 2.43/1.01  res_num_eq_res_simplified:              0
% 2.43/1.01  res_num_sel_changes:                    0
% 2.43/1.01  res_moves_from_active_to_pass:          0
% 2.43/1.01  
% 2.43/1.01  ------ Superposition
% 2.43/1.01  
% 2.43/1.01  sup_time_total:                         0.
% 2.43/1.01  sup_time_generating:                    0.
% 2.43/1.01  sup_time_sim_full:                      0.
% 2.43/1.01  sup_time_sim_immed:                     0.
% 2.43/1.01  
% 2.43/1.01  sup_num_of_clauses:                     90
% 2.43/1.01  sup_num_in_active:                      43
% 2.43/1.01  sup_num_in_passive:                     47
% 2.43/1.01  sup_num_of_loops:                       56
% 2.43/1.01  sup_fw_superposition:                   71
% 2.43/1.01  sup_bw_superposition:                   53
% 2.43/1.01  sup_immediate_simplified:               26
% 2.43/1.01  sup_given_eliminated:                   0
% 2.43/1.01  comparisons_done:                       0
% 2.43/1.01  comparisons_avoided:                    0
% 2.43/1.01  
% 2.43/1.01  ------ Simplifications
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  sim_fw_subset_subsumed:                 2
% 2.43/1.01  sim_bw_subset_subsumed:                 2
% 2.43/1.01  sim_fw_subsumed:                        4
% 2.43/1.01  sim_bw_subsumed:                        0
% 2.43/1.01  sim_fw_subsumption_res:                 1
% 2.43/1.01  sim_bw_subsumption_res:                 0
% 2.43/1.01  sim_tautology_del:                      3
% 2.43/1.01  sim_eq_tautology_del:                   3
% 2.43/1.01  sim_eq_res_simp:                        0
% 2.43/1.01  sim_fw_demodulated:                     14
% 2.43/1.01  sim_bw_demodulated:                     14
% 2.43/1.01  sim_light_normalised:                   8
% 2.43/1.01  sim_joinable_taut:                      0
% 2.43/1.01  sim_joinable_simp:                      0
% 2.43/1.01  sim_ac_normalised:                      0
% 2.43/1.01  sim_smt_subsumption:                    0
% 2.43/1.01  
%------------------------------------------------------------------------------
