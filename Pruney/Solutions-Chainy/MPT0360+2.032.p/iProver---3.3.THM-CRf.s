%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:19 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 245 expanded)
%              Number of clauses        :   57 (  76 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   18
%              Number of atoms          :  279 ( 734 expanded)
%              Number of equality atoms :   85 ( 168 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK2
      & r1_tarski(sK2,k3_subset_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_xboole_0 != sK2
    & r1_tarski(sK2,k3_subset_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f40])).

fof(f69,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f49,f44])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f74,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f72,f73])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_634,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_633,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_640,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3410,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_633,c_640])).

cnf(c_1191,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[status(thm)],[c_16,c_24])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1202,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1191,c_17])).

cnf(c_1203,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1202])).

cnf(c_3611,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3410,c_1203])).

cnf(c_12,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_647,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1981,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_647])).

cnf(c_3618,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3611,c_1981])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_649,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4934,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_649])).

cnf(c_6978,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_4934])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_648,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7334,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_6978,c_648])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_8,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_646,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1169,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X1),k1_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_646])).

cnf(c_7345,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7334,c_1169])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7351,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7345,c_4,c_5])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_644,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8419,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7351,c_644])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k3_subset_1(X1,X0))
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5053,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_18,c_22])).

cnf(c_635,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_638,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3023,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(sK3,k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_638])).

cnf(c_3030,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3023])).

cnf(c_5070,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5053,c_24,c_3030])).

cnf(c_5206,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ r1_tarski(k3_subset_1(sK1,sK2),X0)
    | r1_tarski(sK3,X0) ),
    inference(resolution,[status(thm)],[c_5070,c_2])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1432,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK2,X0) ),
    inference(resolution,[status(thm)],[c_2,c_23])).

cnf(c_5211,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_5070,c_1432])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_5224,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_5211,c_20])).

cnf(c_5227,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5206,c_21,c_5224])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_123,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_1])).

cnf(c_124,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_123])).

cnf(c_5417,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(resolution,[status(thm)],[c_5227,c_124])).

cnf(c_5418,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5417])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8419,c_5418])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:09 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.07/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.03  
% 3.07/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/1.03  
% 3.07/1.03  ------  iProver source info
% 3.07/1.03  
% 3.07/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.07/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/1.03  git: non_committed_changes: false
% 3.07/1.03  git: last_make_outside_of_git: false
% 3.07/1.03  
% 3.07/1.03  ------ 
% 3.07/1.03  ------ Parsing...
% 3.07/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/1.03  
% 3.07/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.07/1.03  
% 3.07/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/1.03  
% 3.07/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/1.03  ------ Proving...
% 3.07/1.03  ------ Problem Properties 
% 3.07/1.03  
% 3.07/1.03  
% 3.07/1.03  clauses                                 25
% 3.07/1.03  conjectures                             4
% 3.07/1.03  EPR                                     8
% 3.07/1.03  Horn                                    23
% 3.07/1.03  unary                                   10
% 3.07/1.03  binary                                  8
% 3.07/1.03  lits                                    48
% 3.07/1.03  lits eq                                 7
% 3.07/1.03  fd_pure                                 0
% 3.07/1.03  fd_pseudo                               0
% 3.07/1.03  fd_cond                                 1
% 3.07/1.03  fd_pseudo_cond                          0
% 3.07/1.03  AC symbols                              0
% 3.07/1.03  
% 3.07/1.03  ------ Input Options Time Limit: Unbounded
% 3.07/1.03  
% 3.07/1.03  
% 3.07/1.03  ------ 
% 3.07/1.03  Current options:
% 3.07/1.03  ------ 
% 3.07/1.03  
% 3.07/1.03  
% 3.07/1.03  
% 3.07/1.03  
% 3.07/1.03  ------ Proving...
% 3.07/1.03  
% 3.07/1.03  
% 3.07/1.03  % SZS status Theorem for theBenchmark.p
% 3.07/1.03  
% 3.07/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/1.03  
% 3.07/1.03  fof(f20,conjecture,(
% 3.07/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f21,negated_conjecture,(
% 3.07/1.03    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 3.07/1.03    inference(negated_conjecture,[],[f20])).
% 3.07/1.03  
% 3.07/1.03  fof(f30,plain,(
% 3.07/1.03    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.07/1.03    inference(ennf_transformation,[],[f21])).
% 3.07/1.03  
% 3.07/1.03  fof(f31,plain,(
% 3.07/1.03    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.07/1.03    inference(flattening,[],[f30])).
% 3.07/1.03  
% 3.07/1.03  fof(f40,plain,(
% 3.07/1.03    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 3.07/1.03    introduced(choice_axiom,[])).
% 3.07/1.03  
% 3.07/1.03  fof(f41,plain,(
% 3.07/1.03    k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f40])).
% 3.07/1.03  
% 3.07/1.03  fof(f69,plain,(
% 3.07/1.03    r1_tarski(sK2,sK3)),
% 3.07/1.03    inference(cnf_transformation,[],[f41])).
% 3.07/1.03  
% 3.07/1.03  fof(f68,plain,(
% 3.07/1.03    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.07/1.03    inference(cnf_transformation,[],[f41])).
% 3.07/1.03  
% 3.07/1.03  fof(f15,axiom,(
% 3.07/1.03    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f26,plain,(
% 3.07/1.03    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.07/1.03    inference(ennf_transformation,[],[f15])).
% 3.07/1.03  
% 3.07/1.03  fof(f38,plain,(
% 3.07/1.03    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.07/1.03    inference(nnf_transformation,[],[f26])).
% 3.07/1.03  
% 3.07/1.03  fof(f59,plain,(
% 3.07/1.03    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f38])).
% 3.07/1.03  
% 3.07/1.03  fof(f17,axiom,(
% 3.07/1.03    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f64,plain,(
% 3.07/1.03    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.07/1.03    inference(cnf_transformation,[],[f17])).
% 3.07/1.03  
% 3.07/1.03  fof(f14,axiom,(
% 3.07/1.03    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f58,plain,(
% 3.07/1.03    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.07/1.03    inference(cnf_transformation,[],[f14])).
% 3.07/1.03  
% 3.07/1.03  fof(f10,axiom,(
% 3.07/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f25,plain,(
% 3.07/1.03    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 3.07/1.03    inference(ennf_transformation,[],[f10])).
% 3.07/1.03  
% 3.07/1.03  fof(f52,plain,(
% 3.07/1.03    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f25])).
% 3.07/1.03  
% 3.07/1.03  fof(f3,axiom,(
% 3.07/1.03    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f22,plain,(
% 3.07/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.07/1.03    inference(ennf_transformation,[],[f3])).
% 3.07/1.03  
% 3.07/1.03  fof(f23,plain,(
% 3.07/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.07/1.03    inference(flattening,[],[f22])).
% 3.07/1.03  
% 3.07/1.03  fof(f45,plain,(
% 3.07/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f23])).
% 3.07/1.03  
% 3.07/1.03  fof(f4,axiom,(
% 3.07/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f24,plain,(
% 3.07/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.07/1.03    inference(ennf_transformation,[],[f4])).
% 3.07/1.03  
% 3.07/1.03  fof(f46,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f24])).
% 3.07/1.03  
% 3.07/1.03  fof(f11,axiom,(
% 3.07/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f53,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.07/1.03    inference(cnf_transformation,[],[f11])).
% 3.07/1.03  
% 3.07/1.03  fof(f7,axiom,(
% 3.07/1.03    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f49,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f7])).
% 3.07/1.03  
% 3.07/1.03  fof(f2,axiom,(
% 3.07/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f44,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.07/1.03    inference(cnf_transformation,[],[f2])).
% 3.07/1.03  
% 3.07/1.03  fof(f72,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.07/1.03    inference(definition_unfolding,[],[f49,f44])).
% 3.07/1.03  
% 3.07/1.03  fof(f8,axiom,(
% 3.07/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f50,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f8])).
% 3.07/1.03  
% 3.07/1.03  fof(f9,axiom,(
% 3.07/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f51,plain,(
% 3.07/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f9])).
% 3.07/1.03  
% 3.07/1.03  fof(f73,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.07/1.03    inference(definition_unfolding,[],[f50,f51])).
% 3.07/1.03  
% 3.07/1.03  fof(f74,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.07/1.03    inference(definition_unfolding,[],[f53,f72,f73])).
% 3.07/1.03  
% 3.07/1.03  fof(f12,axiom,(
% 3.07/1.03    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f54,plain,(
% 3.07/1.03    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 3.07/1.03    inference(cnf_transformation,[],[f12])).
% 3.07/1.03  
% 3.07/1.03  fof(f5,axiom,(
% 3.07/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f47,plain,(
% 3.07/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.07/1.03    inference(cnf_transformation,[],[f5])).
% 3.07/1.03  
% 3.07/1.03  fof(f6,axiom,(
% 3.07/1.03    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f48,plain,(
% 3.07/1.03    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.07/1.03    inference(cnf_transformation,[],[f6])).
% 3.07/1.03  
% 3.07/1.03  fof(f13,axiom,(
% 3.07/1.03    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f36,plain,(
% 3.07/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.07/1.03    inference(nnf_transformation,[],[f13])).
% 3.07/1.03  
% 3.07/1.03  fof(f37,plain,(
% 3.07/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.07/1.03    inference(flattening,[],[f36])).
% 3.07/1.03  
% 3.07/1.03  fof(f56,plain,(
% 3.07/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f37])).
% 3.07/1.03  
% 3.07/1.03  fof(f76,plain,(
% 3.07/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 3.07/1.03    inference(definition_unfolding,[],[f56,f73])).
% 3.07/1.03  
% 3.07/1.03  fof(f18,axiom,(
% 3.07/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f27,plain,(
% 3.07/1.03    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/1.03    inference(ennf_transformation,[],[f18])).
% 3.07/1.03  
% 3.07/1.03  fof(f28,plain,(
% 3.07/1.03    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/1.03    inference(flattening,[],[f27])).
% 3.07/1.03  
% 3.07/1.03  fof(f65,plain,(
% 3.07/1.03    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.07/1.03    inference(cnf_transformation,[],[f28])).
% 3.07/1.03  
% 3.07/1.03  fof(f70,plain,(
% 3.07/1.03    r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 3.07/1.03    inference(cnf_transformation,[],[f41])).
% 3.07/1.03  
% 3.07/1.03  fof(f71,plain,(
% 3.07/1.03    k1_xboole_0 != sK2),
% 3.07/1.03    inference(cnf_transformation,[],[f41])).
% 3.07/1.03  
% 3.07/1.03  fof(f19,axiom,(
% 3.07/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f29,plain,(
% 3.07/1.03    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/1.03    inference(ennf_transformation,[],[f19])).
% 3.07/1.03  
% 3.07/1.03  fof(f39,plain,(
% 3.07/1.03    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/1.03    inference(nnf_transformation,[],[f29])).
% 3.07/1.03  
% 3.07/1.03  fof(f66,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.07/1.03    inference(cnf_transformation,[],[f39])).
% 3.07/1.03  
% 3.07/1.03  fof(f16,axiom,(
% 3.07/1.03    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f63,plain,(
% 3.07/1.03    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f16])).
% 3.07/1.03  
% 3.07/1.03  fof(f79,plain,(
% 3.07/1.03    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.07/1.03    inference(definition_unfolding,[],[f66,f63])).
% 3.07/1.03  
% 3.07/1.03  fof(f60,plain,(
% 3.07/1.03    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f38])).
% 3.07/1.03  
% 3.07/1.03  fof(f1,axiom,(
% 3.07/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.03  
% 3.07/1.03  fof(f32,plain,(
% 3.07/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.07/1.03    inference(nnf_transformation,[],[f1])).
% 3.07/1.03  
% 3.07/1.03  fof(f33,plain,(
% 3.07/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/1.03    inference(rectify,[],[f32])).
% 3.07/1.03  
% 3.07/1.03  fof(f34,plain,(
% 3.07/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.07/1.03    introduced(choice_axiom,[])).
% 3.07/1.03  
% 3.07/1.03  fof(f35,plain,(
% 3.07/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.07/1.03  
% 3.07/1.03  fof(f42,plain,(
% 3.07/1.03    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.07/1.03    inference(cnf_transformation,[],[f35])).
% 3.07/1.03  
% 3.07/1.03  cnf(c_23,negated_conjecture,
% 3.07/1.03      ( r1_tarski(sK2,sK3) ),
% 3.07/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_634,plain,
% 3.07/1.03      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_24,negated_conjecture,
% 3.07/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.07/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_633,plain,
% 3.07/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_16,plain,
% 3.07/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.07/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_640,plain,
% 3.07/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 3.07/1.03      | r2_hidden(X0,X1) = iProver_top
% 3.07/1.03      | v1_xboole_0(X1) = iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_3410,plain,
% 3.07/1.03      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 3.07/1.03      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_633,c_640]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_1191,plain,
% 3.07/1.03      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.07/1.03      inference(resolution,[status(thm)],[c_16,c_24]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_17,plain,
% 3.07/1.03      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.07/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_1202,plain,
% 3.07/1.03      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 3.07/1.03      inference(forward_subsumption_resolution,
% 3.07/1.03                [status(thm)],
% 3.07/1.03                [c_1191,c_17]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_1203,plain,
% 3.07/1.03      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_1202]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_3611,plain,
% 3.07/1.03      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.07/1.03      inference(global_propositional_subsumption,
% 3.07/1.03                [status(thm)],
% 3.07/1.03                [c_3410,c_1203]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_12,plain,
% 3.07/1.03      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.07/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_6,plain,
% 3.07/1.03      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 3.07/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_647,plain,
% 3.07/1.03      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 3.07/1.03      | r2_hidden(X0,X1) != iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_1981,plain,
% 3.07/1.03      ( r1_tarski(X0,X1) = iProver_top
% 3.07/1.03      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_12,c_647]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_3618,plain,
% 3.07/1.03      ( r1_tarski(sK3,sK1) = iProver_top ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_3611,c_1981]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_2,plain,
% 3.07/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.07/1.03      inference(cnf_transformation,[],[f45]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_649,plain,
% 3.07/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.07/1.03      | r1_tarski(X2,X0) != iProver_top
% 3.07/1.03      | r1_tarski(X2,X1) = iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_4934,plain,
% 3.07/1.03      ( r1_tarski(X0,sK3) != iProver_top
% 3.07/1.03      | r1_tarski(X0,sK1) = iProver_top ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_3618,c_649]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_6978,plain,
% 3.07/1.03      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_634,c_4934]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_3,plain,
% 3.07/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.07/1.03      inference(cnf_transformation,[],[f46]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_648,plain,
% 3.07/1.03      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_7334,plain,
% 3.07/1.03      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_6978,c_648]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_7,plain,
% 3.07/1.03      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 3.07/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_8,plain,
% 3.07/1.03      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
% 3.07/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_646,plain,
% 3.07/1.03      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_1169,plain,
% 3.07/1.03      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),k1_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = iProver_top ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_7,c_646]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_7345,plain,
% 3.07/1.03      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),k1_zfmisc_1(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))) = iProver_top ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_7334,c_1169]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_4,plain,
% 3.07/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.07/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_5,plain,
% 3.07/1.03      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.07/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_7351,plain,
% 3.07/1.03      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.07/1.03      inference(demodulation,[status(thm)],[c_7345,c_4,c_5]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_10,plain,
% 3.07/1.03      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2) ),
% 3.07/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_644,plain,
% 3.07/1.03      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) != iProver_top
% 3.07/1.03      | r2_hidden(X1,X2) = iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_8419,plain,
% 3.07/1.03      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_7351,c_644]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_18,plain,
% 3.07/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.07/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.07/1.03      | ~ r1_tarski(X2,k3_subset_1(X1,X0))
% 3.07/1.03      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 3.07/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_22,negated_conjecture,
% 3.07/1.03      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
% 3.07/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_5053,plain,
% 3.07/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.07/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 3.07/1.03      | r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
% 3.07/1.03      inference(resolution,[status(thm)],[c_18,c_22]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_635,plain,
% 3.07/1.03      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_638,plain,
% 3.07/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.07/1.03      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.07/1.03      | r1_tarski(X2,k3_subset_1(X1,X0)) != iProver_top
% 3.07/1.03      | r1_tarski(X0,k3_subset_1(X1,X2)) = iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_3023,plain,
% 3.07/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 3.07/1.03      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 3.07/1.03      | r1_tarski(sK3,k3_subset_1(sK1,sK2)) = iProver_top ),
% 3.07/1.03      inference(superposition,[status(thm)],[c_635,c_638]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_3030,plain,
% 3.07/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.07/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 3.07/1.03      | r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
% 3.07/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3023]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_5070,plain,
% 3.07/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 3.07/1.03      | r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
% 3.07/1.03      inference(global_propositional_subsumption,
% 3.07/1.03                [status(thm)],
% 3.07/1.03                [c_5053,c_24,c_3030]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_5206,plain,
% 3.07/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 3.07/1.03      | ~ r1_tarski(k3_subset_1(sK1,sK2),X0)
% 3.07/1.03      | r1_tarski(sK3,X0) ),
% 3.07/1.03      inference(resolution,[status(thm)],[c_5070,c_2]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_21,negated_conjecture,
% 3.07/1.03      ( k1_xboole_0 != sK2 ),
% 3.07/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_1432,plain,
% 3.07/1.03      ( ~ r1_tarski(sK3,X0) | r1_tarski(sK2,X0) ),
% 3.07/1.03      inference(resolution,[status(thm)],[c_2,c_23]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_5211,plain,
% 3.07/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 3.07/1.03      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
% 3.07/1.03      inference(resolution,[status(thm)],[c_5070,c_1432]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_20,plain,
% 3.07/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.07/1.03      | ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 3.07/1.03      | k1_xboole_0 = X0 ),
% 3.07/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_5224,plain,
% 3.07/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) | k1_xboole_0 = sK2 ),
% 3.07/1.03      inference(resolution,[status(thm)],[c_5211,c_20]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_5227,plain,
% 3.07/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.07/1.03      inference(global_propositional_subsumption,
% 3.07/1.03                [status(thm)],
% 3.07/1.03                [c_5206,c_21,c_5224]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_15,plain,
% 3.07/1.03      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.07/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_1,plain,
% 3.07/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.07/1.03      inference(cnf_transformation,[],[f42]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_123,plain,
% 3.07/1.03      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.07/1.03      inference(global_propositional_subsumption,
% 3.07/1.03                [status(thm)],
% 3.07/1.03                [c_15,c_1]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_124,plain,
% 3.07/1.03      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.07/1.03      inference(renaming,[status(thm)],[c_123]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_5417,plain,
% 3.07/1.03      ( ~ r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 3.07/1.03      inference(resolution,[status(thm)],[c_5227,c_124]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(c_5418,plain,
% 3.07/1.03      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.07/1.03      inference(predicate_to_equality,[status(thm)],[c_5417]) ).
% 3.07/1.03  
% 3.07/1.03  cnf(contradiction,plain,
% 3.07/1.03      ( $false ),
% 3.07/1.03      inference(minisat,[status(thm)],[c_8419,c_5418]) ).
% 3.07/1.03  
% 3.07/1.03  
% 3.07/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/1.03  
% 3.07/1.03  ------                               Statistics
% 3.07/1.03  
% 3.07/1.03  ------ Selected
% 3.07/1.03  
% 3.07/1.03  total_time:                             0.366
% 3.07/1.03  
%------------------------------------------------------------------------------
