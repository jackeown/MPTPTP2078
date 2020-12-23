%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:02 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  243 (52467 expanded)
%              Number of clauses        :  188 (18112 expanded)
%              Number of leaves         :   20 (12360 expanded)
%              Depth                    :   44
%              Number of atoms          :  408 (104566 expanded)
%              Number of equality atoms :  250 (56956 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK1) != sK2
        | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & ( k2_subset_1(sK1) = sK2
        | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k2_subset_1(sK1) != sK2
      | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & ( k2_subset_1(sK1) = sK2
      | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f28])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f36,f32,f32])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f32])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f38,f32])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f53,f53])).

fof(f51,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,
    ( k2_subset_1(sK1) != sK2
    | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_675,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_676,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_675])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_265,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_266,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_272,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_266,c_17])).

cnf(c_797,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_676,c_272])).

cnf(c_798,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_1198,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_1367,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1198])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1207,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2535,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1367,c_1207])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1206,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2530,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1206,c_1207])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1436,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_3241,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1436,c_0])).

cnf(c_3764,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2,c_3241])).

cnf(c_7894,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2530,c_3764])).

cnf(c_7900,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2530,c_2])).

cnf(c_7923,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7894,c_2530,c_7900])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7925,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7923,c_6])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_278,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_279,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_1294,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_279])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1205,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1853,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1205])).

cnf(c_2537,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),sK1) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1853,c_1207])).

cnf(c_2846,plain,
    ( k3_xboole_0(sK1,k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2537,c_2])).

cnf(c_3767,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k3_subset_1(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2846,c_3241])).

cnf(c_1435,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2))) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1294,c_0])).

cnf(c_3113,plain,
    ( k5_xboole_0(sK1,k3_subset_1(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2846,c_1435])).

cnf(c_3791,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3767,c_2537,c_2846,c_3113])).

cnf(c_5757,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3791,c_3241])).

cnf(c_5759,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_subset_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_5757,c_1294])).

cnf(c_6307,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_5759,c_3764])).

cnf(c_6318,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_6307,c_5759])).

cnf(c_8983,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2,c_6318])).

cnf(c_9011,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_8983,c_1294])).

cnf(c_9401,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_7925,c_9011])).

cnf(c_9580,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2,c_9401])).

cnf(c_9652,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_9580,c_1294])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_256,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_246,c_17])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_677,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_678,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_677])).

cnf(c_712,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_256,c_678])).

cnf(c_1202,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_2248,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1205,c_1202])).

cnf(c_2280,plain,
    ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2248,c_0])).

cnf(c_9783,plain,
    ( k3_subset_1(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_9652,c_2280])).

cnf(c_9838,plain,
    ( k3_subset_1(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_9783,c_9652])).

cnf(c_2434,plain,
    ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_2280])).

cnf(c_7897,plain,
    ( k3_subset_1(X0,k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2530,c_2434])).

cnf(c_7917,plain,
    ( k3_subset_1(X0,k5_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7897,c_7900])).

cnf(c_7919,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7917,c_6])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3242,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1436,c_1])).

cnf(c_7892,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)),k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2530,c_3242])).

cnf(c_7927,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7892,c_2530,c_7900])).

cnf(c_7929,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7927,c_6])).

cnf(c_9475,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7929,c_7925])).

cnf(c_9840,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9838,c_7919,c_9475])).

cnf(c_9049,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) ),
    inference(superposition,[status(thm)],[c_9011,c_3764])).

cnf(c_9059,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) ),
    inference(light_normalisation,[status(thm)],[c_9049,c_9011])).

cnf(c_12675,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_9059,c_7925])).

cnf(c_12681,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_2,c_12675])).

cnf(c_12709,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
    inference(light_normalisation,[status(thm)],[c_12681,c_1294])).

cnf(c_1489,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1435,c_0])).

cnf(c_1565,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2)))) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1489,c_0])).

cnf(c_1716,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1565,c_0])).

cnf(c_2010,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2))))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1716,c_0])).

cnf(c_2121,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_2010,c_0])).

cnf(c_2209,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2)))))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_2121,c_0])).

cnf(c_4136,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_2209,c_2846,c_3113])).

cnf(c_4149,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4136,c_3241])).

cnf(c_4151,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))) = k3_subset_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4149,c_1294])).

cnf(c_4505,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_4151,c_3764])).

cnf(c_4516,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_4505,c_4151])).

cnf(c_4899,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2,c_4516])).

cnf(c_7107,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_4899,c_3791])).

cnf(c_7109,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2,c_7107])).

cnf(c_7133,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_7109,c_1294,c_3791])).

cnf(c_1852,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1205])).

cnf(c_1969,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1852])).

cnf(c_7200,plain,
    ( r1_tarski(k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_subset_1(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7133,c_1969])).

cnf(c_8678,plain,
    ( r1_tarski(k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_subset_1(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_7200])).

cnf(c_8687,plain,
    ( r1_tarski(k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8678,c_1294,c_3791])).

cnf(c_8776,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) = k3_subset_1(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_8687,c_1202])).

cnf(c_11854,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8776,c_7919,c_7925])).

cnf(c_12710,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12709,c_7925,c_11854])).

cnf(c_13585,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9840,c_12710])).

cnf(c_13629,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13585,c_6,c_7925])).

cnf(c_6305,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
    inference(superposition,[status(thm)],[c_5759,c_3242])).

cnf(c_6321,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_6305,c_5759])).

cnf(c_6308,plain,
    ( k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_5759,c_2434])).

cnf(c_6850,plain,
    ( k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_2,c_6308])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) = sK2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1203,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1222,plain,
    ( sK2 = sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1203,c_15])).

cnf(c_2532,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2)
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_1222,c_1207])).

cnf(c_2577,plain,
    ( k3_subset_1(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k3_xboole_0(k3_subset_1(sK1,sK2),sK2)
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_2532,c_2280])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1204,plain,
    ( k2_subset_1(sK1) != sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1233,plain,
    ( sK2 != sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1204,c_15])).

cnf(c_1270,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | sK2 != sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1233])).

cnf(c_929,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1287,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_1289,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_1454,plain,
    ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_930,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1457,plain,
    ( X0 != X1
    | k3_subset_1(sK1,sK2) != X1
    | k3_subset_1(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_1588,plain,
    ( X0 != k3_subset_1(sK1,sK2)
    | k3_subset_1(sK1,sK2) = X0
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_1655,plain,
    ( k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
    | k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_933,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1345,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)
    | X1 != X2
    | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1446,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)
    | k3_subset_1(sK1,sK2) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_2092,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | k3_subset_1(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | sK2 != sK1 ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_3521,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3938,plain,
    ( k3_subset_1(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k3_xboole_0(k3_subset_1(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2577,c_1270,c_1287,c_1289,c_1454,c_1655,c_2092,c_3521])).

cnf(c_6854,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1) = k3_xboole_0(k3_subset_1(sK1,sK2),sK2) ),
    inference(light_normalisation,[status(thm)],[c_6850,c_1294,c_3938])).

cnf(c_6896,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(k3_subset_1(sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_6854,c_2])).

cnf(c_6906,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_6896,c_5759])).

cnf(c_6908,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1) = k3_subset_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_6906,c_6854])).

cnf(c_2426,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_subset_1(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_2280])).

cnf(c_3279,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_2426,c_1])).

cnf(c_5076,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_3242])).

cnf(c_6215,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_3279,c_5076])).

cnf(c_6236,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_6215])).

cnf(c_7080,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
    inference(superposition,[status(thm)],[c_5759,c_6236])).

cnf(c_7086,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_7080,c_5759])).

cnf(c_6881,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
    inference(superposition,[status(thm)],[c_6854,c_2426])).

cnf(c_10385,plain,
    ( k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_6881,c_6906,c_6908,c_9401])).

cnf(c_11047,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_7086,c_6908,c_10385])).

cnf(c_11049,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2,c_11047])).

cnf(c_11053,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_11049,c_1294])).

cnf(c_1478,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_9781,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_9652,c_1478])).

cnf(c_9915,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9783,c_7919,c_9475])).

cnf(c_9949,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_9781,c_9915])).

cnf(c_9951,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_9949,c_6,c_9475])).

cnf(c_11054,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_11053,c_9475,c_9951])).

cnf(c_11858,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k3_subset_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_6321,c_6908,c_11054])).

cnf(c_13937,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k3_subset_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_13629,c_11858])).

cnf(c_2247,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1206,c_1202])).

cnf(c_5871,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2247,c_1])).

cnf(c_7855,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_2530,c_5871])).

cnf(c_5859,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_2247])).

cnf(c_7856,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2530,c_5859])).

cnf(c_7858,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7856,c_6])).

cnf(c_7860,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_7855,c_7858])).

cnf(c_7862,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_7860,c_6])).

cnf(c_13948,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_subset_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_13937,c_7862])).

cnf(c_13949,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k3_subset_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_13948,c_6,c_2530])).

cnf(c_14497,plain,
    ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2535,c_13949])).

cnf(c_7423,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_6906,c_3764])).

cnf(c_7428,plain,
    ( k3_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_6906,c_2])).

cnf(c_7431,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK2,k3_subset_1(sK1,sK2))) = k5_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_7423,c_6906,c_7428])).

cnf(c_16014,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_14497,c_7431])).

cnf(c_2255,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_subset_1(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1969,c_1202])).

cnf(c_9440,plain,
    ( k3_subset_1(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_7925,c_2255])).

cnf(c_9460,plain,
    ( k3_subset_1(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_9440,c_7925])).

cnf(c_9462,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9460,c_7919])).

cnf(c_1477,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1294,c_1])).

cnf(c_14500,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2535,c_1477])).

cnf(c_14507,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_14497,c_14500])).

cnf(c_15089,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9462,c_14507])).

cnf(c_15092,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_15089,c_6])).

cnf(c_16071,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_16014,c_2535,c_15092])).

cnf(c_7413,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6906,c_1969])).

cnf(c_16018,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14497,c_7413])).

cnf(c_16029,plain,
    ( sK2 != sK1
    | r1_tarski(k5_xboole_0(sK1,sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14497,c_1233])).

cnf(c_16060,plain,
    ( sK2 != sK1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_16018,c_16029])).

cnf(c_16074,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_16071,c_16060])).

cnf(c_16092,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16074])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.90/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.00  
% 3.90/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/1.00  
% 3.90/1.00  ------  iProver source info
% 3.90/1.00  
% 3.90/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.90/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/1.00  git: non_committed_changes: false
% 3.90/1.00  git: last_make_outside_of_git: false
% 3.90/1.00  
% 3.90/1.00  ------ 
% 3.90/1.00  
% 3.90/1.00  ------ Input Options
% 3.90/1.00  
% 3.90/1.00  --out_options                           all
% 3.90/1.00  --tptp_safe_out                         true
% 3.90/1.00  --problem_path                          ""
% 3.90/1.00  --include_path                          ""
% 3.90/1.00  --clausifier                            res/vclausify_rel
% 3.90/1.00  --clausifier_options                    --mode clausify
% 3.90/1.00  --stdin                                 false
% 3.90/1.00  --stats_out                             all
% 3.90/1.00  
% 3.90/1.00  ------ General Options
% 3.90/1.00  
% 3.90/1.00  --fof                                   false
% 3.90/1.00  --time_out_real                         305.
% 3.90/1.00  --time_out_virtual                      -1.
% 3.90/1.00  --symbol_type_check                     false
% 3.90/1.00  --clausify_out                          false
% 3.90/1.00  --sig_cnt_out                           false
% 3.90/1.00  --trig_cnt_out                          false
% 3.90/1.00  --trig_cnt_out_tolerance                1.
% 3.90/1.00  --trig_cnt_out_sk_spl                   false
% 3.90/1.00  --abstr_cl_out                          false
% 3.90/1.00  
% 3.90/1.00  ------ Global Options
% 3.90/1.00  
% 3.90/1.00  --schedule                              default
% 3.90/1.00  --add_important_lit                     false
% 3.90/1.00  --prop_solver_per_cl                    1000
% 3.90/1.00  --min_unsat_core                        false
% 3.90/1.00  --soft_assumptions                      false
% 3.90/1.00  --soft_lemma_size                       3
% 3.90/1.00  --prop_impl_unit_size                   0
% 3.90/1.00  --prop_impl_unit                        []
% 3.90/1.00  --share_sel_clauses                     true
% 3.90/1.00  --reset_solvers                         false
% 3.90/1.00  --bc_imp_inh                            [conj_cone]
% 3.90/1.00  --conj_cone_tolerance                   3.
% 3.90/1.00  --extra_neg_conj                        none
% 3.90/1.00  --large_theory_mode                     true
% 3.90/1.00  --prolific_symb_bound                   200
% 3.90/1.00  --lt_threshold                          2000
% 3.90/1.00  --clause_weak_htbl                      true
% 3.90/1.00  --gc_record_bc_elim                     false
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing Options
% 3.90/1.00  
% 3.90/1.00  --preprocessing_flag                    true
% 3.90/1.00  --time_out_prep_mult                    0.1
% 3.90/1.00  --splitting_mode                        input
% 3.90/1.00  --splitting_grd                         true
% 3.90/1.00  --splitting_cvd                         false
% 3.90/1.00  --splitting_cvd_svl                     false
% 3.90/1.00  --splitting_nvd                         32
% 3.90/1.00  --sub_typing                            true
% 3.90/1.00  --prep_gs_sim                           true
% 3.90/1.00  --prep_unflatten                        true
% 3.90/1.00  --prep_res_sim                          true
% 3.90/1.00  --prep_upred                            true
% 3.90/1.00  --prep_sem_filter                       exhaustive
% 3.90/1.00  --prep_sem_filter_out                   false
% 3.90/1.00  --pred_elim                             true
% 3.90/1.00  --res_sim_input                         true
% 3.90/1.00  --eq_ax_congr_red                       true
% 3.90/1.00  --pure_diseq_elim                       true
% 3.90/1.00  --brand_transform                       false
% 3.90/1.00  --non_eq_to_eq                          false
% 3.90/1.00  --prep_def_merge                        true
% 3.90/1.00  --prep_def_merge_prop_impl              false
% 3.90/1.00  --prep_def_merge_mbd                    true
% 3.90/1.00  --prep_def_merge_tr_red                 false
% 3.90/1.00  --prep_def_merge_tr_cl                  false
% 3.90/1.00  --smt_preprocessing                     true
% 3.90/1.00  --smt_ac_axioms                         fast
% 3.90/1.00  --preprocessed_out                      false
% 3.90/1.00  --preprocessed_stats                    false
% 3.90/1.00  
% 3.90/1.00  ------ Abstraction refinement Options
% 3.90/1.00  
% 3.90/1.00  --abstr_ref                             []
% 3.90/1.00  --abstr_ref_prep                        false
% 3.90/1.00  --abstr_ref_until_sat                   false
% 3.90/1.00  --abstr_ref_sig_restrict                funpre
% 3.90/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/1.00  --abstr_ref_under                       []
% 3.90/1.00  
% 3.90/1.00  ------ SAT Options
% 3.90/1.00  
% 3.90/1.00  --sat_mode                              false
% 3.90/1.00  --sat_fm_restart_options                ""
% 3.90/1.00  --sat_gr_def                            false
% 3.90/1.00  --sat_epr_types                         true
% 3.90/1.00  --sat_non_cyclic_types                  false
% 3.90/1.00  --sat_finite_models                     false
% 3.90/1.00  --sat_fm_lemmas                         false
% 3.90/1.00  --sat_fm_prep                           false
% 3.90/1.00  --sat_fm_uc_incr                        true
% 3.90/1.00  --sat_out_model                         small
% 3.90/1.00  --sat_out_clauses                       false
% 3.90/1.00  
% 3.90/1.00  ------ QBF Options
% 3.90/1.00  
% 3.90/1.00  --qbf_mode                              false
% 3.90/1.00  --qbf_elim_univ                         false
% 3.90/1.00  --qbf_dom_inst                          none
% 3.90/1.00  --qbf_dom_pre_inst                      false
% 3.90/1.00  --qbf_sk_in                             false
% 3.90/1.00  --qbf_pred_elim                         true
% 3.90/1.00  --qbf_split                             512
% 3.90/1.00  
% 3.90/1.00  ------ BMC1 Options
% 3.90/1.00  
% 3.90/1.00  --bmc1_incremental                      false
% 3.90/1.00  --bmc1_axioms                           reachable_all
% 3.90/1.00  --bmc1_min_bound                        0
% 3.90/1.00  --bmc1_max_bound                        -1
% 3.90/1.00  --bmc1_max_bound_default                -1
% 3.90/1.00  --bmc1_symbol_reachability              true
% 3.90/1.00  --bmc1_property_lemmas                  false
% 3.90/1.00  --bmc1_k_induction                      false
% 3.90/1.00  --bmc1_non_equiv_states                 false
% 3.90/1.00  --bmc1_deadlock                         false
% 3.90/1.00  --bmc1_ucm                              false
% 3.90/1.00  --bmc1_add_unsat_core                   none
% 3.90/1.00  --bmc1_unsat_core_children              false
% 3.90/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/1.00  --bmc1_out_stat                         full
% 3.90/1.00  --bmc1_ground_init                      false
% 3.90/1.00  --bmc1_pre_inst_next_state              false
% 3.90/1.00  --bmc1_pre_inst_state                   false
% 3.90/1.00  --bmc1_pre_inst_reach_state             false
% 3.90/1.00  --bmc1_out_unsat_core                   false
% 3.90/1.00  --bmc1_aig_witness_out                  false
% 3.90/1.00  --bmc1_verbose                          false
% 3.90/1.00  --bmc1_dump_clauses_tptp                false
% 3.90/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.90/1.00  --bmc1_dump_file                        -
% 3.90/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.90/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.90/1.00  --bmc1_ucm_extend_mode                  1
% 3.90/1.00  --bmc1_ucm_init_mode                    2
% 3.90/1.00  --bmc1_ucm_cone_mode                    none
% 3.90/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.90/1.00  --bmc1_ucm_relax_model                  4
% 3.90/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.90/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/1.00  --bmc1_ucm_layered_model                none
% 3.90/1.00  --bmc1_ucm_max_lemma_size               10
% 3.90/1.00  
% 3.90/1.00  ------ AIG Options
% 3.90/1.00  
% 3.90/1.00  --aig_mode                              false
% 3.90/1.00  
% 3.90/1.00  ------ Instantiation Options
% 3.90/1.00  
% 3.90/1.00  --instantiation_flag                    true
% 3.90/1.00  --inst_sos_flag                         false
% 3.90/1.00  --inst_sos_phase                        true
% 3.90/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/1.00  --inst_lit_sel_side                     num_symb
% 3.90/1.00  --inst_solver_per_active                1400
% 3.90/1.00  --inst_solver_calls_frac                1.
% 3.90/1.00  --inst_passive_queue_type               priority_queues
% 3.90/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/1.00  --inst_passive_queues_freq              [25;2]
% 3.90/1.00  --inst_dismatching                      true
% 3.90/1.00  --inst_eager_unprocessed_to_passive     true
% 3.90/1.00  --inst_prop_sim_given                   true
% 3.90/1.00  --inst_prop_sim_new                     false
% 3.90/1.00  --inst_subs_new                         false
% 3.90/1.00  --inst_eq_res_simp                      false
% 3.90/1.00  --inst_subs_given                       false
% 3.90/1.00  --inst_orphan_elimination               true
% 3.90/1.00  --inst_learning_loop_flag               true
% 3.90/1.00  --inst_learning_start                   3000
% 3.90/1.00  --inst_learning_factor                  2
% 3.90/1.00  --inst_start_prop_sim_after_learn       3
% 3.90/1.00  --inst_sel_renew                        solver
% 3.90/1.00  --inst_lit_activity_flag                true
% 3.90/1.00  --inst_restr_to_given                   false
% 3.90/1.00  --inst_activity_threshold               500
% 3.90/1.00  --inst_out_proof                        true
% 3.90/1.00  
% 3.90/1.00  ------ Resolution Options
% 3.90/1.00  
% 3.90/1.00  --resolution_flag                       true
% 3.90/1.00  --res_lit_sel                           adaptive
% 3.90/1.00  --res_lit_sel_side                      none
% 3.90/1.00  --res_ordering                          kbo
% 3.90/1.00  --res_to_prop_solver                    active
% 3.90/1.00  --res_prop_simpl_new                    false
% 3.90/1.00  --res_prop_simpl_given                  true
% 3.90/1.00  --res_passive_queue_type                priority_queues
% 3.90/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/1.00  --res_passive_queues_freq               [15;5]
% 3.90/1.00  --res_forward_subs                      full
% 3.90/1.00  --res_backward_subs                     full
% 3.90/1.00  --res_forward_subs_resolution           true
% 3.90/1.00  --res_backward_subs_resolution          true
% 3.90/1.00  --res_orphan_elimination                true
% 3.90/1.00  --res_time_limit                        2.
% 3.90/1.00  --res_out_proof                         true
% 3.90/1.00  
% 3.90/1.00  ------ Superposition Options
% 3.90/1.00  
% 3.90/1.00  --superposition_flag                    true
% 3.90/1.00  --sup_passive_queue_type                priority_queues
% 3.90/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.90/1.00  --demod_completeness_check              fast
% 3.90/1.00  --demod_use_ground                      true
% 3.90/1.00  --sup_to_prop_solver                    passive
% 3.90/1.00  --sup_prop_simpl_new                    true
% 3.90/1.00  --sup_prop_simpl_given                  true
% 3.90/1.00  --sup_fun_splitting                     false
% 3.90/1.00  --sup_smt_interval                      50000
% 3.90/1.00  
% 3.90/1.00  ------ Superposition Simplification Setup
% 3.90/1.00  
% 3.90/1.00  --sup_indices_passive                   []
% 3.90/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_full_bw                           [BwDemod]
% 3.90/1.00  --sup_immed_triv                        [TrivRules]
% 3.90/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_immed_bw_main                     []
% 3.90/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/1.00  
% 3.90/1.00  ------ Combination Options
% 3.90/1.00  
% 3.90/1.00  --comb_res_mult                         3
% 3.90/1.00  --comb_sup_mult                         2
% 3.90/1.00  --comb_inst_mult                        10
% 3.90/1.00  
% 3.90/1.00  ------ Debug Options
% 3.90/1.00  
% 3.90/1.00  --dbg_backtrace                         false
% 3.90/1.00  --dbg_dump_prop_clauses                 false
% 3.90/1.00  --dbg_dump_prop_clauses_file            -
% 3.90/1.00  --dbg_out_stat                          false
% 3.90/1.00  ------ Parsing...
% 3.90/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/1.00  ------ Proving...
% 3.90/1.00  ------ Problem Properties 
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  clauses                                 16
% 3.90/1.00  conjectures                             2
% 3.90/1.00  EPR                                     1
% 3.90/1.00  Horn                                    14
% 3.90/1.00  unary                                   7
% 3.90/1.00  binary                                  6
% 3.90/1.00  lits                                    28
% 3.90/1.00  lits eq                                 16
% 3.90/1.00  fd_pure                                 0
% 3.90/1.00  fd_pseudo                               0
% 3.90/1.00  fd_cond                                 0
% 3.90/1.00  fd_pseudo_cond                          0
% 3.90/1.00  AC symbols                              0
% 3.90/1.00  
% 3.90/1.00  ------ Schedule dynamic 5 is on 
% 3.90/1.00  
% 3.90/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  ------ 
% 3.90/1.00  Current options:
% 3.90/1.00  ------ 
% 3.90/1.00  
% 3.90/1.00  ------ Input Options
% 3.90/1.00  
% 3.90/1.00  --out_options                           all
% 3.90/1.00  --tptp_safe_out                         true
% 3.90/1.00  --problem_path                          ""
% 3.90/1.00  --include_path                          ""
% 3.90/1.00  --clausifier                            res/vclausify_rel
% 3.90/1.00  --clausifier_options                    --mode clausify
% 3.90/1.00  --stdin                                 false
% 3.90/1.00  --stats_out                             all
% 3.90/1.00  
% 3.90/1.00  ------ General Options
% 3.90/1.00  
% 3.90/1.00  --fof                                   false
% 3.90/1.00  --time_out_real                         305.
% 3.90/1.00  --time_out_virtual                      -1.
% 3.90/1.00  --symbol_type_check                     false
% 3.90/1.00  --clausify_out                          false
% 3.90/1.00  --sig_cnt_out                           false
% 3.90/1.00  --trig_cnt_out                          false
% 3.90/1.00  --trig_cnt_out_tolerance                1.
% 3.90/1.00  --trig_cnt_out_sk_spl                   false
% 3.90/1.00  --abstr_cl_out                          false
% 3.90/1.00  
% 3.90/1.00  ------ Global Options
% 3.90/1.00  
% 3.90/1.00  --schedule                              default
% 3.90/1.00  --add_important_lit                     false
% 3.90/1.00  --prop_solver_per_cl                    1000
% 3.90/1.00  --min_unsat_core                        false
% 3.90/1.00  --soft_assumptions                      false
% 3.90/1.00  --soft_lemma_size                       3
% 3.90/1.00  --prop_impl_unit_size                   0
% 3.90/1.00  --prop_impl_unit                        []
% 3.90/1.00  --share_sel_clauses                     true
% 3.90/1.00  --reset_solvers                         false
% 3.90/1.00  --bc_imp_inh                            [conj_cone]
% 3.90/1.00  --conj_cone_tolerance                   3.
% 3.90/1.00  --extra_neg_conj                        none
% 3.90/1.00  --large_theory_mode                     true
% 3.90/1.00  --prolific_symb_bound                   200
% 3.90/1.00  --lt_threshold                          2000
% 3.90/1.00  --clause_weak_htbl                      true
% 3.90/1.00  --gc_record_bc_elim                     false
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing Options
% 3.90/1.00  
% 3.90/1.00  --preprocessing_flag                    true
% 3.90/1.00  --time_out_prep_mult                    0.1
% 3.90/1.00  --splitting_mode                        input
% 3.90/1.00  --splitting_grd                         true
% 3.90/1.00  --splitting_cvd                         false
% 3.90/1.00  --splitting_cvd_svl                     false
% 3.90/1.00  --splitting_nvd                         32
% 3.90/1.00  --sub_typing                            true
% 3.90/1.00  --prep_gs_sim                           true
% 3.90/1.00  --prep_unflatten                        true
% 3.90/1.00  --prep_res_sim                          true
% 3.90/1.00  --prep_upred                            true
% 3.90/1.00  --prep_sem_filter                       exhaustive
% 3.90/1.00  --prep_sem_filter_out                   false
% 3.90/1.00  --pred_elim                             true
% 3.90/1.00  --res_sim_input                         true
% 3.90/1.00  --eq_ax_congr_red                       true
% 3.90/1.00  --pure_diseq_elim                       true
% 3.90/1.00  --brand_transform                       false
% 3.90/1.00  --non_eq_to_eq                          false
% 3.90/1.00  --prep_def_merge                        true
% 3.90/1.00  --prep_def_merge_prop_impl              false
% 3.90/1.00  --prep_def_merge_mbd                    true
% 3.90/1.00  --prep_def_merge_tr_red                 false
% 3.90/1.00  --prep_def_merge_tr_cl                  false
% 3.90/1.00  --smt_preprocessing                     true
% 3.90/1.00  --smt_ac_axioms                         fast
% 3.90/1.00  --preprocessed_out                      false
% 3.90/1.00  --preprocessed_stats                    false
% 3.90/1.00  
% 3.90/1.00  ------ Abstraction refinement Options
% 3.90/1.00  
% 3.90/1.00  --abstr_ref                             []
% 3.90/1.00  --abstr_ref_prep                        false
% 3.90/1.00  --abstr_ref_until_sat                   false
% 3.90/1.00  --abstr_ref_sig_restrict                funpre
% 3.90/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/1.00  --abstr_ref_under                       []
% 3.90/1.00  
% 3.90/1.00  ------ SAT Options
% 3.90/1.00  
% 3.90/1.00  --sat_mode                              false
% 3.90/1.00  --sat_fm_restart_options                ""
% 3.90/1.00  --sat_gr_def                            false
% 3.90/1.00  --sat_epr_types                         true
% 3.90/1.00  --sat_non_cyclic_types                  false
% 3.90/1.00  --sat_finite_models                     false
% 3.90/1.00  --sat_fm_lemmas                         false
% 3.90/1.00  --sat_fm_prep                           false
% 3.90/1.00  --sat_fm_uc_incr                        true
% 3.90/1.00  --sat_out_model                         small
% 3.90/1.00  --sat_out_clauses                       false
% 3.90/1.00  
% 3.90/1.00  ------ QBF Options
% 3.90/1.00  
% 3.90/1.00  --qbf_mode                              false
% 3.90/1.00  --qbf_elim_univ                         false
% 3.90/1.00  --qbf_dom_inst                          none
% 3.90/1.00  --qbf_dom_pre_inst                      false
% 3.90/1.00  --qbf_sk_in                             false
% 3.90/1.00  --qbf_pred_elim                         true
% 3.90/1.00  --qbf_split                             512
% 3.90/1.00  
% 3.90/1.00  ------ BMC1 Options
% 3.90/1.00  
% 3.90/1.00  --bmc1_incremental                      false
% 3.90/1.00  --bmc1_axioms                           reachable_all
% 3.90/1.00  --bmc1_min_bound                        0
% 3.90/1.00  --bmc1_max_bound                        -1
% 3.90/1.00  --bmc1_max_bound_default                -1
% 3.90/1.00  --bmc1_symbol_reachability              true
% 3.90/1.00  --bmc1_property_lemmas                  false
% 3.90/1.00  --bmc1_k_induction                      false
% 3.90/1.00  --bmc1_non_equiv_states                 false
% 3.90/1.00  --bmc1_deadlock                         false
% 3.90/1.00  --bmc1_ucm                              false
% 3.90/1.00  --bmc1_add_unsat_core                   none
% 3.90/1.00  --bmc1_unsat_core_children              false
% 3.90/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/1.00  --bmc1_out_stat                         full
% 3.90/1.00  --bmc1_ground_init                      false
% 3.90/1.00  --bmc1_pre_inst_next_state              false
% 3.90/1.00  --bmc1_pre_inst_state                   false
% 3.90/1.00  --bmc1_pre_inst_reach_state             false
% 3.90/1.00  --bmc1_out_unsat_core                   false
% 3.90/1.00  --bmc1_aig_witness_out                  false
% 3.90/1.00  --bmc1_verbose                          false
% 3.90/1.00  --bmc1_dump_clauses_tptp                false
% 3.90/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.90/1.00  --bmc1_dump_file                        -
% 3.90/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.90/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.90/1.00  --bmc1_ucm_extend_mode                  1
% 3.90/1.00  --bmc1_ucm_init_mode                    2
% 3.90/1.00  --bmc1_ucm_cone_mode                    none
% 3.90/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.90/1.00  --bmc1_ucm_relax_model                  4
% 3.90/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.90/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/1.00  --bmc1_ucm_layered_model                none
% 3.90/1.00  --bmc1_ucm_max_lemma_size               10
% 3.90/1.00  
% 3.90/1.00  ------ AIG Options
% 3.90/1.00  
% 3.90/1.00  --aig_mode                              false
% 3.90/1.00  
% 3.90/1.00  ------ Instantiation Options
% 3.90/1.00  
% 3.90/1.00  --instantiation_flag                    true
% 3.90/1.00  --inst_sos_flag                         false
% 3.90/1.00  --inst_sos_phase                        true
% 3.90/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/1.00  --inst_lit_sel_side                     none
% 3.90/1.00  --inst_solver_per_active                1400
% 3.90/1.00  --inst_solver_calls_frac                1.
% 3.90/1.00  --inst_passive_queue_type               priority_queues
% 3.90/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/1.00  --inst_passive_queues_freq              [25;2]
% 3.90/1.00  --inst_dismatching                      true
% 3.90/1.00  --inst_eager_unprocessed_to_passive     true
% 3.90/1.00  --inst_prop_sim_given                   true
% 3.90/1.00  --inst_prop_sim_new                     false
% 3.90/1.00  --inst_subs_new                         false
% 3.90/1.00  --inst_eq_res_simp                      false
% 3.90/1.00  --inst_subs_given                       false
% 3.90/1.00  --inst_orphan_elimination               true
% 3.90/1.00  --inst_learning_loop_flag               true
% 3.90/1.00  --inst_learning_start                   3000
% 3.90/1.00  --inst_learning_factor                  2
% 3.90/1.00  --inst_start_prop_sim_after_learn       3
% 3.90/1.00  --inst_sel_renew                        solver
% 3.90/1.00  --inst_lit_activity_flag                true
% 3.90/1.00  --inst_restr_to_given                   false
% 3.90/1.00  --inst_activity_threshold               500
% 3.90/1.00  --inst_out_proof                        true
% 3.90/1.00  
% 3.90/1.00  ------ Resolution Options
% 3.90/1.00  
% 3.90/1.00  --resolution_flag                       false
% 3.90/1.00  --res_lit_sel                           adaptive
% 3.90/1.00  --res_lit_sel_side                      none
% 3.90/1.00  --res_ordering                          kbo
% 3.90/1.00  --res_to_prop_solver                    active
% 3.90/1.00  --res_prop_simpl_new                    false
% 3.90/1.00  --res_prop_simpl_given                  true
% 3.90/1.00  --res_passive_queue_type                priority_queues
% 3.90/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/1.00  --res_passive_queues_freq               [15;5]
% 3.90/1.00  --res_forward_subs                      full
% 3.90/1.00  --res_backward_subs                     full
% 3.90/1.00  --res_forward_subs_resolution           true
% 3.90/1.00  --res_backward_subs_resolution          true
% 3.90/1.00  --res_orphan_elimination                true
% 3.90/1.00  --res_time_limit                        2.
% 3.90/1.00  --res_out_proof                         true
% 3.90/1.00  
% 3.90/1.00  ------ Superposition Options
% 3.90/1.00  
% 3.90/1.00  --superposition_flag                    true
% 3.90/1.00  --sup_passive_queue_type                priority_queues
% 3.90/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.90/1.00  --demod_completeness_check              fast
% 3.90/1.00  --demod_use_ground                      true
% 3.90/1.00  --sup_to_prop_solver                    passive
% 3.90/1.00  --sup_prop_simpl_new                    true
% 3.90/1.00  --sup_prop_simpl_given                  true
% 3.90/1.00  --sup_fun_splitting                     false
% 3.90/1.00  --sup_smt_interval                      50000
% 3.90/1.00  
% 3.90/1.00  ------ Superposition Simplification Setup
% 3.90/1.00  
% 3.90/1.00  --sup_indices_passive                   []
% 3.90/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_full_bw                           [BwDemod]
% 3.90/1.00  --sup_immed_triv                        [TrivRules]
% 3.90/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_immed_bw_main                     []
% 3.90/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/1.00  
% 3.90/1.00  ------ Combination Options
% 3.90/1.00  
% 3.90/1.00  --comb_res_mult                         3
% 3.90/1.00  --comb_sup_mult                         2
% 3.90/1.00  --comb_inst_mult                        10
% 3.90/1.00  
% 3.90/1.00  ------ Debug Options
% 3.90/1.00  
% 3.90/1.00  --dbg_backtrace                         false
% 3.90/1.00  --dbg_dump_prop_clauses                 false
% 3.90/1.00  --dbg_dump_prop_clauses_file            -
% 3.90/1.00  --dbg_out_stat                          false
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  ------ Proving...
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  % SZS status Theorem for theBenchmark.p
% 3.90/1.00  
% 3.90/1.00   Resolution empty clause
% 3.90/1.00  
% 3.90/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/1.00  
% 3.90/1.00  fof(f10,axiom,(
% 3.90/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f21,plain,(
% 3.90/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.90/1.00    inference(nnf_transformation,[],[f10])).
% 3.90/1.00  
% 3.90/1.00  fof(f22,plain,(
% 3.90/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.90/1.00    inference(rectify,[],[f21])).
% 3.90/1.00  
% 3.90/1.00  fof(f23,plain,(
% 3.90/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.90/1.00    introduced(choice_axiom,[])).
% 3.90/1.00  
% 3.90/1.00  fof(f24,plain,(
% 3.90/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.90/1.00  
% 3.90/1.00  fof(f39,plain,(
% 3.90/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.90/1.00    inference(cnf_transformation,[],[f24])).
% 3.90/1.00  
% 3.90/1.00  fof(f59,plain,(
% 3.90/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.90/1.00    inference(equality_resolution,[],[f39])).
% 3.90/1.00  
% 3.90/1.00  fof(f11,axiom,(
% 3.90/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f18,plain,(
% 3.90/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.90/1.00    inference(ennf_transformation,[],[f11])).
% 3.90/1.00  
% 3.90/1.00  fof(f25,plain,(
% 3.90/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.90/1.00    inference(nnf_transformation,[],[f18])).
% 3.90/1.00  
% 3.90/1.00  fof(f43,plain,(
% 3.90/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f25])).
% 3.90/1.00  
% 3.90/1.00  fof(f15,conjecture,(
% 3.90/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f16,negated_conjecture,(
% 3.90/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.90/1.00    inference(negated_conjecture,[],[f15])).
% 3.90/1.00  
% 3.90/1.00  fof(f20,plain,(
% 3.90/1.00    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.90/1.00    inference(ennf_transformation,[],[f16])).
% 3.90/1.00  
% 3.90/1.00  fof(f26,plain,(
% 3.90/1.00    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.90/1.00    inference(nnf_transformation,[],[f20])).
% 3.90/1.00  
% 3.90/1.00  fof(f27,plain,(
% 3.90/1.00    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.90/1.00    inference(flattening,[],[f26])).
% 3.90/1.00  
% 3.90/1.00  fof(f28,plain,(
% 3.90/1.00    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.90/1.00    introduced(choice_axiom,[])).
% 3.90/1.00  
% 3.90/1.00  fof(f29,plain,(
% 3.90/1.00    (k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f28])).
% 3.90/1.00  
% 3.90/1.00  fof(f50,plain,(
% 3.90/1.00    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.90/1.00    inference(cnf_transformation,[],[f29])).
% 3.90/1.00  
% 3.90/1.00  fof(f14,axiom,(
% 3.90/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f49,plain,(
% 3.90/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.90/1.00    inference(cnf_transformation,[],[f14])).
% 3.90/1.00  
% 3.90/1.00  fof(f4,axiom,(
% 3.90/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f17,plain,(
% 3.90/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.90/1.00    inference(ennf_transformation,[],[f4])).
% 3.90/1.00  
% 3.90/1.00  fof(f33,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f17])).
% 3.90/1.00  
% 3.90/1.00  fof(f2,axiom,(
% 3.90/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f31,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f2])).
% 3.90/1.00  
% 3.90/1.00  fof(f5,axiom,(
% 3.90/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f34,plain,(
% 3.90/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f5])).
% 3.90/1.00  
% 3.90/1.00  fof(f7,axiom,(
% 3.90/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f36,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.90/1.00    inference(cnf_transformation,[],[f7])).
% 3.90/1.00  
% 3.90/1.00  fof(f3,axiom,(
% 3.90/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f32,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.90/1.00    inference(cnf_transformation,[],[f3])).
% 3.90/1.00  
% 3.90/1.00  fof(f54,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.90/1.00    inference(definition_unfolding,[],[f36,f32,f32])).
% 3.90/1.00  
% 3.90/1.00  fof(f8,axiom,(
% 3.90/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f37,plain,(
% 3.90/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.90/1.00    inference(cnf_transformation,[],[f8])).
% 3.90/1.00  
% 3.90/1.00  fof(f13,axiom,(
% 3.90/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f19,plain,(
% 3.90/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.90/1.00    inference(ennf_transformation,[],[f13])).
% 3.90/1.00  
% 3.90/1.00  fof(f48,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/1.00    inference(cnf_transformation,[],[f19])).
% 3.90/1.00  
% 3.90/1.00  fof(f57,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.90/1.00    inference(definition_unfolding,[],[f48,f32])).
% 3.90/1.00  
% 3.90/1.00  fof(f6,axiom,(
% 3.90/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f35,plain,(
% 3.90/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f6])).
% 3.90/1.00  
% 3.90/1.00  fof(f56,plain,(
% 3.90/1.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.90/1.00    inference(definition_unfolding,[],[f35,f32])).
% 3.90/1.00  
% 3.90/1.00  fof(f44,plain,(
% 3.90/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f25])).
% 3.90/1.00  
% 3.90/1.00  fof(f40,plain,(
% 3.90/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.90/1.00    inference(cnf_transformation,[],[f24])).
% 3.90/1.00  
% 3.90/1.00  fof(f58,plain,(
% 3.90/1.00    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.90/1.00    inference(equality_resolution,[],[f40])).
% 3.90/1.00  
% 3.90/1.00  fof(f1,axiom,(
% 3.90/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f30,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.90/1.00    inference(cnf_transformation,[],[f1])).
% 3.90/1.00  
% 3.90/1.00  fof(f9,axiom,(
% 3.90/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f38,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.90/1.00    inference(cnf_transformation,[],[f9])).
% 3.90/1.00  
% 3.90/1.00  fof(f53,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.90/1.00    inference(definition_unfolding,[],[f38,f32])).
% 3.90/1.00  
% 3.90/1.00  fof(f55,plain,(
% 3.90/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.90/1.00    inference(definition_unfolding,[],[f30,f53,f53])).
% 3.90/1.00  
% 3.90/1.00  fof(f51,plain,(
% 3.90/1.00    k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 3.90/1.00    inference(cnf_transformation,[],[f29])).
% 3.90/1.00  
% 3.90/1.00  fof(f12,axiom,(
% 3.90/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/1.00  
% 3.90/1.00  fof(f47,plain,(
% 3.90/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.90/1.00    inference(cnf_transformation,[],[f12])).
% 3.90/1.00  
% 3.90/1.00  fof(f52,plain,(
% 3.90/1.00    k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 3.90/1.00    inference(cnf_transformation,[],[f29])).
% 3.90/1.00  
% 3.90/1.00  cnf(c_10,plain,
% 3.90/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_675,plain,
% 3.90/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.90/1.00      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_676,plain,
% 3.90/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.90/1.00      inference(renaming,[status(thm)],[c_675]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_14,plain,
% 3.90/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_20,negated_conjecture,
% 3.90/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.90/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_265,plain,
% 3.90/1.00      ( r2_hidden(X0,X1)
% 3.90/1.00      | v1_xboole_0(X1)
% 3.90/1.00      | k1_zfmisc_1(sK1) != X1
% 3.90/1.00      | sK2 != X0 ),
% 3.90/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_266,plain,
% 3.90/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.90/1.00      inference(unflattening,[status(thm)],[c_265]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_17,plain,
% 3.90/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.90/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_272,plain,
% 3.90/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 3.90/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_266,c_17]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_797,plain,
% 3.90/1.00      ( r1_tarski(X0,X1) | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1) | sK2 != X0 ),
% 3.90/1.00      inference(resolution_lifted,[status(thm)],[c_676,c_272]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_798,plain,
% 3.90/1.00      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.90/1.00      inference(unflattening,[status(thm)],[c_797]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1198,plain,
% 3.90/1.00      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) | r1_tarski(sK2,X0) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1367,plain,
% 3.90/1.00      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.90/1.00      inference(equality_resolution,[status(thm)],[c_1198]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3,plain,
% 3.90/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.90/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1207,plain,
% 3.90/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2535,plain,
% 3.90/1.00      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1367,c_1207]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2,plain,
% 3.90/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.90/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4,plain,
% 3.90/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.90/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1206,plain,
% 3.90/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2530,plain,
% 3.90/1.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1206,c_1207]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_0,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1436,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3241,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1436,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3764,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_3241]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7894,plain,
% 3.90/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2530,c_3764]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7900,plain,
% 3.90/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2530,c_2]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7923,plain,
% 3.90/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7894,c_2530,c_7900]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.90/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7925,plain,
% 3.90/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7923,c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_16,plain,
% 3.90/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.90/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_278,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.90/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.90/1.00      | sK2 != X1 ),
% 3.90/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_279,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
% 3.90/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.90/1.00      inference(unflattening,[status(thm)],[c_278]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1294,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(equality_resolution,[status(thm)],[c_279]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5,plain,
% 3.90/1.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.90/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1205,plain,
% 3.90/1.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1853,plain,
% 3.90/1.00      ( r1_tarski(k3_subset_1(sK1,sK2),sK1) = iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1294,c_1205]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2537,plain,
% 3.90/1.00      ( k3_xboole_0(k3_subset_1(sK1,sK2),sK1) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1853,c_1207]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2846,plain,
% 3.90/1.00      ( k3_xboole_0(sK1,k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2537,c_2]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3767,plain,
% 3.90/1.00      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k3_subset_1(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2846,c_3241]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1435,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2))) = k3_xboole_0(sK1,sK2) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1294,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3113,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_subset_1(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_2846,c_1435]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3791,plain,
% 3.90/1.00      ( k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
% 3.90/1.00      inference(light_normalisation,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_3767,c_2537,c_2846,c_3113]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5757,plain,
% 3.90/1.00      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_3791,c_3241]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5759,plain,
% 3.90/1.00      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_5757,c_1294]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6307,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_5759,c_3764]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6318,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_6307,c_5759]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8983,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_6318]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9011,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_8983,c_1294]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9401,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_7925,c_9011]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9580,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_9401]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9652,plain,
% 3.90/1.00      ( k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_9580,c_1294]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_13,plain,
% 3.90/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_245,plain,
% 3.90/1.00      ( ~ r2_hidden(X0,X1)
% 3.90/1.00      | v1_xboole_0(X1)
% 3.90/1.00      | X2 != X0
% 3.90/1.00      | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = k3_subset_1(X3,X2)
% 3.90/1.00      | k1_zfmisc_1(X3) != X1 ),
% 3.90/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_246,plain,
% 3.90/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.90/1.00      | v1_xboole_0(k1_zfmisc_1(X1))
% 3.90/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.90/1.00      inference(unflattening,[status(thm)],[c_245]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_256,plain,
% 3.90/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.90/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.90/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_246,c_17]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9,plain,
% 3.90/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.90/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_677,plain,
% 3.90/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.90/1.00      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_678,plain,
% 3.90/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.90/1.00      inference(renaming,[status(thm)],[c_677]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_712,plain,
% 3.90/1.00      ( ~ r1_tarski(X0,X1)
% 3.90/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.90/1.00      inference(bin_hyper_res,[status(thm)],[c_256,c_678]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1202,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.90/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2248,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1205,c_1202]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2280,plain,
% 3.90/1.00      ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_2248,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9783,plain,
% 3.90/1.00      ( k3_subset_1(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_9652,c_2280]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9838,plain,
% 3.90/1.00      ( k3_subset_1(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_9783,c_9652]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2434,plain,
% 3.90/1.00      ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,X1) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_2280]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7897,plain,
% 3.90/1.00      ( k3_subset_1(X0,k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2530,c_2434]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7917,plain,
% 3.90/1.00      ( k3_subset_1(X0,k5_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7897,c_7900]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7919,plain,
% 3.90/1.00      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7917,c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.90/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3242,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1436,c_1]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7892,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)),k3_xboole_0(X0,k1_xboole_0)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2530,c_3242]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7927,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7892,c_2530,c_7900]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7929,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7927,c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9475,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7929,c_7925]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9840,plain,
% 3.90/1.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) = k1_xboole_0 ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_9838,c_7919,c_9475]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9049,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_9011,c_3764]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9059,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_9049,c_9011]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12675,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_9059,c_7925]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12681,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_12675]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12709,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_12681,c_1294]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1489,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1435,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1565,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2)))) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1489,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1716,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1565,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2010,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2))))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1716,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2121,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2)))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2010,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2209,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK1,sK2)))))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2121,c_0]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4136,plain,
% 3.90/1.00      ( k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,sK2) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_2209,c_2846,c_3113]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4149,plain,
% 3.90/1.00      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_4136,c_3241]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4151,plain,
% 3.90/1.00      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_4149,c_1294]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4505,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_4151,c_3764]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4516,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_4505,c_4151]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_4899,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_4516]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7107,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_4899,c_3791]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7109,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_7107]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7133,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7109,c_1294,c_3791]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1852,plain,
% 3.90/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_0,c_1205]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1969,plain,
% 3.90/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_1852]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7200,plain,
% 3.90/1.00      ( r1_tarski(k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,sK2),sK1)),k3_subset_1(sK1,sK2))) = iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_7133,c_1969]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8678,plain,
% 3.90/1.00      ( r1_tarski(k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_subset_1(sK1,sK2))) = iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_7200]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8687,plain,
% 3.90/1.00      ( r1_tarski(k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = iProver_top ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_8678,c_1294,c_3791]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_8776,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) = k3_subset_1(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_8687,c_1202]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_11854,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k1_xboole_0 ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_8776,c_7919,c_7925]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_12710,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k1_xboole_0 ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_12709,c_7925,c_11854]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_13585,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k1_xboole_0)) = k1_xboole_0 ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_9840,c_12710]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_13629,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)) = k1_xboole_0 ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_13585,c_6,c_7925]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6305,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_5759,c_3242]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6321,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_6305,c_5759]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6308,plain,
% 3.90/1.00      ( k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_5759,c_2434]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6850,plain,
% 3.90/1.00      ( k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_6308]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_19,negated_conjecture,
% 3.90/1.00      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) = sK2 ),
% 3.90/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1203,plain,
% 3.90/1.00      ( k2_subset_1(sK1) = sK2
% 3.90/1.00      | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_15,plain,
% 3.90/1.00      ( k2_subset_1(X0) = X0 ),
% 3.90/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1222,plain,
% 3.90/1.00      ( sK2 = sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_1203,c_15]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2532,plain,
% 3.90/1.00      ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2)
% 3.90/1.00      | sK2 = sK1 ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1222,c_1207]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2577,plain,
% 3.90/1.00      ( k3_subset_1(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k3_xboole_0(k3_subset_1(sK1,sK2),sK2)
% 3.90/1.00      | sK2 = sK1 ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2532,c_2280]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_18,negated_conjecture,
% 3.90/1.00      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) != sK2 ),
% 3.90/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1204,plain,
% 3.90/1.00      ( k2_subset_1(sK1) != sK2
% 3.90/1.00      | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 3.90/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1233,plain,
% 3.90/1.00      ( sK2 != sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_1204,c_15]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1270,plain,
% 3.90/1.00      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) | sK2 != sK1 ),
% 3.90/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1233]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_929,plain,( X0 = X0 ),theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1287,plain,
% 3.90/1.00      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_929]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1289,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2)
% 3.90/1.00      | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_279]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1454,plain,
% 3.90/1.00      ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_929]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_930,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1457,plain,
% 3.90/1.00      ( X0 != X1 | k3_subset_1(sK1,sK2) != X1 | k3_subset_1(sK1,sK2) = X0 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_930]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1588,plain,
% 3.90/1.00      ( X0 != k3_subset_1(sK1,sK2)
% 3.90/1.00      | k3_subset_1(sK1,sK2) = X0
% 3.90/1.00      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1457]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1655,plain,
% 3.90/1.00      ( k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
% 3.90/1.00      | k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
% 3.90/1.00      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1588]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_933,plain,
% 3.90/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.90/1.00      theory(equality) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1345,plain,
% 3.90/1.00      ( r1_tarski(X0,X1)
% 3.90/1.00      | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)
% 3.90/1.00      | X1 != X2
% 3.90/1.00      | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_933]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1446,plain,
% 3.90/1.00      ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 3.90/1.00      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)
% 3.90/1.00      | k3_subset_1(sK1,sK2) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 3.90/1.00      | sK2 != X0 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1345]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2092,plain,
% 3.90/1.00      ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 3.90/1.00      | ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
% 3.90/1.00      | k3_subset_1(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
% 3.90/1.00      | sK2 != sK1 ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_1446]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3521,plain,
% 3.90/1.00      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) ),
% 3.90/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3938,plain,
% 3.90/1.00      ( k3_subset_1(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k3_xboole_0(k3_subset_1(sK1,sK2),sK2) ),
% 3.90/1.00      inference(global_propositional_subsumption,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_2577,c_1270,c_1287,c_1289,c_1454,c_1655,c_2092,c_3521]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6854,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1) = k3_xboole_0(k3_subset_1(sK1,sK2),sK2) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_6850,c_1294,c_3938]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6896,plain,
% 3.90/1.00      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(k3_subset_1(sK1,sK2),sK2) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_6854,c_2]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6906,plain,
% 3.90/1.00      ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_6896,c_5759]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6908,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_6906,c_6854]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2426,plain,
% 3.90/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_subset_1(X0,k3_xboole_0(X0,X1)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_0,c_2280]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_3279,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1)))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2426,c_1]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5076,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_3242]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6215,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_3279,c_5076]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6236,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_6215]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7080,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_5759,c_6236]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7086,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7080,c_5759]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_6881,plain,
% 3.90/1.00      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK1)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_6854,c_2426]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_10385,plain,
% 3.90/1.00      ( k3_subset_1(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)) = k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(light_normalisation,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_6881,c_6906,c_6908,c_9401]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_11047,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7086,c_6908,c_10385]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_11049,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_11047]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_11053,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_11049,c_1294]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1478,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9781,plain,
% 3.90/1.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_9652,c_1478]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9915,plain,
% 3.90/1.00      ( k3_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2))) = k1_xboole_0 ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_9783,c_7919,c_9475]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9949,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k1_xboole_0)) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_9781,c_9915]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9951,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_9949,c_6,c_9475]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_11054,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_11053,c_9475,c_9951]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_11858,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_subset_1(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_6321,c_6908,c_11054]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_13937,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))))) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_13629,c_11858]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2247,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1206,c_1202]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5871,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2247,c_1]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7855,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_2530,c_5871]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_5859,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = k3_subset_1(X0,k1_xboole_0) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_2,c_2247]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7856,plain,
% 3.90/1.00      ( k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_2530,c_5859]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7858,plain,
% 3.90/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7856,c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7860,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7855,c_7858]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7862,plain,
% 3.90/1.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_7860,c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_13948,plain,
% 3.90/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_13937,c_7862]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_13949,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_13948,c_6,c_2530]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_14497,plain,
% 3.90/1.00      ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_2535,c_13949]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7423,plain,
% 3.90/1.00      ( k3_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k3_subset_1(sK1,sK2),sK2))) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_subset_1(sK1,sK2))) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_6906,c_3764]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7428,plain,
% 3.90/1.00      ( k3_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_6906,c_2]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7431,plain,
% 3.90/1.00      ( k3_xboole_0(sK2,k5_xboole_0(sK2,k3_subset_1(sK1,sK2))) = k5_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_7423,c_6906,c_7428]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_16014,plain,
% 3.90/1.00      ( k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_14497,c_7431]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_2255,plain,
% 3.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_subset_1(X0,k3_xboole_0(X1,X0)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1969,c_1202]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9440,plain,
% 3.90/1.00      ( k3_subset_1(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_7925,c_2255]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9460,plain,
% 3.90/1.00      ( k3_subset_1(X0,X0) = k5_xboole_0(X0,X0) ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_9440,c_7925]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_9462,plain,
% 3.90/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_9460,c_7919]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_1477,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_1294,c_1]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_14500,plain,
% 3.90/1.00      ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_2535,c_1477]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_14507,plain,
% 3.90/1.00      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_14497,c_14500]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_15089,plain,
% 3.90/1.00      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_9462,c_14507]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_15092,plain,
% 3.90/1.00      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_15089,c_6]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_16071,plain,
% 3.90/1.00      ( sK2 = sK1 ),
% 3.90/1.00      inference(light_normalisation,[status(thm)],[c_16014,c_2535,c_15092]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_7413,plain,
% 3.90/1.00      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 3.90/1.00      inference(superposition,[status(thm)],[c_6906,c_1969]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_16018,plain,
% 3.90/1.00      ( r1_tarski(k5_xboole_0(sK1,sK2),sK2) = iProver_top ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_14497,c_7413]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_16029,plain,
% 3.90/1.00      ( sK2 != sK1 | r1_tarski(k5_xboole_0(sK1,sK2),sK2) != iProver_top ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_14497,c_1233]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_16060,plain,
% 3.90/1.00      ( sK2 != sK1 ),
% 3.90/1.00      inference(backward_subsumption_resolution,
% 3.90/1.00                [status(thm)],
% 3.90/1.00                [c_16018,c_16029]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_16074,plain,
% 3.90/1.00      ( sK1 != sK1 ),
% 3.90/1.00      inference(demodulation,[status(thm)],[c_16071,c_16060]) ).
% 3.90/1.00  
% 3.90/1.00  cnf(c_16092,plain,
% 3.90/1.00      ( $false ),
% 3.90/1.00      inference(equality_resolution_simp,[status(thm)],[c_16074]) ).
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/1.00  
% 3.90/1.00  ------                               Statistics
% 3.90/1.00  
% 3.90/1.00  ------ General
% 3.90/1.00  
% 3.90/1.00  abstr_ref_over_cycles:                  0
% 3.90/1.00  abstr_ref_under_cycles:                 0
% 3.90/1.00  gc_basic_clause_elim:                   0
% 3.90/1.00  forced_gc_time:                         0
% 3.90/1.00  parsing_time:                           0.009
% 3.90/1.00  unif_index_cands_time:                  0.
% 3.90/1.00  unif_index_add_time:                    0.
% 3.90/1.00  orderings_time:                         0.
% 3.90/1.00  out_proof_time:                         0.014
% 3.90/1.00  total_time:                             0.484
% 3.90/1.00  num_of_symbols:                         44
% 3.90/1.00  num_of_terms:                           14617
% 3.90/1.00  
% 3.90/1.00  ------ Preprocessing
% 3.90/1.00  
% 3.90/1.00  num_of_splits:                          0
% 3.90/1.00  num_of_split_atoms:                     0
% 3.90/1.00  num_of_reused_defs:                     0
% 3.90/1.00  num_eq_ax_congr_red:                    14
% 3.90/1.00  num_of_sem_filtered_clauses:            1
% 3.90/1.00  num_of_subtypes:                        0
% 3.90/1.00  monotx_restored_types:                  0
% 3.90/1.00  sat_num_of_epr_types:                   0
% 3.90/1.00  sat_num_of_non_cyclic_types:            0
% 3.90/1.00  sat_guarded_non_collapsed_types:        0
% 3.90/1.00  num_pure_diseq_elim:                    0
% 3.90/1.00  simp_replaced_by:                       0
% 3.90/1.00  res_preprocessed:                       105
% 3.90/1.00  prep_upred:                             0
% 3.90/1.00  prep_unflattend:                        50
% 3.90/1.00  smt_new_axioms:                         0
% 3.90/1.00  pred_elim_cands:                        1
% 3.90/1.00  pred_elim:                              3
% 3.90/1.00  pred_elim_cl:                           5
% 3.90/1.00  pred_elim_cycles:                       7
% 3.90/1.00  merged_defs:                            14
% 3.90/1.00  merged_defs_ncl:                        0
% 3.90/1.00  bin_hyper_res:                          15
% 3.90/1.00  prep_cycles:                            5
% 3.90/1.00  pred_elim_time:                         0.01
% 3.90/1.00  splitting_time:                         0.
% 3.90/1.00  sem_filter_time:                        0.
% 3.90/1.00  monotx_time:                            0.001
% 3.90/1.00  subtype_inf_time:                       0.
% 3.90/1.00  
% 3.90/1.00  ------ Problem properties
% 3.90/1.00  
% 3.90/1.00  clauses:                                16
% 3.90/1.00  conjectures:                            2
% 3.90/1.00  epr:                                    1
% 3.90/1.00  horn:                                   14
% 3.90/1.00  ground:                                 2
% 3.90/1.00  unary:                                  7
% 3.90/1.00  binary:                                 6
% 3.90/1.00  lits:                                   28
% 3.90/1.00  lits_eq:                                16
% 3.90/1.00  fd_pure:                                0
% 3.90/1.00  fd_pseudo:                              0
% 3.90/1.00  fd_cond:                                0
% 3.90/1.00  fd_pseudo_cond:                         0
% 3.90/1.00  ac_symbols:                             0
% 3.90/1.00  
% 3.90/1.00  ------ Propositional Solver
% 3.90/1.00  
% 3.90/1.00  prop_solver_calls:                      37
% 3.90/1.00  prop_fast_solver_calls:                 846
% 3.90/1.00  smt_solver_calls:                       0
% 3.90/1.00  smt_fast_solver_calls:                  0
% 3.90/1.00  prop_num_of_clauses:                    5104
% 3.90/1.00  prop_preprocess_simplified:             10925
% 3.90/1.00  prop_fo_subsumed:                       14
% 3.90/1.00  prop_solver_time:                       0.
% 3.90/1.00  smt_solver_time:                        0.
% 3.90/1.00  smt_fast_solver_time:                   0.
% 3.90/1.00  prop_fast_solver_time:                  0.
% 3.90/1.00  prop_unsat_core_time:                   0.
% 3.90/1.00  
% 3.90/1.00  ------ QBF
% 3.90/1.00  
% 3.90/1.00  qbf_q_res:                              0
% 3.90/1.00  qbf_num_tautologies:                    0
% 3.90/1.00  qbf_prep_cycles:                        0
% 3.90/1.00  
% 3.90/1.00  ------ BMC1
% 3.90/1.00  
% 3.90/1.00  bmc1_current_bound:                     -1
% 3.90/1.00  bmc1_last_solved_bound:                 -1
% 3.90/1.00  bmc1_unsat_core_size:                   -1
% 3.90/1.00  bmc1_unsat_core_parents_size:           -1
% 3.90/1.00  bmc1_merge_next_fun:                    0
% 3.90/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.90/1.00  
% 3.90/1.00  ------ Instantiation
% 3.90/1.00  
% 3.90/1.00  inst_num_of_clauses:                    2354
% 3.90/1.00  inst_num_in_passive:                    905
% 3.90/1.00  inst_num_in_active:                     929
% 3.90/1.00  inst_num_in_unprocessed:                525
% 3.90/1.00  inst_num_of_loops:                      1050
% 3.90/1.00  inst_num_of_learning_restarts:          0
% 3.90/1.00  inst_num_moves_active_passive:          112
% 3.90/1.00  inst_lit_activity:                      0
% 3.90/1.00  inst_lit_activity_moves:                0
% 3.90/1.00  inst_num_tautologies:                   0
% 3.90/1.00  inst_num_prop_implied:                  0
% 3.90/1.00  inst_num_existing_simplified:           0
% 3.90/1.00  inst_num_eq_res_simplified:             0
% 3.90/1.00  inst_num_child_elim:                    0
% 3.90/1.00  inst_num_of_dismatching_blockings:      570
% 3.90/1.00  inst_num_of_non_proper_insts:           2259
% 3.90/1.00  inst_num_of_duplicates:                 0
% 3.90/1.00  inst_inst_num_from_inst_to_res:         0
% 3.90/1.00  inst_dismatching_checking_time:         0.
% 3.90/1.00  
% 3.90/1.00  ------ Resolution
% 3.90/1.00  
% 3.90/1.00  res_num_of_clauses:                     0
% 3.90/1.00  res_num_in_passive:                     0
% 3.90/1.00  res_num_in_active:                      0
% 3.90/1.00  res_num_of_loops:                       110
% 3.90/1.00  res_forward_subset_subsumed:            458
% 3.90/1.00  res_backward_subset_subsumed:           26
% 3.90/1.00  res_forward_subsumed:                   2
% 3.90/1.00  res_backward_subsumed:                  0
% 3.90/1.00  res_forward_subsumption_resolution:     2
% 3.90/1.00  res_backward_subsumption_resolution:    0
% 3.90/1.00  res_clause_to_clause_subsumption:       2842
% 3.90/1.00  res_orphan_elimination:                 0
% 3.90/1.00  res_tautology_del:                      314
% 3.90/1.00  res_num_eq_res_simplified:              0
% 3.90/1.00  res_num_sel_changes:                    0
% 3.90/1.00  res_moves_from_active_to_pass:          0
% 3.90/1.00  
% 3.90/1.00  ------ Superposition
% 3.90/1.00  
% 3.90/1.00  sup_time_total:                         0.
% 3.90/1.00  sup_time_generating:                    0.
% 3.90/1.00  sup_time_sim_full:                      0.
% 3.90/1.00  sup_time_sim_immed:                     0.
% 3.90/1.00  
% 3.90/1.00  sup_num_of_clauses:                     522
% 3.90/1.00  sup_num_in_active:                      61
% 3.90/1.00  sup_num_in_passive:                     461
% 3.90/1.00  sup_num_of_loops:                       209
% 3.90/1.00  sup_fw_superposition:                   953
% 3.90/1.00  sup_bw_superposition:                   1361
% 3.90/1.00  sup_immediate_simplified:               981
% 3.90/1.00  sup_given_eliminated:                   9
% 3.90/1.00  comparisons_done:                       0
% 3.90/1.00  comparisons_avoided:                    17
% 3.90/1.00  
% 3.90/1.00  ------ Simplifications
% 3.90/1.00  
% 3.90/1.00  
% 3.90/1.00  sim_fw_subset_subsumed:                 1
% 3.90/1.00  sim_bw_subset_subsumed:                 8
% 3.90/1.00  sim_fw_subsumed:                        69
% 3.90/1.00  sim_bw_subsumed:                        9
% 3.90/1.00  sim_fw_subsumption_res:                 0
% 3.90/1.00  sim_bw_subsumption_res:                 1
% 3.90/1.00  sim_tautology_del:                      2
% 3.90/1.00  sim_eq_tautology_del:                   260
% 3.90/1.00  sim_eq_res_simp:                        0
% 3.90/1.00  sim_fw_demodulated:                     277
% 3.90/1.00  sim_bw_demodulated:                     260
% 3.90/1.00  sim_light_normalised:                   863
% 3.90/1.00  sim_joinable_taut:                      0
% 3.90/1.00  sim_joinable_simp:                      0
% 3.90/1.00  sim_ac_normalised:                      0
% 3.90/1.00  sim_smt_subsumption:                    0
% 3.90/1.00  
%------------------------------------------------------------------------------
