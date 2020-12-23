%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:13 EST 2020

% Result     : Theorem 11.98s
% Output     : CNFRefutation 11.98s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 272 expanded)
%              Number of clauses        :   57 ( 112 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  229 ( 586 expanded)
%              Number of equality atoms :  110 ( 258 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f41])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f69,f47])).

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

fof(f40,plain,(
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

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f23,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f72,f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1151,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_32253,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1147,c_1151])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1152,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2747,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1152])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_30,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3046,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2747,c_30])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1156,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7876,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3046,c_1156])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1160,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8328,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_7876,c_1160])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8333,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_8328,c_0])).

cnf(c_32254,plain,
    ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_32253,c_8333])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1150,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_33587,plain,
    ( m1_subset_1(k5_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32254,c_1150])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_34078,plain,
    ( m1_subset_1(k5_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33587,c_24])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_757,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X0,X2) ),
    inference(theory_normalisation,[status(thm)],[c_21,c_6,c_1])).

cnf(c_1148,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_1449,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(sK2,X0))) = k4_subset_1(sK1,sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1148])).

cnf(c_34089,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_34078,c_1449])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_249,plain,
    ( k5_xboole_0(X0,X1) != X2
    | k3_xboole_0(X0,X1) != X3
    | k3_xboole_0(X3,X2) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_250,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_1921,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_250])).

cnf(c_8331,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8328,c_1921])).

cnf(c_34090,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0)) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_34089,c_8331])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1399,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1456,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_1460,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1456,c_1399])).

cnf(c_1176,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_1597,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_1176])).

cnf(c_1612,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1597,c_5])).

cnf(c_1780,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_1460,c_1612])).

cnf(c_1177,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_2866,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1780,c_1177])).

cnf(c_34091,plain,
    ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_34090,c_1399,c_2866])).

cnf(c_22,negated_conjecture,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_17,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1161,plain,
    ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_22,c_17])).

cnf(c_33497,plain,
    ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_32254,c_1161])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34091,c_33497])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.98/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.98/2.00  
% 11.98/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.98/2.00  
% 11.98/2.00  ------  iProver source info
% 11.98/2.00  
% 11.98/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.98/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.98/2.00  git: non_committed_changes: false
% 11.98/2.00  git: last_make_outside_of_git: false
% 11.98/2.00  
% 11.98/2.00  ------ 
% 11.98/2.00  
% 11.98/2.00  ------ Input Options
% 11.98/2.00  
% 11.98/2.00  --out_options                           all
% 11.98/2.00  --tptp_safe_out                         true
% 11.98/2.00  --problem_path                          ""
% 11.98/2.00  --include_path                          ""
% 11.98/2.00  --clausifier                            res/vclausify_rel
% 11.98/2.00  --clausifier_options                    ""
% 11.98/2.00  --stdin                                 false
% 11.98/2.00  --stats_out                             all
% 11.98/2.00  
% 11.98/2.00  ------ General Options
% 11.98/2.00  
% 11.98/2.00  --fof                                   false
% 11.98/2.00  --time_out_real                         305.
% 11.98/2.00  --time_out_virtual                      -1.
% 11.98/2.00  --symbol_type_check                     false
% 11.98/2.00  --clausify_out                          false
% 11.98/2.00  --sig_cnt_out                           false
% 11.98/2.00  --trig_cnt_out                          false
% 11.98/2.00  --trig_cnt_out_tolerance                1.
% 11.98/2.00  --trig_cnt_out_sk_spl                   false
% 11.98/2.00  --abstr_cl_out                          false
% 11.98/2.00  
% 11.98/2.00  ------ Global Options
% 11.98/2.00  
% 11.98/2.00  --schedule                              default
% 11.98/2.00  --add_important_lit                     false
% 11.98/2.00  --prop_solver_per_cl                    1000
% 11.98/2.00  --min_unsat_core                        false
% 11.98/2.00  --soft_assumptions                      false
% 11.98/2.00  --soft_lemma_size                       3
% 11.98/2.00  --prop_impl_unit_size                   0
% 11.98/2.00  --prop_impl_unit                        []
% 11.98/2.00  --share_sel_clauses                     true
% 11.98/2.00  --reset_solvers                         false
% 11.98/2.00  --bc_imp_inh                            [conj_cone]
% 11.98/2.00  --conj_cone_tolerance                   3.
% 11.98/2.00  --extra_neg_conj                        none
% 11.98/2.00  --large_theory_mode                     true
% 11.98/2.00  --prolific_symb_bound                   200
% 11.98/2.00  --lt_threshold                          2000
% 11.98/2.00  --clause_weak_htbl                      true
% 11.98/2.00  --gc_record_bc_elim                     false
% 11.98/2.00  
% 11.98/2.00  ------ Preprocessing Options
% 11.98/2.00  
% 11.98/2.00  --preprocessing_flag                    true
% 11.98/2.00  --time_out_prep_mult                    0.1
% 11.98/2.00  --splitting_mode                        input
% 11.98/2.00  --splitting_grd                         true
% 11.98/2.00  --splitting_cvd                         false
% 11.98/2.00  --splitting_cvd_svl                     false
% 11.98/2.00  --splitting_nvd                         32
% 11.98/2.00  --sub_typing                            true
% 11.98/2.00  --prep_gs_sim                           true
% 11.98/2.00  --prep_unflatten                        true
% 11.98/2.00  --prep_res_sim                          true
% 11.98/2.00  --prep_upred                            true
% 11.98/2.00  --prep_sem_filter                       exhaustive
% 11.98/2.00  --prep_sem_filter_out                   false
% 11.98/2.00  --pred_elim                             true
% 11.98/2.00  --res_sim_input                         true
% 11.98/2.00  --eq_ax_congr_red                       true
% 11.98/2.00  --pure_diseq_elim                       true
% 11.98/2.00  --brand_transform                       false
% 11.98/2.00  --non_eq_to_eq                          false
% 11.98/2.00  --prep_def_merge                        true
% 11.98/2.00  --prep_def_merge_prop_impl              false
% 11.98/2.00  --prep_def_merge_mbd                    true
% 11.98/2.00  --prep_def_merge_tr_red                 false
% 11.98/2.00  --prep_def_merge_tr_cl                  false
% 11.98/2.00  --smt_preprocessing                     true
% 11.98/2.00  --smt_ac_axioms                         fast
% 11.98/2.00  --preprocessed_out                      false
% 11.98/2.00  --preprocessed_stats                    false
% 11.98/2.00  
% 11.98/2.00  ------ Abstraction refinement Options
% 11.98/2.00  
% 11.98/2.00  --abstr_ref                             []
% 11.98/2.00  --abstr_ref_prep                        false
% 11.98/2.00  --abstr_ref_until_sat                   false
% 11.98/2.00  --abstr_ref_sig_restrict                funpre
% 11.98/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.98/2.00  --abstr_ref_under                       []
% 11.98/2.00  
% 11.98/2.00  ------ SAT Options
% 11.98/2.00  
% 11.98/2.00  --sat_mode                              false
% 11.98/2.00  --sat_fm_restart_options                ""
% 11.98/2.00  --sat_gr_def                            false
% 11.98/2.00  --sat_epr_types                         true
% 11.98/2.00  --sat_non_cyclic_types                  false
% 11.98/2.00  --sat_finite_models                     false
% 11.98/2.00  --sat_fm_lemmas                         false
% 11.98/2.00  --sat_fm_prep                           false
% 11.98/2.00  --sat_fm_uc_incr                        true
% 11.98/2.00  --sat_out_model                         small
% 11.98/2.00  --sat_out_clauses                       false
% 11.98/2.00  
% 11.98/2.00  ------ QBF Options
% 11.98/2.00  
% 11.98/2.00  --qbf_mode                              false
% 11.98/2.00  --qbf_elim_univ                         false
% 11.98/2.00  --qbf_dom_inst                          none
% 11.98/2.00  --qbf_dom_pre_inst                      false
% 11.98/2.00  --qbf_sk_in                             false
% 11.98/2.00  --qbf_pred_elim                         true
% 11.98/2.00  --qbf_split                             512
% 11.98/2.00  
% 11.98/2.00  ------ BMC1 Options
% 11.98/2.00  
% 11.98/2.00  --bmc1_incremental                      false
% 11.98/2.00  --bmc1_axioms                           reachable_all
% 11.98/2.00  --bmc1_min_bound                        0
% 11.98/2.00  --bmc1_max_bound                        -1
% 11.98/2.00  --bmc1_max_bound_default                -1
% 11.98/2.00  --bmc1_symbol_reachability              true
% 11.98/2.00  --bmc1_property_lemmas                  false
% 11.98/2.00  --bmc1_k_induction                      false
% 11.98/2.00  --bmc1_non_equiv_states                 false
% 11.98/2.00  --bmc1_deadlock                         false
% 11.98/2.00  --bmc1_ucm                              false
% 11.98/2.00  --bmc1_add_unsat_core                   none
% 11.98/2.00  --bmc1_unsat_core_children              false
% 11.98/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.98/2.00  --bmc1_out_stat                         full
% 11.98/2.00  --bmc1_ground_init                      false
% 11.98/2.00  --bmc1_pre_inst_next_state              false
% 11.98/2.00  --bmc1_pre_inst_state                   false
% 11.98/2.00  --bmc1_pre_inst_reach_state             false
% 11.98/2.00  --bmc1_out_unsat_core                   false
% 11.98/2.00  --bmc1_aig_witness_out                  false
% 11.98/2.00  --bmc1_verbose                          false
% 11.98/2.00  --bmc1_dump_clauses_tptp                false
% 11.98/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.98/2.00  --bmc1_dump_file                        -
% 11.98/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.98/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.98/2.00  --bmc1_ucm_extend_mode                  1
% 11.98/2.00  --bmc1_ucm_init_mode                    2
% 11.98/2.00  --bmc1_ucm_cone_mode                    none
% 11.98/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.98/2.00  --bmc1_ucm_relax_model                  4
% 11.98/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.98/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.98/2.00  --bmc1_ucm_layered_model                none
% 11.98/2.00  --bmc1_ucm_max_lemma_size               10
% 11.98/2.00  
% 11.98/2.00  ------ AIG Options
% 11.98/2.00  
% 11.98/2.00  --aig_mode                              false
% 11.98/2.00  
% 11.98/2.00  ------ Instantiation Options
% 11.98/2.00  
% 11.98/2.00  --instantiation_flag                    true
% 11.98/2.00  --inst_sos_flag                         true
% 11.98/2.00  --inst_sos_phase                        true
% 11.98/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.98/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.98/2.00  --inst_lit_sel_side                     num_symb
% 11.98/2.00  --inst_solver_per_active                1400
% 11.98/2.00  --inst_solver_calls_frac                1.
% 11.98/2.00  --inst_passive_queue_type               priority_queues
% 11.98/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.98/2.00  --inst_passive_queues_freq              [25;2]
% 11.98/2.00  --inst_dismatching                      true
% 11.98/2.00  --inst_eager_unprocessed_to_passive     true
% 11.98/2.00  --inst_prop_sim_given                   true
% 11.98/2.00  --inst_prop_sim_new                     false
% 11.98/2.00  --inst_subs_new                         false
% 11.98/2.00  --inst_eq_res_simp                      false
% 11.98/2.00  --inst_subs_given                       false
% 11.98/2.00  --inst_orphan_elimination               true
% 11.98/2.00  --inst_learning_loop_flag               true
% 11.98/2.00  --inst_learning_start                   3000
% 11.98/2.00  --inst_learning_factor                  2
% 11.98/2.00  --inst_start_prop_sim_after_learn       3
% 11.98/2.00  --inst_sel_renew                        solver
% 11.98/2.00  --inst_lit_activity_flag                true
% 11.98/2.00  --inst_restr_to_given                   false
% 11.98/2.00  --inst_activity_threshold               500
% 11.98/2.00  --inst_out_proof                        true
% 11.98/2.00  
% 11.98/2.00  ------ Resolution Options
% 11.98/2.00  
% 11.98/2.00  --resolution_flag                       true
% 11.98/2.00  --res_lit_sel                           adaptive
% 11.98/2.00  --res_lit_sel_side                      none
% 11.98/2.00  --res_ordering                          kbo
% 11.98/2.00  --res_to_prop_solver                    active
% 11.98/2.00  --res_prop_simpl_new                    false
% 11.98/2.00  --res_prop_simpl_given                  true
% 11.98/2.00  --res_passive_queue_type                priority_queues
% 11.98/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.98/2.00  --res_passive_queues_freq               [15;5]
% 11.98/2.00  --res_forward_subs                      full
% 11.98/2.00  --res_backward_subs                     full
% 11.98/2.00  --res_forward_subs_resolution           true
% 11.98/2.00  --res_backward_subs_resolution          true
% 11.98/2.00  --res_orphan_elimination                true
% 11.98/2.00  --res_time_limit                        2.
% 11.98/2.00  --res_out_proof                         true
% 11.98/2.00  
% 11.98/2.00  ------ Superposition Options
% 11.98/2.00  
% 11.98/2.00  --superposition_flag                    true
% 11.98/2.00  --sup_passive_queue_type                priority_queues
% 11.98/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.98/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.98/2.00  --demod_completeness_check              fast
% 11.98/2.00  --demod_use_ground                      true
% 11.98/2.00  --sup_to_prop_solver                    passive
% 11.98/2.00  --sup_prop_simpl_new                    true
% 11.98/2.00  --sup_prop_simpl_given                  true
% 11.98/2.00  --sup_fun_splitting                     true
% 11.98/2.00  --sup_smt_interval                      50000
% 11.98/2.00  
% 11.98/2.00  ------ Superposition Simplification Setup
% 11.98/2.00  
% 11.98/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.98/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.98/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.98/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.98/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.98/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.98/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.98/2.00  --sup_immed_triv                        [TrivRules]
% 11.98/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.98/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.98/2.00  --sup_immed_bw_main                     []
% 11.98/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.98/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.98/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.98/2.00  --sup_input_bw                          []
% 11.98/2.00  
% 11.98/2.00  ------ Combination Options
% 11.98/2.00  
% 11.98/2.00  --comb_res_mult                         3
% 11.98/2.00  --comb_sup_mult                         2
% 11.98/2.00  --comb_inst_mult                        10
% 11.98/2.00  
% 11.98/2.00  ------ Debug Options
% 11.98/2.00  
% 11.98/2.00  --dbg_backtrace                         false
% 11.98/2.00  --dbg_dump_prop_clauses                 false
% 11.98/2.00  --dbg_dump_prop_clauses_file            -
% 11.98/2.00  --dbg_out_stat                          false
% 11.98/2.00  ------ Parsing...
% 11.98/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.98/2.00  
% 11.98/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.98/2.00  
% 11.98/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.98/2.00  
% 11.98/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.98/2.00  ------ Proving...
% 11.98/2.00  ------ Problem Properties 
% 11.98/2.00  
% 11.98/2.00  
% 11.98/2.00  clauses                                 23
% 11.98/2.00  conjectures                             2
% 11.98/2.00  EPR                                     4
% 11.98/2.00  Horn                                    20
% 11.98/2.00  unary                                   11
% 11.98/2.00  binary                                  5
% 11.98/2.00  lits                                    42
% 11.98/2.00  lits eq                                 14
% 11.98/2.00  fd_pure                                 0
% 11.98/2.00  fd_pseudo                               0
% 11.98/2.00  fd_cond                                 0
% 11.98/2.00  fd_pseudo_cond                          2
% 11.98/2.00  AC symbols                              1
% 11.98/2.00  
% 11.98/2.00  ------ Schedule dynamic 5 is on 
% 11.98/2.00  
% 11.98/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.98/2.00  
% 11.98/2.00  
% 11.98/2.00  ------ 
% 11.98/2.00  Current options:
% 11.98/2.00  ------ 
% 11.98/2.00  
% 11.98/2.00  ------ Input Options
% 11.98/2.00  
% 11.98/2.00  --out_options                           all
% 11.98/2.00  --tptp_safe_out                         true
% 11.98/2.00  --problem_path                          ""
% 11.98/2.00  --include_path                          ""
% 11.98/2.00  --clausifier                            res/vclausify_rel
% 11.98/2.00  --clausifier_options                    ""
% 11.98/2.00  --stdin                                 false
% 11.98/2.00  --stats_out                             all
% 11.98/2.00  
% 11.98/2.00  ------ General Options
% 11.98/2.00  
% 11.98/2.00  --fof                                   false
% 11.98/2.00  --time_out_real                         305.
% 11.98/2.00  --time_out_virtual                      -1.
% 11.98/2.00  --symbol_type_check                     false
% 11.98/2.00  --clausify_out                          false
% 11.98/2.00  --sig_cnt_out                           false
% 11.98/2.00  --trig_cnt_out                          false
% 11.98/2.00  --trig_cnt_out_tolerance                1.
% 11.98/2.00  --trig_cnt_out_sk_spl                   false
% 11.98/2.00  --abstr_cl_out                          false
% 11.98/2.00  
% 11.98/2.00  ------ Global Options
% 11.98/2.00  
% 11.98/2.00  --schedule                              default
% 11.98/2.00  --add_important_lit                     false
% 11.98/2.00  --prop_solver_per_cl                    1000
% 11.98/2.00  --min_unsat_core                        false
% 11.98/2.00  --soft_assumptions                      false
% 11.98/2.00  --soft_lemma_size                       3
% 11.98/2.00  --prop_impl_unit_size                   0
% 11.98/2.00  --prop_impl_unit                        []
% 11.98/2.00  --share_sel_clauses                     true
% 11.98/2.00  --reset_solvers                         false
% 11.98/2.00  --bc_imp_inh                            [conj_cone]
% 11.98/2.00  --conj_cone_tolerance                   3.
% 11.98/2.00  --extra_neg_conj                        none
% 11.98/2.00  --large_theory_mode                     true
% 11.98/2.00  --prolific_symb_bound                   200
% 11.98/2.00  --lt_threshold                          2000
% 11.98/2.00  --clause_weak_htbl                      true
% 11.98/2.00  --gc_record_bc_elim                     false
% 11.98/2.00  
% 11.98/2.00  ------ Preprocessing Options
% 11.98/2.00  
% 11.98/2.00  --preprocessing_flag                    true
% 11.98/2.00  --time_out_prep_mult                    0.1
% 11.98/2.00  --splitting_mode                        input
% 11.98/2.00  --splitting_grd                         true
% 11.98/2.00  --splitting_cvd                         false
% 11.98/2.00  --splitting_cvd_svl                     false
% 11.98/2.00  --splitting_nvd                         32
% 11.98/2.00  --sub_typing                            true
% 11.98/2.00  --prep_gs_sim                           true
% 11.98/2.00  --prep_unflatten                        true
% 11.98/2.00  --prep_res_sim                          true
% 11.98/2.00  --prep_upred                            true
% 11.98/2.00  --prep_sem_filter                       exhaustive
% 11.98/2.00  --prep_sem_filter_out                   false
% 11.98/2.00  --pred_elim                             true
% 11.98/2.00  --res_sim_input                         true
% 11.98/2.00  --eq_ax_congr_red                       true
% 11.98/2.00  --pure_diseq_elim                       true
% 11.98/2.00  --brand_transform                       false
% 11.98/2.00  --non_eq_to_eq                          false
% 11.98/2.00  --prep_def_merge                        true
% 11.98/2.00  --prep_def_merge_prop_impl              false
% 11.98/2.00  --prep_def_merge_mbd                    true
% 11.98/2.00  --prep_def_merge_tr_red                 false
% 11.98/2.00  --prep_def_merge_tr_cl                  false
% 11.98/2.00  --smt_preprocessing                     true
% 11.98/2.00  --smt_ac_axioms                         fast
% 11.98/2.00  --preprocessed_out                      false
% 11.98/2.00  --preprocessed_stats                    false
% 11.98/2.00  
% 11.98/2.00  ------ Abstraction refinement Options
% 11.98/2.00  
% 11.98/2.00  --abstr_ref                             []
% 11.98/2.00  --abstr_ref_prep                        false
% 11.98/2.00  --abstr_ref_until_sat                   false
% 11.98/2.00  --abstr_ref_sig_restrict                funpre
% 11.98/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.98/2.00  --abstr_ref_under                       []
% 11.98/2.00  
% 11.98/2.00  ------ SAT Options
% 11.98/2.00  
% 11.98/2.00  --sat_mode                              false
% 11.98/2.00  --sat_fm_restart_options                ""
% 11.98/2.00  --sat_gr_def                            false
% 11.98/2.00  --sat_epr_types                         true
% 11.98/2.00  --sat_non_cyclic_types                  false
% 11.98/2.00  --sat_finite_models                     false
% 11.98/2.00  --sat_fm_lemmas                         false
% 11.98/2.00  --sat_fm_prep                           false
% 11.98/2.00  --sat_fm_uc_incr                        true
% 11.98/2.00  --sat_out_model                         small
% 11.98/2.00  --sat_out_clauses                       false
% 11.98/2.00  
% 11.98/2.00  ------ QBF Options
% 11.98/2.00  
% 11.98/2.00  --qbf_mode                              false
% 11.98/2.00  --qbf_elim_univ                         false
% 11.98/2.00  --qbf_dom_inst                          none
% 11.98/2.00  --qbf_dom_pre_inst                      false
% 11.98/2.00  --qbf_sk_in                             false
% 11.98/2.00  --qbf_pred_elim                         true
% 11.98/2.00  --qbf_split                             512
% 11.98/2.00  
% 11.98/2.00  ------ BMC1 Options
% 11.98/2.00  
% 11.98/2.00  --bmc1_incremental                      false
% 11.98/2.00  --bmc1_axioms                           reachable_all
% 11.98/2.00  --bmc1_min_bound                        0
% 11.98/2.00  --bmc1_max_bound                        -1
% 11.98/2.00  --bmc1_max_bound_default                -1
% 11.98/2.00  --bmc1_symbol_reachability              true
% 11.98/2.00  --bmc1_property_lemmas                  false
% 11.98/2.00  --bmc1_k_induction                      false
% 11.98/2.00  --bmc1_non_equiv_states                 false
% 11.98/2.00  --bmc1_deadlock                         false
% 11.98/2.00  --bmc1_ucm                              false
% 11.98/2.00  --bmc1_add_unsat_core                   none
% 11.98/2.00  --bmc1_unsat_core_children              false
% 11.98/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.98/2.00  --bmc1_out_stat                         full
% 11.98/2.00  --bmc1_ground_init                      false
% 11.98/2.00  --bmc1_pre_inst_next_state              false
% 11.98/2.00  --bmc1_pre_inst_state                   false
% 11.98/2.00  --bmc1_pre_inst_reach_state             false
% 11.98/2.00  --bmc1_out_unsat_core                   false
% 11.98/2.00  --bmc1_aig_witness_out                  false
% 11.98/2.00  --bmc1_verbose                          false
% 11.98/2.00  --bmc1_dump_clauses_tptp                false
% 11.98/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.98/2.00  --bmc1_dump_file                        -
% 11.98/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.98/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.98/2.00  --bmc1_ucm_extend_mode                  1
% 11.98/2.00  --bmc1_ucm_init_mode                    2
% 11.98/2.00  --bmc1_ucm_cone_mode                    none
% 11.98/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.98/2.00  --bmc1_ucm_relax_model                  4
% 11.98/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.98/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.98/2.00  --bmc1_ucm_layered_model                none
% 11.98/2.00  --bmc1_ucm_max_lemma_size               10
% 11.98/2.00  
% 11.98/2.00  ------ AIG Options
% 11.98/2.00  
% 11.98/2.00  --aig_mode                              false
% 11.98/2.00  
% 11.98/2.00  ------ Instantiation Options
% 11.98/2.00  
% 11.98/2.00  --instantiation_flag                    true
% 11.98/2.00  --inst_sos_flag                         true
% 11.98/2.00  --inst_sos_phase                        true
% 11.98/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.98/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.98/2.00  --inst_lit_sel_side                     none
% 11.98/2.00  --inst_solver_per_active                1400
% 11.98/2.00  --inst_solver_calls_frac                1.
% 11.98/2.00  --inst_passive_queue_type               priority_queues
% 11.98/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.98/2.00  --inst_passive_queues_freq              [25;2]
% 11.98/2.00  --inst_dismatching                      true
% 11.98/2.00  --inst_eager_unprocessed_to_passive     true
% 11.98/2.00  --inst_prop_sim_given                   true
% 11.98/2.00  --inst_prop_sim_new                     false
% 11.98/2.00  --inst_subs_new                         false
% 11.98/2.00  --inst_eq_res_simp                      false
% 11.98/2.00  --inst_subs_given                       false
% 11.98/2.00  --inst_orphan_elimination               true
% 11.98/2.00  --inst_learning_loop_flag               true
% 11.98/2.00  --inst_learning_start                   3000
% 11.98/2.00  --inst_learning_factor                  2
% 11.98/2.00  --inst_start_prop_sim_after_learn       3
% 11.98/2.00  --inst_sel_renew                        solver
% 11.98/2.00  --inst_lit_activity_flag                true
% 11.98/2.00  --inst_restr_to_given                   false
% 11.98/2.00  --inst_activity_threshold               500
% 11.98/2.00  --inst_out_proof                        true
% 11.98/2.00  
% 11.98/2.00  ------ Resolution Options
% 11.98/2.00  
% 11.98/2.00  --resolution_flag                       false
% 11.98/2.00  --res_lit_sel                           adaptive
% 11.98/2.00  --res_lit_sel_side                      none
% 11.98/2.00  --res_ordering                          kbo
% 11.98/2.00  --res_to_prop_solver                    active
% 11.98/2.00  --res_prop_simpl_new                    false
% 11.98/2.00  --res_prop_simpl_given                  true
% 11.98/2.00  --res_passive_queue_type                priority_queues
% 11.98/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.98/2.00  --res_passive_queues_freq               [15;5]
% 11.98/2.00  --res_forward_subs                      full
% 11.98/2.00  --res_backward_subs                     full
% 11.98/2.00  --res_forward_subs_resolution           true
% 11.98/2.00  --res_backward_subs_resolution          true
% 11.98/2.00  --res_orphan_elimination                true
% 11.98/2.00  --res_time_limit                        2.
% 11.98/2.00  --res_out_proof                         true
% 11.98/2.00  
% 11.98/2.00  ------ Superposition Options
% 11.98/2.00  
% 11.98/2.00  --superposition_flag                    true
% 11.98/2.00  --sup_passive_queue_type                priority_queues
% 11.98/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.98/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.98/2.00  --demod_completeness_check              fast
% 11.98/2.00  --demod_use_ground                      true
% 11.98/2.00  --sup_to_prop_solver                    passive
% 11.98/2.00  --sup_prop_simpl_new                    true
% 11.98/2.00  --sup_prop_simpl_given                  true
% 11.98/2.00  --sup_fun_splitting                     true
% 11.98/2.00  --sup_smt_interval                      50000
% 11.98/2.00  
% 11.98/2.00  ------ Superposition Simplification Setup
% 11.98/2.00  
% 11.98/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.98/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.98/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.98/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.98/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.98/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.98/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.98/2.00  --sup_immed_triv                        [TrivRules]
% 11.98/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.98/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.98/2.00  --sup_immed_bw_main                     []
% 11.98/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.98/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.98/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.98/2.00  --sup_input_bw                          []
% 11.98/2.00  
% 11.98/2.00  ------ Combination Options
% 11.98/2.00  
% 11.98/2.00  --comb_res_mult                         3
% 11.98/2.00  --comb_sup_mult                         2
% 11.98/2.00  --comb_inst_mult                        10
% 11.98/2.00  
% 11.98/2.00  ------ Debug Options
% 11.98/2.00  
% 11.98/2.00  --dbg_backtrace                         false
% 11.98/2.00  --dbg_dump_prop_clauses                 false
% 11.98/2.00  --dbg_dump_prop_clauses_file            -
% 11.98/2.00  --dbg_out_stat                          false
% 11.98/2.00  
% 11.98/2.00  
% 11.98/2.00  
% 11.98/2.00  
% 11.98/2.00  ------ Proving...
% 11.98/2.00  
% 11.98/2.00  
% 11.98/2.00  % SZS status Theorem for theBenchmark.p
% 11.98/2.00  
% 11.98/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.98/2.00  
% 11.98/2.00  fof(f25,conjecture,(
% 11.98/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f26,negated_conjecture,(
% 11.98/2.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 11.98/2.00    inference(negated_conjecture,[],[f25])).
% 11.98/2.00  
% 11.98/2.00  fof(f35,plain,(
% 11.98/2.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/2.00    inference(ennf_transformation,[],[f26])).
% 11.98/2.00  
% 11.98/2.00  fof(f41,plain,(
% 11.98/2.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 11.98/2.00    introduced(choice_axiom,[])).
% 11.98/2.00  
% 11.98/2.00  fof(f42,plain,(
% 11.98/2.00    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.98/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f41])).
% 11.98/2.00  
% 11.98/2.00  fof(f73,plain,(
% 11.98/2.00    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.98/2.00    inference(cnf_transformation,[],[f42])).
% 11.98/2.00  
% 11.98/2.00  fof(f21,axiom,(
% 11.98/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f31,plain,(
% 11.98/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/2.00    inference(ennf_transformation,[],[f21])).
% 11.98/2.00  
% 11.98/2.00  fof(f69,plain,(
% 11.98/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/2.00    inference(cnf_transformation,[],[f31])).
% 11.98/2.00  
% 11.98/2.00  fof(f5,axiom,(
% 11.98/2.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f47,plain,(
% 11.98/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.98/2.00    inference(cnf_transformation,[],[f5])).
% 11.98/2.00  
% 11.98/2.00  fof(f81,plain,(
% 11.98/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/2.00    inference(definition_unfolding,[],[f69,f47])).
% 11.98/2.00  
% 11.98/2.00  fof(f19,axiom,(
% 11.98/2.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f30,plain,(
% 11.98/2.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.98/2.00    inference(ennf_transformation,[],[f19])).
% 11.98/2.00  
% 11.98/2.00  fof(f40,plain,(
% 11.98/2.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.98/2.00    inference(nnf_transformation,[],[f30])).
% 11.98/2.00  
% 11.98/2.00  fof(f64,plain,(
% 11.98/2.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.98/2.00    inference(cnf_transformation,[],[f40])).
% 11.98/2.00  
% 11.98/2.00  fof(f23,axiom,(
% 11.98/2.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f71,plain,(
% 11.98/2.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.98/2.00    inference(cnf_transformation,[],[f23])).
% 11.98/2.00  
% 11.98/2.00  fof(f17,axiom,(
% 11.98/2.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f36,plain,(
% 11.98/2.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.98/2.00    inference(nnf_transformation,[],[f17])).
% 11.98/2.00  
% 11.98/2.00  fof(f37,plain,(
% 11.98/2.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.98/2.00    inference(rectify,[],[f36])).
% 11.98/2.00  
% 11.98/2.00  fof(f38,plain,(
% 11.98/2.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 11.98/2.00    introduced(choice_axiom,[])).
% 11.98/2.00  
% 11.98/2.00  fof(f39,plain,(
% 11.98/2.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.98/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 11.98/2.00  
% 11.98/2.00  fof(f59,plain,(
% 11.98/2.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.98/2.00    inference(cnf_transformation,[],[f39])).
% 11.98/2.00  
% 11.98/2.00  fof(f84,plain,(
% 11.98/2.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.98/2.00    inference(equality_resolution,[],[f59])).
% 11.98/2.00  
% 11.98/2.00  fof(f6,axiom,(
% 11.98/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f29,plain,(
% 11.98/2.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.98/2.00    inference(ennf_transformation,[],[f6])).
% 11.98/2.00  
% 11.98/2.00  fof(f48,plain,(
% 11.98/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.98/2.00    inference(cnf_transformation,[],[f29])).
% 11.98/2.00  
% 11.98/2.00  fof(f1,axiom,(
% 11.98/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f43,plain,(
% 11.98/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.98/2.00    inference(cnf_transformation,[],[f1])).
% 11.98/2.00  
% 11.98/2.00  fof(f22,axiom,(
% 11.98/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f32,plain,(
% 11.98/2.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/2.00    inference(ennf_transformation,[],[f22])).
% 11.98/2.00  
% 11.98/2.00  fof(f70,plain,(
% 11.98/2.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/2.00    inference(cnf_transformation,[],[f32])).
% 11.98/2.00  
% 11.98/2.00  fof(f24,axiom,(
% 11.98/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f33,plain,(
% 11.98/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.98/2.00    inference(ennf_transformation,[],[f24])).
% 11.98/2.00  
% 11.98/2.00  fof(f34,plain,(
% 11.98/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/2.00    inference(flattening,[],[f33])).
% 11.98/2.00  
% 11.98/2.00  fof(f72,plain,(
% 11.98/2.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/2.00    inference(cnf_transformation,[],[f34])).
% 11.98/2.00  
% 11.98/2.00  fof(f10,axiom,(
% 11.98/2.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f52,plain,(
% 11.98/2.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 11.98/2.00    inference(cnf_transformation,[],[f10])).
% 11.98/2.00  
% 11.98/2.00  fof(f82,plain,(
% 11.98/2.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/2.00    inference(definition_unfolding,[],[f72,f52])).
% 11.98/2.00  
% 11.98/2.00  fof(f8,axiom,(
% 11.98/2.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f50,plain,(
% 11.98/2.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.98/2.00    inference(cnf_transformation,[],[f8])).
% 11.98/2.00  
% 11.98/2.00  fof(f2,axiom,(
% 11.98/2.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f44,plain,(
% 11.98/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.98/2.00    inference(cnf_transformation,[],[f2])).
% 11.98/2.00  
% 11.98/2.00  fof(f3,axiom,(
% 11.98/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f27,plain,(
% 11.98/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.98/2.00    inference(unused_predicate_definition_removal,[],[f3])).
% 11.98/2.00  
% 11.98/2.00  fof(f28,plain,(
% 11.98/2.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 11.98/2.00    inference(ennf_transformation,[],[f27])).
% 11.98/2.00  
% 11.98/2.00  fof(f45,plain,(
% 11.98/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.98/2.00    inference(cnf_transformation,[],[f28])).
% 11.98/2.00  
% 11.98/2.00  fof(f4,axiom,(
% 11.98/2.00    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f46,plain,(
% 11.98/2.00    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 11.98/2.00    inference(cnf_transformation,[],[f4])).
% 11.98/2.00  
% 11.98/2.00  fof(f7,axiom,(
% 11.98/2.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f49,plain,(
% 11.98/2.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.98/2.00    inference(cnf_transformation,[],[f7])).
% 11.98/2.00  
% 11.98/2.00  fof(f9,axiom,(
% 11.98/2.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f51,plain,(
% 11.98/2.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.98/2.00    inference(cnf_transformation,[],[f9])).
% 11.98/2.00  
% 11.98/2.00  fof(f74,plain,(
% 11.98/2.00    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))),
% 11.98/2.00    inference(cnf_transformation,[],[f42])).
% 11.98/2.00  
% 11.98/2.00  fof(f20,axiom,(
% 11.98/2.00    ! [X0] : k2_subset_1(X0) = X0),
% 11.98/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.98/2.00  
% 11.98/2.00  fof(f68,plain,(
% 11.98/2.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.98/2.00    inference(cnf_transformation,[],[f20])).
% 11.98/2.00  
% 11.98/2.00  cnf(c_23,negated_conjecture,
% 11.98/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 11.98/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.98/2.00  
% 11.98/2.00  cnf(c_1147,plain,
% 11.98/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.98/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.98/2.00  
% 11.98/2.00  cnf(c_18,plain,
% 11.98/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.98/2.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 11.98/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.98/2.00  
% 11.98/2.00  cnf(c_1151,plain,
% 11.98/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 11.98/2.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.98/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.98/2.00  
% 11.98/2.00  cnf(c_32253,plain,
% 11.98/2.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 11.98/2.00      inference(superposition,[status(thm)],[c_1147,c_1151]) ).
% 11.98/2.00  
% 11.98/2.00  cnf(c_16,plain,
% 11.98/2.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.98/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1152,plain,
% 11.98/2.01      ( m1_subset_1(X0,X1) != iProver_top
% 11.98/2.01      | r2_hidden(X0,X1) = iProver_top
% 11.98/2.01      | v1_xboole_0(X1) = iProver_top ),
% 11.98/2.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_2747,plain,
% 11.98/2.01      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 11.98/2.01      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_1147,c_1152]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_20,plain,
% 11.98/2.01      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.98/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_28,plain,
% 11.98/2.01      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 11.98/2.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_30,plain,
% 11.98/2.01      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 11.98/2.01      inference(instantiation,[status(thm)],[c_28]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_3046,plain,
% 11.98/2.01      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.98/2.01      inference(global_propositional_subsumption,
% 11.98/2.01                [status(thm)],
% 11.98/2.01                [c_2747,c_30]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_11,plain,
% 11.98/2.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.98/2.01      inference(cnf_transformation,[],[f84]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1156,plain,
% 11.98/2.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.98/2.01      | r1_tarski(X0,X1) = iProver_top ),
% 11.98/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_7876,plain,
% 11.98/2.01      ( r1_tarski(sK2,sK1) = iProver_top ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_3046,c_1156]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_4,plain,
% 11.98/2.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.98/2.01      inference(cnf_transformation,[],[f48]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1160,plain,
% 11.98/2.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.98/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_8328,plain,
% 11.98/2.01      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_7876,c_1160]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_0,plain,
% 11.98/2.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.98/2.01      inference(cnf_transformation,[],[f43]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_8333,plain,
% 11.98/2.01      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_8328,c_0]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_32254,plain,
% 11.98/2.01      ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
% 11.98/2.01      inference(light_normalisation,[status(thm)],[c_32253,c_8333]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_19,plain,
% 11.98/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.98/2.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 11.98/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1150,plain,
% 11.98/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.98/2.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 11.98/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_33587,plain,
% 11.98/2.01      ( m1_subset_1(k5_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 11.98/2.01      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_32254,c_1150]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_24,plain,
% 11.98/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.98/2.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_34078,plain,
% 11.98/2.01      ( m1_subset_1(k5_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 11.98/2.01      inference(global_propositional_subsumption,
% 11.98/2.01                [status(thm)],
% 11.98/2.01                [c_33587,c_24]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_21,plain,
% 11.98/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.98/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.98/2.01      | k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 11.98/2.01      inference(cnf_transformation,[],[f82]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_6,plain,
% 11.98/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.98/2.01      inference(cnf_transformation,[],[f50]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1,plain,
% 11.98/2.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.98/2.01      inference(cnf_transformation,[],[f44]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_757,plain,
% 11.98/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.98/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.98/2.01      | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X0,X2) ),
% 11.98/2.01      inference(theory_normalisation,[status(thm)],[c_21,c_6,c_1]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1148,plain,
% 11.98/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k4_subset_1(X2,X0,X1)
% 11.98/2.01      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 11.98/2.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 11.98/2.01      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1449,plain,
% 11.98/2.01      ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(sK2,X0))) = k4_subset_1(sK1,sK2,X0)
% 11.98/2.01      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_1147,c_1148]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_34089,plain,
% 11.98/2.01      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_34078,c_1449]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_2,plain,
% 11.98/2.01      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.98/2.01      inference(cnf_transformation,[],[f45]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_3,plain,
% 11.98/2.01      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 11.98/2.01      inference(cnf_transformation,[],[f46]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_249,plain,
% 11.98/2.01      ( k5_xboole_0(X0,X1) != X2
% 11.98/2.01      | k3_xboole_0(X0,X1) != X3
% 11.98/2.01      | k3_xboole_0(X3,X2) = k1_xboole_0 ),
% 11.98/2.01      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_250,plain,
% 11.98/2.01      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.98/2.01      inference(unflattening,[status(thm)],[c_249]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1921,plain,
% 11.98/2.01      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_1,c_250]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_8331,plain,
% 11.98/2.01      ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_8328,c_1921]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_34090,plain,
% 11.98/2.01      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0)) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
% 11.98/2.01      inference(light_normalisation,[status(thm)],[c_34089,c_8331]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_5,plain,
% 11.98/2.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.98/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1399,plain,
% 11.98/2.01      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_7,plain,
% 11.98/2.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.98/2.01      inference(cnf_transformation,[],[f51]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1456,plain,
% 11.98/2.01      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1460,plain,
% 11.98/2.01      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 11.98/2.01      inference(demodulation,[status(thm)],[c_1456,c_1399]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1176,plain,
% 11.98/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1597,plain,
% 11.98/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_7,c_1176]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1612,plain,
% 11.98/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 11.98/2.01      inference(demodulation,[status(thm)],[c_1597,c_5]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1780,plain,
% 11.98/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_1460,c_1612]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1177,plain,
% 11.98/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_2866,plain,
% 11.98/2.01      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
% 11.98/2.01      inference(superposition,[status(thm)],[c_1780,c_1177]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_34091,plain,
% 11.98/2.01      ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
% 11.98/2.01      inference(demodulation,[status(thm)],[c_34090,c_1399,c_2866]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_22,negated_conjecture,
% 11.98/2.01      ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
% 11.98/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_17,plain,
% 11.98/2.01      ( k2_subset_1(X0) = X0 ),
% 11.98/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_1161,plain,
% 11.98/2.01      ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
% 11.98/2.01      inference(demodulation,[status(thm)],[c_22,c_17]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(c_33497,plain,
% 11.98/2.01      ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) != sK1 ),
% 11.98/2.01      inference(demodulation,[status(thm)],[c_32254,c_1161]) ).
% 11.98/2.01  
% 11.98/2.01  cnf(contradiction,plain,
% 11.98/2.01      ( $false ),
% 11.98/2.01      inference(minisat,[status(thm)],[c_34091,c_33497]) ).
% 11.98/2.01  
% 11.98/2.01  
% 11.98/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.98/2.01  
% 11.98/2.01  ------                               Statistics
% 11.98/2.01  
% 11.98/2.01  ------ General
% 11.98/2.01  
% 11.98/2.01  abstr_ref_over_cycles:                  0
% 11.98/2.01  abstr_ref_under_cycles:                 0
% 11.98/2.01  gc_basic_clause_elim:                   0
% 11.98/2.01  forced_gc_time:                         0
% 11.98/2.01  parsing_time:                           0.016
% 11.98/2.01  unif_index_cands_time:                  0.
% 11.98/2.01  unif_index_add_time:                    0.
% 11.98/2.01  orderings_time:                         0.
% 11.98/2.01  out_proof_time:                         0.011
% 11.98/2.01  total_time:                             1.466
% 11.98/2.01  num_of_symbols:                         48
% 11.98/2.01  num_of_terms:                           76719
% 11.98/2.01  
% 11.98/2.01  ------ Preprocessing
% 11.98/2.01  
% 11.98/2.01  num_of_splits:                          0
% 11.98/2.01  num_of_split_atoms:                     0
% 11.98/2.01  num_of_reused_defs:                     0
% 11.98/2.01  num_eq_ax_congr_red:                    35
% 11.98/2.01  num_of_sem_filtered_clauses:            1
% 11.98/2.01  num_of_subtypes:                        0
% 11.98/2.01  monotx_restored_types:                  0
% 11.98/2.01  sat_num_of_epr_types:                   0
% 11.98/2.01  sat_num_of_non_cyclic_types:            0
% 11.98/2.01  sat_guarded_non_collapsed_types:        0
% 11.98/2.01  num_pure_diseq_elim:                    0
% 11.98/2.01  simp_replaced_by:                       0
% 11.98/2.01  res_preprocessed:                       120
% 11.98/2.01  prep_upred:                             0
% 11.98/2.01  prep_unflattend:                        38
% 11.98/2.01  smt_new_axioms:                         0
% 11.98/2.01  pred_elim_cands:                        4
% 11.98/2.01  pred_elim:                              1
% 11.98/2.01  pred_elim_cl:                           1
% 11.98/2.01  pred_elim_cycles:                       5
% 11.98/2.01  merged_defs:                            8
% 11.98/2.01  merged_defs_ncl:                        0
% 11.98/2.01  bin_hyper_res:                          8
% 11.98/2.01  prep_cycles:                            4
% 11.98/2.01  pred_elim_time:                         0.005
% 11.98/2.01  splitting_time:                         0.
% 11.98/2.01  sem_filter_time:                        0.
% 11.98/2.01  monotx_time:                            0.
% 11.98/2.01  subtype_inf_time:                       0.
% 11.98/2.01  
% 11.98/2.01  ------ Problem properties
% 11.98/2.01  
% 11.98/2.01  clauses:                                23
% 11.98/2.01  conjectures:                            2
% 11.98/2.01  epr:                                    4
% 11.98/2.01  horn:                                   20
% 11.98/2.01  ground:                                 2
% 11.98/2.01  unary:                                  11
% 11.98/2.01  binary:                                 5
% 11.98/2.01  lits:                                   42
% 11.98/2.01  lits_eq:                                14
% 11.98/2.01  fd_pure:                                0
% 11.98/2.01  fd_pseudo:                              0
% 11.98/2.01  fd_cond:                                0
% 11.98/2.01  fd_pseudo_cond:                         2
% 11.98/2.01  ac_symbols:                             1
% 11.98/2.01  
% 11.98/2.01  ------ Propositional Solver
% 11.98/2.01  
% 11.98/2.01  prop_solver_calls:                      33
% 11.98/2.01  prop_fast_solver_calls:                 794
% 11.98/2.01  smt_solver_calls:                       0
% 11.98/2.01  smt_fast_solver_calls:                  0
% 11.98/2.01  prop_num_of_clauses:                    9193
% 11.98/2.01  prop_preprocess_simplified:             10070
% 11.98/2.01  prop_fo_subsumed:                       4
% 11.98/2.01  prop_solver_time:                       0.
% 11.98/2.01  smt_solver_time:                        0.
% 11.98/2.01  smt_fast_solver_time:                   0.
% 11.98/2.01  prop_fast_solver_time:                  0.
% 11.98/2.01  prop_unsat_core_time:                   0.
% 11.98/2.01  
% 11.98/2.01  ------ QBF
% 11.98/2.01  
% 11.98/2.01  qbf_q_res:                              0
% 11.98/2.01  qbf_num_tautologies:                    0
% 11.98/2.01  qbf_prep_cycles:                        0
% 11.98/2.01  
% 11.98/2.01  ------ BMC1
% 11.98/2.01  
% 11.98/2.01  bmc1_current_bound:                     -1
% 11.98/2.01  bmc1_last_solved_bound:                 -1
% 11.98/2.01  bmc1_unsat_core_size:                   -1
% 11.98/2.01  bmc1_unsat_core_parents_size:           -1
% 11.98/2.01  bmc1_merge_next_fun:                    0
% 11.98/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.98/2.01  
% 11.98/2.01  ------ Instantiation
% 11.98/2.01  
% 11.98/2.01  inst_num_of_clauses:                    2221
% 11.98/2.01  inst_num_in_passive:                    703
% 11.98/2.01  inst_num_in_active:                     729
% 11.98/2.01  inst_num_in_unprocessed:                789
% 11.98/2.01  inst_num_of_loops:                      790
% 11.98/2.01  inst_num_of_learning_restarts:          0
% 11.98/2.01  inst_num_moves_active_passive:          56
% 11.98/2.01  inst_lit_activity:                      0
% 11.98/2.01  inst_lit_activity_moves:                0
% 11.98/2.01  inst_num_tautologies:                   0
% 11.98/2.01  inst_num_prop_implied:                  0
% 11.98/2.01  inst_num_existing_simplified:           0
% 11.98/2.01  inst_num_eq_res_simplified:             0
% 11.98/2.01  inst_num_child_elim:                    0
% 11.98/2.01  inst_num_of_dismatching_blockings:      426
% 11.98/2.01  inst_num_of_non_proper_insts:           2519
% 11.98/2.01  inst_num_of_duplicates:                 0
% 11.98/2.01  inst_inst_num_from_inst_to_res:         0
% 11.98/2.01  inst_dismatching_checking_time:         0.
% 11.98/2.01  
% 11.98/2.01  ------ Resolution
% 11.98/2.01  
% 11.98/2.01  res_num_of_clauses:                     0
% 11.98/2.01  res_num_in_passive:                     0
% 11.98/2.01  res_num_in_active:                      0
% 11.98/2.01  res_num_of_loops:                       124
% 11.98/2.01  res_forward_subset_subsumed:            586
% 11.98/2.01  res_backward_subset_subsumed:           0
% 11.98/2.01  res_forward_subsumed:                   0
% 11.98/2.01  res_backward_subsumed:                  0
% 11.98/2.01  res_forward_subsumption_resolution:     2
% 11.98/2.01  res_backward_subsumption_resolution:    0
% 11.98/2.01  res_clause_to_clause_subsumption:       96572
% 11.98/2.01  res_orphan_elimination:                 0
% 11.98/2.01  res_tautology_del:                      195
% 11.98/2.01  res_num_eq_res_simplified:              0
% 11.98/2.01  res_num_sel_changes:                    0
% 11.98/2.01  res_moves_from_active_to_pass:          0
% 11.98/2.01  
% 11.98/2.01  ------ Superposition
% 11.98/2.01  
% 11.98/2.01  sup_time_total:                         0.
% 11.98/2.01  sup_time_generating:                    0.
% 11.98/2.01  sup_time_sim_full:                      0.
% 11.98/2.01  sup_time_sim_immed:                     0.
% 11.98/2.01  
% 11.98/2.01  sup_num_of_clauses:                     3377
% 11.98/2.01  sup_num_in_active:                      84
% 11.98/2.01  sup_num_in_passive:                     3293
% 11.98/2.01  sup_num_of_loops:                       156
% 11.98/2.01  sup_fw_superposition:                   8464
% 11.98/2.01  sup_bw_superposition:                   4754
% 11.98/2.01  sup_immediate_simplified:               7708
% 11.98/2.01  sup_given_eliminated:                   6
% 11.98/2.01  comparisons_done:                       0
% 11.98/2.01  comparisons_avoided:                    0
% 11.98/2.01  
% 11.98/2.01  ------ Simplifications
% 11.98/2.01  
% 11.98/2.01  
% 11.98/2.01  sim_fw_subset_subsumed:                 3
% 11.98/2.01  sim_bw_subset_subsumed:                 0
% 11.98/2.01  sim_fw_subsumed:                        1094
% 11.98/2.01  sim_bw_subsumed:                        29
% 11.98/2.01  sim_fw_subsumption_res:                 0
% 11.98/2.01  sim_bw_subsumption_res:                 0
% 11.98/2.01  sim_tautology_del:                      4
% 11.98/2.01  sim_eq_tautology_del:                   2093
% 11.98/2.01  sim_eq_res_simp:                        0
% 11.98/2.01  sim_fw_demodulated:                     7833
% 11.98/2.01  sim_bw_demodulated:                     125
% 11.98/2.01  sim_light_normalised:                   2428
% 11.98/2.01  sim_joinable_taut:                      341
% 11.98/2.01  sim_joinable_simp:                      0
% 11.98/2.01  sim_ac_normalised:                      0
% 11.98/2.01  sim_smt_subsumption:                    0
% 11.98/2.01  
%------------------------------------------------------------------------------
