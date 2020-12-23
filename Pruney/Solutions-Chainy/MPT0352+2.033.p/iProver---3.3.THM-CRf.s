%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:37 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 268 expanded)
%              Number of clauses        :   50 (  90 expanded)
%              Number of leaves         :   12 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  240 ( 976 expanded)
%              Number of equality atoms :   74 ( 159 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f26,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f25,f24])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f31,f31])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_412,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_413,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_1191,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_413])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1089,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1351,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1191,c_1089])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1090,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1352,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1191,c_1090])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_421,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_422,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_1194,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_422])).

cnf(c_1691,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1352,c_1194])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1261,plain,
    ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1268,plain,
    ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_1270,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_1695,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1691,c_1270])).

cnf(c_1795,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_1270,c_1691])).

cnf(c_1799,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1795,c_1194])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_376,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_377,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_379,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_23])).

cnf(c_1088,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1091,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1682,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1091])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1096,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2042,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_1682,c_1096])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2299,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2042,c_1])).

cnf(c_1095,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2594,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK3) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_1095])).

cnf(c_31635,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_2594])).

cnf(c_394,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_395,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_397,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_23])).

cnf(c_1087,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1683,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_1091])).

cnf(c_2043,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_1683,c_1096])).

cnf(c_2352,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2043,c_1])).

cnf(c_31657,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31635,c_2352])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31657,c_1695])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.15/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.15/1.51  
% 7.15/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.15/1.51  
% 7.15/1.51  ------  iProver source info
% 7.15/1.51  
% 7.15/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.15/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.15/1.51  git: non_committed_changes: false
% 7.15/1.51  git: last_make_outside_of_git: false
% 7.15/1.51  
% 7.15/1.51  ------ 
% 7.15/1.51  
% 7.15/1.51  ------ Input Options
% 7.15/1.51  
% 7.15/1.51  --out_options                           all
% 7.15/1.51  --tptp_safe_out                         true
% 7.15/1.51  --problem_path                          ""
% 7.15/1.51  --include_path                          ""
% 7.15/1.51  --clausifier                            res/vclausify_rel
% 7.15/1.51  --clausifier_options                    --mode clausify
% 7.15/1.51  --stdin                                 false
% 7.15/1.51  --stats_out                             all
% 7.15/1.51  
% 7.15/1.51  ------ General Options
% 7.15/1.51  
% 7.15/1.51  --fof                                   false
% 7.15/1.51  --time_out_real                         305.
% 7.15/1.51  --time_out_virtual                      -1.
% 7.15/1.51  --symbol_type_check                     false
% 7.15/1.51  --clausify_out                          false
% 7.15/1.51  --sig_cnt_out                           false
% 7.15/1.51  --trig_cnt_out                          false
% 7.15/1.51  --trig_cnt_out_tolerance                1.
% 7.15/1.51  --trig_cnt_out_sk_spl                   false
% 7.15/1.51  --abstr_cl_out                          false
% 7.15/1.51  
% 7.15/1.51  ------ Global Options
% 7.15/1.51  
% 7.15/1.51  --schedule                              default
% 7.15/1.51  --add_important_lit                     false
% 7.15/1.51  --prop_solver_per_cl                    1000
% 7.15/1.51  --min_unsat_core                        false
% 7.15/1.51  --soft_assumptions                      false
% 7.15/1.51  --soft_lemma_size                       3
% 7.15/1.51  --prop_impl_unit_size                   0
% 7.15/1.51  --prop_impl_unit                        []
% 7.15/1.51  --share_sel_clauses                     true
% 7.15/1.51  --reset_solvers                         false
% 7.15/1.51  --bc_imp_inh                            [conj_cone]
% 7.15/1.51  --conj_cone_tolerance                   3.
% 7.15/1.51  --extra_neg_conj                        none
% 7.15/1.51  --large_theory_mode                     true
% 7.15/1.51  --prolific_symb_bound                   200
% 7.15/1.51  --lt_threshold                          2000
% 7.15/1.51  --clause_weak_htbl                      true
% 7.15/1.51  --gc_record_bc_elim                     false
% 7.15/1.51  
% 7.15/1.51  ------ Preprocessing Options
% 7.15/1.51  
% 7.15/1.51  --preprocessing_flag                    true
% 7.15/1.51  --time_out_prep_mult                    0.1
% 7.15/1.51  --splitting_mode                        input
% 7.15/1.51  --splitting_grd                         true
% 7.15/1.51  --splitting_cvd                         false
% 7.15/1.51  --splitting_cvd_svl                     false
% 7.15/1.51  --splitting_nvd                         32
% 7.15/1.51  --sub_typing                            true
% 7.15/1.51  --prep_gs_sim                           true
% 7.15/1.51  --prep_unflatten                        true
% 7.15/1.51  --prep_res_sim                          true
% 7.15/1.51  --prep_upred                            true
% 7.15/1.51  --prep_sem_filter                       exhaustive
% 7.15/1.51  --prep_sem_filter_out                   false
% 7.15/1.51  --pred_elim                             true
% 7.15/1.51  --res_sim_input                         true
% 7.15/1.51  --eq_ax_congr_red                       true
% 7.15/1.51  --pure_diseq_elim                       true
% 7.15/1.51  --brand_transform                       false
% 7.15/1.51  --non_eq_to_eq                          false
% 7.15/1.51  --prep_def_merge                        true
% 7.15/1.51  --prep_def_merge_prop_impl              false
% 7.15/1.51  --prep_def_merge_mbd                    true
% 7.15/1.51  --prep_def_merge_tr_red                 false
% 7.15/1.51  --prep_def_merge_tr_cl                  false
% 7.15/1.51  --smt_preprocessing                     true
% 7.15/1.51  --smt_ac_axioms                         fast
% 7.15/1.51  --preprocessed_out                      false
% 7.15/1.51  --preprocessed_stats                    false
% 7.15/1.51  
% 7.15/1.51  ------ Abstraction refinement Options
% 7.15/1.51  
% 7.15/1.51  --abstr_ref                             []
% 7.15/1.51  --abstr_ref_prep                        false
% 7.15/1.51  --abstr_ref_until_sat                   false
% 7.15/1.51  --abstr_ref_sig_restrict                funpre
% 7.15/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.15/1.51  --abstr_ref_under                       []
% 7.15/1.51  
% 7.15/1.51  ------ SAT Options
% 7.15/1.51  
% 7.15/1.51  --sat_mode                              false
% 7.15/1.51  --sat_fm_restart_options                ""
% 7.15/1.51  --sat_gr_def                            false
% 7.15/1.51  --sat_epr_types                         true
% 7.15/1.51  --sat_non_cyclic_types                  false
% 7.15/1.51  --sat_finite_models                     false
% 7.15/1.51  --sat_fm_lemmas                         false
% 7.15/1.51  --sat_fm_prep                           false
% 7.15/1.51  --sat_fm_uc_incr                        true
% 7.15/1.51  --sat_out_model                         small
% 7.15/1.51  --sat_out_clauses                       false
% 7.15/1.51  
% 7.15/1.51  ------ QBF Options
% 7.15/1.51  
% 7.15/1.51  --qbf_mode                              false
% 7.15/1.51  --qbf_elim_univ                         false
% 7.15/1.51  --qbf_dom_inst                          none
% 7.15/1.51  --qbf_dom_pre_inst                      false
% 7.15/1.51  --qbf_sk_in                             false
% 7.15/1.51  --qbf_pred_elim                         true
% 7.15/1.51  --qbf_split                             512
% 7.15/1.51  
% 7.15/1.51  ------ BMC1 Options
% 7.15/1.51  
% 7.15/1.51  --bmc1_incremental                      false
% 7.15/1.51  --bmc1_axioms                           reachable_all
% 7.15/1.51  --bmc1_min_bound                        0
% 7.15/1.51  --bmc1_max_bound                        -1
% 7.15/1.51  --bmc1_max_bound_default                -1
% 7.15/1.51  --bmc1_symbol_reachability              true
% 7.15/1.51  --bmc1_property_lemmas                  false
% 7.15/1.51  --bmc1_k_induction                      false
% 7.15/1.51  --bmc1_non_equiv_states                 false
% 7.15/1.51  --bmc1_deadlock                         false
% 7.15/1.51  --bmc1_ucm                              false
% 7.15/1.51  --bmc1_add_unsat_core                   none
% 7.15/1.51  --bmc1_unsat_core_children              false
% 7.15/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.15/1.51  --bmc1_out_stat                         full
% 7.15/1.51  --bmc1_ground_init                      false
% 7.15/1.51  --bmc1_pre_inst_next_state              false
% 7.15/1.51  --bmc1_pre_inst_state                   false
% 7.15/1.51  --bmc1_pre_inst_reach_state             false
% 7.15/1.51  --bmc1_out_unsat_core                   false
% 7.15/1.51  --bmc1_aig_witness_out                  false
% 7.15/1.51  --bmc1_verbose                          false
% 7.15/1.51  --bmc1_dump_clauses_tptp                false
% 7.15/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.15/1.51  --bmc1_dump_file                        -
% 7.15/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.15/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.15/1.51  --bmc1_ucm_extend_mode                  1
% 7.15/1.51  --bmc1_ucm_init_mode                    2
% 7.15/1.51  --bmc1_ucm_cone_mode                    none
% 7.15/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.15/1.51  --bmc1_ucm_relax_model                  4
% 7.15/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.15/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.15/1.51  --bmc1_ucm_layered_model                none
% 7.15/1.51  --bmc1_ucm_max_lemma_size               10
% 7.15/1.51  
% 7.15/1.51  ------ AIG Options
% 7.15/1.51  
% 7.15/1.51  --aig_mode                              false
% 7.15/1.51  
% 7.15/1.51  ------ Instantiation Options
% 7.15/1.51  
% 7.15/1.51  --instantiation_flag                    true
% 7.15/1.51  --inst_sos_flag                         false
% 7.15/1.51  --inst_sos_phase                        true
% 7.15/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.15/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.15/1.51  --inst_lit_sel_side                     num_symb
% 7.15/1.51  --inst_solver_per_active                1400
% 7.15/1.51  --inst_solver_calls_frac                1.
% 7.15/1.51  --inst_passive_queue_type               priority_queues
% 7.15/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.15/1.51  --inst_passive_queues_freq              [25;2]
% 7.15/1.51  --inst_dismatching                      true
% 7.15/1.51  --inst_eager_unprocessed_to_passive     true
% 7.15/1.51  --inst_prop_sim_given                   true
% 7.15/1.51  --inst_prop_sim_new                     false
% 7.15/1.51  --inst_subs_new                         false
% 7.15/1.51  --inst_eq_res_simp                      false
% 7.15/1.51  --inst_subs_given                       false
% 7.15/1.51  --inst_orphan_elimination               true
% 7.15/1.51  --inst_learning_loop_flag               true
% 7.15/1.51  --inst_learning_start                   3000
% 7.15/1.51  --inst_learning_factor                  2
% 7.15/1.51  --inst_start_prop_sim_after_learn       3
% 7.15/1.51  --inst_sel_renew                        solver
% 7.15/1.51  --inst_lit_activity_flag                true
% 7.15/1.51  --inst_restr_to_given                   false
% 7.15/1.51  --inst_activity_threshold               500
% 7.15/1.51  --inst_out_proof                        true
% 7.15/1.51  
% 7.15/1.51  ------ Resolution Options
% 7.15/1.51  
% 7.15/1.51  --resolution_flag                       true
% 7.15/1.51  --res_lit_sel                           adaptive
% 7.15/1.51  --res_lit_sel_side                      none
% 7.15/1.51  --res_ordering                          kbo
% 7.15/1.51  --res_to_prop_solver                    active
% 7.15/1.51  --res_prop_simpl_new                    false
% 7.15/1.51  --res_prop_simpl_given                  true
% 7.15/1.51  --res_passive_queue_type                priority_queues
% 7.15/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.15/1.51  --res_passive_queues_freq               [15;5]
% 7.15/1.51  --res_forward_subs                      full
% 7.15/1.51  --res_backward_subs                     full
% 7.15/1.51  --res_forward_subs_resolution           true
% 7.15/1.51  --res_backward_subs_resolution          true
% 7.15/1.51  --res_orphan_elimination                true
% 7.15/1.51  --res_time_limit                        2.
% 7.15/1.51  --res_out_proof                         true
% 7.15/1.51  
% 7.15/1.51  ------ Superposition Options
% 7.15/1.51  
% 7.15/1.51  --superposition_flag                    true
% 7.15/1.51  --sup_passive_queue_type                priority_queues
% 7.15/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.15/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.15/1.51  --demod_completeness_check              fast
% 7.15/1.51  --demod_use_ground                      true
% 7.15/1.51  --sup_to_prop_solver                    passive
% 7.15/1.51  --sup_prop_simpl_new                    true
% 7.15/1.51  --sup_prop_simpl_given                  true
% 7.15/1.51  --sup_fun_splitting                     false
% 7.15/1.51  --sup_smt_interval                      50000
% 7.15/1.51  
% 7.15/1.51  ------ Superposition Simplification Setup
% 7.15/1.51  
% 7.15/1.51  --sup_indices_passive                   []
% 7.15/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.15/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.51  --sup_full_bw                           [BwDemod]
% 7.15/1.51  --sup_immed_triv                        [TrivRules]
% 7.15/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.15/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.51  --sup_immed_bw_main                     []
% 7.15/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.15/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.51  
% 7.15/1.51  ------ Combination Options
% 7.15/1.51  
% 7.15/1.51  --comb_res_mult                         3
% 7.15/1.51  --comb_sup_mult                         2
% 7.15/1.51  --comb_inst_mult                        10
% 7.15/1.51  
% 7.15/1.51  ------ Debug Options
% 7.15/1.51  
% 7.15/1.51  --dbg_backtrace                         false
% 7.15/1.51  --dbg_dump_prop_clauses                 false
% 7.15/1.51  --dbg_dump_prop_clauses_file            -
% 7.15/1.51  --dbg_out_stat                          false
% 7.15/1.51  ------ Parsing...
% 7.15/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.15/1.51  
% 7.15/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.15/1.51  
% 7.15/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.15/1.51  
% 7.15/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.15/1.51  ------ Proving...
% 7.15/1.51  ------ Problem Properties 
% 7.15/1.51  
% 7.15/1.51  
% 7.15/1.51  clauses                                 15
% 7.15/1.51  conjectures                             2
% 7.15/1.51  EPR                                     0
% 7.15/1.51  Horn                                    13
% 7.15/1.51  unary                                   4
% 7.15/1.51  binary                                  9
% 7.15/1.51  lits                                    28
% 7.15/1.51  lits eq                                 10
% 7.15/1.51  fd_pure                                 0
% 7.15/1.51  fd_pseudo                               0
% 7.15/1.51  fd_cond                                 0
% 7.15/1.51  fd_pseudo_cond                          2
% 7.15/1.51  AC symbols                              0
% 7.15/1.51  
% 7.15/1.51  ------ Schedule dynamic 5 is on 
% 7.15/1.51  
% 7.15/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.15/1.51  
% 7.15/1.51  
% 7.15/1.51  ------ 
% 7.15/1.51  Current options:
% 7.15/1.51  ------ 
% 7.15/1.51  
% 7.15/1.51  ------ Input Options
% 7.15/1.51  
% 7.15/1.51  --out_options                           all
% 7.15/1.51  --tptp_safe_out                         true
% 7.15/1.51  --problem_path                          ""
% 7.15/1.51  --include_path                          ""
% 7.15/1.51  --clausifier                            res/vclausify_rel
% 7.15/1.51  --clausifier_options                    --mode clausify
% 7.15/1.51  --stdin                                 false
% 7.15/1.51  --stats_out                             all
% 7.15/1.51  
% 7.15/1.51  ------ General Options
% 7.15/1.51  
% 7.15/1.51  --fof                                   false
% 7.15/1.51  --time_out_real                         305.
% 7.15/1.51  --time_out_virtual                      -1.
% 7.15/1.51  --symbol_type_check                     false
% 7.15/1.51  --clausify_out                          false
% 7.15/1.51  --sig_cnt_out                           false
% 7.15/1.51  --trig_cnt_out                          false
% 7.15/1.51  --trig_cnt_out_tolerance                1.
% 7.15/1.51  --trig_cnt_out_sk_spl                   false
% 7.15/1.51  --abstr_cl_out                          false
% 7.15/1.51  
% 7.15/1.51  ------ Global Options
% 7.15/1.51  
% 7.15/1.51  --schedule                              default
% 7.15/1.51  --add_important_lit                     false
% 7.15/1.51  --prop_solver_per_cl                    1000
% 7.15/1.51  --min_unsat_core                        false
% 7.15/1.51  --soft_assumptions                      false
% 7.15/1.51  --soft_lemma_size                       3
% 7.15/1.51  --prop_impl_unit_size                   0
% 7.15/1.51  --prop_impl_unit                        []
% 7.15/1.51  --share_sel_clauses                     true
% 7.15/1.51  --reset_solvers                         false
% 7.15/1.51  --bc_imp_inh                            [conj_cone]
% 7.15/1.51  --conj_cone_tolerance                   3.
% 7.15/1.51  --extra_neg_conj                        none
% 7.15/1.51  --large_theory_mode                     true
% 7.15/1.51  --prolific_symb_bound                   200
% 7.15/1.51  --lt_threshold                          2000
% 7.15/1.51  --clause_weak_htbl                      true
% 7.15/1.51  --gc_record_bc_elim                     false
% 7.15/1.51  
% 7.15/1.51  ------ Preprocessing Options
% 7.15/1.51  
% 7.15/1.51  --preprocessing_flag                    true
% 7.15/1.51  --time_out_prep_mult                    0.1
% 7.15/1.51  --splitting_mode                        input
% 7.15/1.51  --splitting_grd                         true
% 7.15/1.51  --splitting_cvd                         false
% 7.15/1.51  --splitting_cvd_svl                     false
% 7.15/1.51  --splitting_nvd                         32
% 7.15/1.51  --sub_typing                            true
% 7.15/1.51  --prep_gs_sim                           true
% 7.15/1.51  --prep_unflatten                        true
% 7.15/1.51  --prep_res_sim                          true
% 7.15/1.51  --prep_upred                            true
% 7.15/1.51  --prep_sem_filter                       exhaustive
% 7.15/1.51  --prep_sem_filter_out                   false
% 7.15/1.51  --pred_elim                             true
% 7.15/1.51  --res_sim_input                         true
% 7.15/1.51  --eq_ax_congr_red                       true
% 7.15/1.51  --pure_diseq_elim                       true
% 7.15/1.51  --brand_transform                       false
% 7.15/1.51  --non_eq_to_eq                          false
% 7.15/1.51  --prep_def_merge                        true
% 7.15/1.51  --prep_def_merge_prop_impl              false
% 7.15/1.51  --prep_def_merge_mbd                    true
% 7.15/1.51  --prep_def_merge_tr_red                 false
% 7.15/1.51  --prep_def_merge_tr_cl                  false
% 7.15/1.51  --smt_preprocessing                     true
% 7.15/1.51  --smt_ac_axioms                         fast
% 7.15/1.51  --preprocessed_out                      false
% 7.15/1.51  --preprocessed_stats                    false
% 7.15/1.51  
% 7.15/1.51  ------ Abstraction refinement Options
% 7.15/1.51  
% 7.15/1.51  --abstr_ref                             []
% 7.15/1.51  --abstr_ref_prep                        false
% 7.15/1.51  --abstr_ref_until_sat                   false
% 7.15/1.51  --abstr_ref_sig_restrict                funpre
% 7.15/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.15/1.51  --abstr_ref_under                       []
% 7.15/1.51  
% 7.15/1.51  ------ SAT Options
% 7.15/1.51  
% 7.15/1.51  --sat_mode                              false
% 7.15/1.51  --sat_fm_restart_options                ""
% 7.15/1.51  --sat_gr_def                            false
% 7.15/1.51  --sat_epr_types                         true
% 7.15/1.51  --sat_non_cyclic_types                  false
% 7.15/1.51  --sat_finite_models                     false
% 7.15/1.51  --sat_fm_lemmas                         false
% 7.15/1.51  --sat_fm_prep                           false
% 7.15/1.51  --sat_fm_uc_incr                        true
% 7.15/1.51  --sat_out_model                         small
% 7.15/1.51  --sat_out_clauses                       false
% 7.15/1.51  
% 7.15/1.51  ------ QBF Options
% 7.15/1.51  
% 7.15/1.51  --qbf_mode                              false
% 7.15/1.51  --qbf_elim_univ                         false
% 7.15/1.51  --qbf_dom_inst                          none
% 7.15/1.51  --qbf_dom_pre_inst                      false
% 7.15/1.51  --qbf_sk_in                             false
% 7.15/1.51  --qbf_pred_elim                         true
% 7.15/1.51  --qbf_split                             512
% 7.15/1.51  
% 7.15/1.51  ------ BMC1 Options
% 7.15/1.51  
% 7.15/1.51  --bmc1_incremental                      false
% 7.15/1.51  --bmc1_axioms                           reachable_all
% 7.15/1.51  --bmc1_min_bound                        0
% 7.15/1.51  --bmc1_max_bound                        -1
% 7.15/1.51  --bmc1_max_bound_default                -1
% 7.15/1.51  --bmc1_symbol_reachability              true
% 7.15/1.51  --bmc1_property_lemmas                  false
% 7.15/1.51  --bmc1_k_induction                      false
% 7.15/1.51  --bmc1_non_equiv_states                 false
% 7.15/1.51  --bmc1_deadlock                         false
% 7.15/1.51  --bmc1_ucm                              false
% 7.15/1.51  --bmc1_add_unsat_core                   none
% 7.15/1.51  --bmc1_unsat_core_children              false
% 7.15/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.15/1.51  --bmc1_out_stat                         full
% 7.15/1.51  --bmc1_ground_init                      false
% 7.15/1.51  --bmc1_pre_inst_next_state              false
% 7.15/1.51  --bmc1_pre_inst_state                   false
% 7.15/1.51  --bmc1_pre_inst_reach_state             false
% 7.15/1.51  --bmc1_out_unsat_core                   false
% 7.15/1.51  --bmc1_aig_witness_out                  false
% 7.15/1.51  --bmc1_verbose                          false
% 7.15/1.51  --bmc1_dump_clauses_tptp                false
% 7.15/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.15/1.51  --bmc1_dump_file                        -
% 7.15/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.15/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.15/1.51  --bmc1_ucm_extend_mode                  1
% 7.15/1.51  --bmc1_ucm_init_mode                    2
% 7.15/1.51  --bmc1_ucm_cone_mode                    none
% 7.15/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.15/1.51  --bmc1_ucm_relax_model                  4
% 7.15/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.15/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.15/1.51  --bmc1_ucm_layered_model                none
% 7.15/1.51  --bmc1_ucm_max_lemma_size               10
% 7.15/1.51  
% 7.15/1.51  ------ AIG Options
% 7.15/1.51  
% 7.15/1.51  --aig_mode                              false
% 7.15/1.51  
% 7.15/1.51  ------ Instantiation Options
% 7.15/1.51  
% 7.15/1.51  --instantiation_flag                    true
% 7.15/1.51  --inst_sos_flag                         false
% 7.15/1.51  --inst_sos_phase                        true
% 7.15/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.15/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.15/1.51  --inst_lit_sel_side                     none
% 7.15/1.51  --inst_solver_per_active                1400
% 7.15/1.51  --inst_solver_calls_frac                1.
% 7.15/1.51  --inst_passive_queue_type               priority_queues
% 7.15/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.15/1.51  --inst_passive_queues_freq              [25;2]
% 7.15/1.51  --inst_dismatching                      true
% 7.15/1.51  --inst_eager_unprocessed_to_passive     true
% 7.15/1.51  --inst_prop_sim_given                   true
% 7.15/1.51  --inst_prop_sim_new                     false
% 7.15/1.51  --inst_subs_new                         false
% 7.15/1.51  --inst_eq_res_simp                      false
% 7.15/1.51  --inst_subs_given                       false
% 7.15/1.51  --inst_orphan_elimination               true
% 7.15/1.51  --inst_learning_loop_flag               true
% 7.15/1.51  --inst_learning_start                   3000
% 7.15/1.51  --inst_learning_factor                  2
% 7.15/1.51  --inst_start_prop_sim_after_learn       3
% 7.15/1.51  --inst_sel_renew                        solver
% 7.15/1.51  --inst_lit_activity_flag                true
% 7.15/1.51  --inst_restr_to_given                   false
% 7.15/1.51  --inst_activity_threshold               500
% 7.15/1.51  --inst_out_proof                        true
% 7.15/1.51  
% 7.15/1.51  ------ Resolution Options
% 7.15/1.51  
% 7.15/1.51  --resolution_flag                       false
% 7.15/1.51  --res_lit_sel                           adaptive
% 7.15/1.51  --res_lit_sel_side                      none
% 7.15/1.51  --res_ordering                          kbo
% 7.15/1.51  --res_to_prop_solver                    active
% 7.15/1.51  --res_prop_simpl_new                    false
% 7.15/1.51  --res_prop_simpl_given                  true
% 7.15/1.51  --res_passive_queue_type                priority_queues
% 7.15/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.15/1.51  --res_passive_queues_freq               [15;5]
% 7.15/1.51  --res_forward_subs                      full
% 7.15/1.51  --res_backward_subs                     full
% 7.15/1.51  --res_forward_subs_resolution           true
% 7.15/1.51  --res_backward_subs_resolution          true
% 7.15/1.51  --res_orphan_elimination                true
% 7.15/1.51  --res_time_limit                        2.
% 7.15/1.51  --res_out_proof                         true
% 7.15/1.51  
% 7.15/1.51  ------ Superposition Options
% 7.15/1.51  
% 7.15/1.51  --superposition_flag                    true
% 7.15/1.51  --sup_passive_queue_type                priority_queues
% 7.15/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.15/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.15/1.51  --demod_completeness_check              fast
% 7.15/1.51  --demod_use_ground                      true
% 7.15/1.51  --sup_to_prop_solver                    passive
% 7.15/1.51  --sup_prop_simpl_new                    true
% 7.15/1.51  --sup_prop_simpl_given                  true
% 7.15/1.51  --sup_fun_splitting                     false
% 7.15/1.51  --sup_smt_interval                      50000
% 7.15/1.51  
% 7.15/1.51  ------ Superposition Simplification Setup
% 7.15/1.51  
% 7.15/1.51  --sup_indices_passive                   []
% 7.15/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.15/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.51  --sup_full_bw                           [BwDemod]
% 7.15/1.51  --sup_immed_triv                        [TrivRules]
% 7.15/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.15/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.51  --sup_immed_bw_main                     []
% 7.15/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.15/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.51  
% 7.15/1.51  ------ Combination Options
% 7.15/1.51  
% 7.15/1.51  --comb_res_mult                         3
% 7.15/1.51  --comb_sup_mult                         2
% 7.15/1.51  --comb_inst_mult                        10
% 7.15/1.51  
% 7.15/1.51  ------ Debug Options
% 7.15/1.51  
% 7.15/1.51  --dbg_backtrace                         false
% 7.15/1.51  --dbg_dump_prop_clauses                 false
% 7.15/1.51  --dbg_dump_prop_clauses_file            -
% 7.15/1.51  --dbg_out_stat                          false
% 7.15/1.51  
% 7.15/1.51  
% 7.15/1.51  
% 7.15/1.51  
% 7.15/1.51  ------ Proving...
% 7.15/1.51  
% 7.15/1.51  
% 7.15/1.51  % SZS status Theorem for theBenchmark.p
% 7.15/1.51  
% 7.15/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.15/1.51  
% 7.15/1.51  fof(f8,axiom,(
% 7.15/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.15/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.51  
% 7.15/1.51  fof(f15,plain,(
% 7.15/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.15/1.51    inference(ennf_transformation,[],[f8])).
% 7.15/1.51  
% 7.15/1.51  fof(f40,plain,(
% 7.15/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.15/1.51    inference(cnf_transformation,[],[f15])).
% 7.15/1.51  
% 7.15/1.51  fof(f10,conjecture,(
% 7.15/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.15/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.51  
% 7.15/1.51  fof(f11,negated_conjecture,(
% 7.15/1.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.15/1.51    inference(negated_conjecture,[],[f10])).
% 7.15/1.51  
% 7.15/1.51  fof(f16,plain,(
% 7.15/1.51    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.15/1.51    inference(ennf_transformation,[],[f11])).
% 7.15/1.51  
% 7.15/1.51  fof(f22,plain,(
% 7.15/1.51    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.15/1.51    inference(nnf_transformation,[],[f16])).
% 7.15/1.51  
% 7.15/1.51  fof(f23,plain,(
% 7.15/1.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.15/1.51    inference(flattening,[],[f22])).
% 7.15/1.51  
% 7.15/1.51  fof(f25,plain,(
% 7.15/1.51    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 7.15/1.51    introduced(choice_axiom,[])).
% 7.15/1.51  
% 7.15/1.51  fof(f24,plain,(
% 7.15/1.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 7.15/1.51    introduced(choice_axiom,[])).
% 7.15/1.51  
% 7.15/1.51  fof(f26,plain,(
% 7.15/1.51    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.15/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f25,f24])).
% 7.15/1.51  
% 7.15/1.51  fof(f43,plain,(
% 7.15/1.51    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.15/1.51    inference(cnf_transformation,[],[f26])).
% 7.15/1.51  
% 7.15/1.51  fof(f44,plain,(
% 7.15/1.51    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 7.15/1.51    inference(cnf_transformation,[],[f26])).
% 7.15/1.51  
% 7.15/1.51  fof(f45,plain,(
% 7.15/1.51    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 7.15/1.51    inference(cnf_transformation,[],[f26])).
% 7.15/1.51  
% 7.15/1.51  fof(f42,plain,(
% 7.15/1.51    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.15/1.51    inference(cnf_transformation,[],[f26])).
% 7.15/1.51  
% 7.15/1.51  fof(f4,axiom,(
% 7.15/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 7.15/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.51  
% 7.15/1.51  fof(f13,plain,(
% 7.15/1.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 7.15/1.51    inference(ennf_transformation,[],[f4])).
% 7.15/1.51  
% 7.15/1.51  fof(f30,plain,(
% 7.15/1.51    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 7.15/1.51    inference(cnf_transformation,[],[f13])).
% 7.15/1.51  
% 7.15/1.51  fof(f7,axiom,(
% 7.15/1.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.15/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.51  
% 7.15/1.51  fof(f14,plain,(
% 7.15/1.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.15/1.51    inference(ennf_transformation,[],[f7])).
% 7.15/1.51  
% 7.15/1.51  fof(f21,plain,(
% 7.15/1.51    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.15/1.51    inference(nnf_transformation,[],[f14])).
% 7.15/1.51  
% 7.15/1.51  fof(f36,plain,(
% 7.15/1.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.15/1.51    inference(cnf_transformation,[],[f21])).
% 7.15/1.51  
% 7.15/1.51  fof(f9,axiom,(
% 7.15/1.51    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.15/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.51  
% 7.15/1.51  fof(f41,plain,(
% 7.15/1.51    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.15/1.51    inference(cnf_transformation,[],[f9])).
% 7.15/1.51  
% 7.15/1.51  fof(f6,axiom,(
% 7.15/1.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.15/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.51  
% 7.15/1.51  fof(f17,plain,(
% 7.15/1.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.15/1.51    inference(nnf_transformation,[],[f6])).
% 7.15/1.51  
% 7.15/1.51  fof(f18,plain,(
% 7.15/1.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.15/1.51    inference(rectify,[],[f17])).
% 7.15/1.51  
% 7.15/1.51  fof(f19,plain,(
% 7.15/1.51    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.15/1.51    introduced(choice_axiom,[])).
% 7.15/1.51  
% 7.15/1.51  fof(f20,plain,(
% 7.15/1.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.15/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 7.15/1.51  
% 7.15/1.51  fof(f32,plain,(
% 7.15/1.51    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.15/1.51    inference(cnf_transformation,[],[f20])).
% 7.15/1.51  
% 7.15/1.51  fof(f50,plain,(
% 7.15/1.51    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.15/1.51    inference(equality_resolution,[],[f32])).
% 7.15/1.51  
% 7.15/1.51  fof(f3,axiom,(
% 7.15/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.15/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.51  
% 7.15/1.51  fof(f12,plain,(
% 7.15/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.15/1.51    inference(ennf_transformation,[],[f3])).
% 7.15/1.51  
% 7.15/1.51  fof(f29,plain,(
% 7.15/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.15/1.51    inference(cnf_transformation,[],[f12])).
% 7.15/1.51  
% 7.15/1.51  fof(f5,axiom,(
% 7.15/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.15/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.51  
% 7.15/1.51  fof(f31,plain,(
% 7.15/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.15/1.51    inference(cnf_transformation,[],[f5])).
% 7.15/1.51  
% 7.15/1.51  fof(f48,plain,(
% 7.15/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.15/1.51    inference(definition_unfolding,[],[f29,f31])).
% 7.15/1.51  
% 7.15/1.51  fof(f1,axiom,(
% 7.15/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.15/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.51  
% 7.15/1.51  fof(f27,plain,(
% 7.15/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.15/1.51    inference(cnf_transformation,[],[f1])).
% 7.15/1.51  
% 7.15/1.51  fof(f47,plain,(
% 7.15/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.15/1.51    inference(definition_unfolding,[],[f27,f31,f31])).
% 7.15/1.51  
% 7.15/1.51  cnf(c_12,plain,
% 7.15/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.15/1.51      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.15/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_16,negated_conjecture,
% 7.15/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.15/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_412,plain,
% 7.15/1.51      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.15/1.51      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 7.15/1.51      | sK3 != X1 ),
% 7.15/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_413,plain,
% 7.15/1.51      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 7.15/1.51      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.15/1.51      inference(unflattening,[status(thm)],[c_412]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1191,plain,
% 7.15/1.51      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 7.15/1.51      inference(equality_resolution,[status(thm)],[c_413]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_15,negated_conjecture,
% 7.15/1.51      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.15/1.51      | r1_tarski(sK2,sK3) ),
% 7.15/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1089,plain,
% 7.15/1.51      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 7.15/1.51      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.15/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1351,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 7.15/1.51      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.15/1.51      inference(demodulation,[status(thm)],[c_1191,c_1089]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_14,negated_conjecture,
% 7.15/1.51      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.15/1.51      | ~ r1_tarski(sK2,sK3) ),
% 7.15/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1090,plain,
% 7.15/1.51      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 7.15/1.51      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.15/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1352,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 7.15/1.51      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.15/1.51      inference(demodulation,[status(thm)],[c_1191,c_1090]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_17,negated_conjecture,
% 7.15/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.15/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_421,plain,
% 7.15/1.51      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.15/1.51      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 7.15/1.51      | sK2 != X1 ),
% 7.15/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_422,plain,
% 7.15/1.51      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 7.15/1.51      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.15/1.51      inference(unflattening,[status(thm)],[c_421]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1194,plain,
% 7.15/1.51      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 7.15/1.51      inference(equality_resolution,[status(thm)],[c_422]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1691,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 7.15/1.51      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.15/1.51      inference(light_normalisation,[status(thm)],[c_1352,c_1194]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_3,plain,
% 7.15/1.51      ( ~ r1_tarski(X0,X1)
% 7.15/1.51      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 7.15/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1261,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2))
% 7.15/1.51      | ~ r1_tarski(sK2,sK3) ),
% 7.15/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1268,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2)) = iProver_top
% 7.15/1.51      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.15/1.51      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1270,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 7.15/1.51      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.15/1.51      inference(instantiation,[status(thm)],[c_1268]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1695,plain,
% 7.15/1.51      ( r1_tarski(sK2,sK3) != iProver_top ),
% 7.15/1.51      inference(global_propositional_subsumption,
% 7.15/1.51                [status(thm)],
% 7.15/1.51                [c_1691,c_1270]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1795,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top ),
% 7.15/1.51      inference(global_propositional_subsumption,
% 7.15/1.51                [status(thm)],
% 7.15/1.51                [c_1351,c_1270,c_1691]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1799,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 7.15/1.51      inference(light_normalisation,[status(thm)],[c_1795,c_1194]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_11,plain,
% 7.15/1.51      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.15/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_376,plain,
% 7.15/1.51      ( r2_hidden(X0,X1)
% 7.15/1.51      | v1_xboole_0(X1)
% 7.15/1.51      | k1_zfmisc_1(sK1) != X1
% 7.15/1.51      | sK3 != X0 ),
% 7.15/1.51      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_377,plain,
% 7.15/1.51      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.15/1.51      inference(unflattening,[status(thm)],[c_376]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_13,plain,
% 7.15/1.51      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.15/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_23,plain,
% 7.15/1.51      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.15/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_379,plain,
% 7.15/1.51      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 7.15/1.51      inference(global_propositional_subsumption,
% 7.15/1.51                [status(thm)],
% 7.15/1.51                [c_377,c_23]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1088,plain,
% 7.15/1.51      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.15/1.51      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_7,plain,
% 7.15/1.51      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.15/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1091,plain,
% 7.15/1.51      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.15/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.15/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1682,plain,
% 7.15/1.51      ( r1_tarski(sK3,sK1) = iProver_top ),
% 7.15/1.51      inference(superposition,[status(thm)],[c_1088,c_1091]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_2,plain,
% 7.15/1.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.15/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1096,plain,
% 7.15/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.15/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.15/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_2042,plain,
% 7.15/1.51      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
% 7.15/1.51      inference(superposition,[status(thm)],[c_1682,c_1096]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1,plain,
% 7.15/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.15/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_2299,plain,
% 7.15/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
% 7.15/1.51      inference(superposition,[status(thm)],[c_2042,c_1]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1095,plain,
% 7.15/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.15/1.51      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 7.15/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_2594,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(sK1,X0),sK3) = iProver_top
% 7.15/1.51      | r1_tarski(k4_xboole_0(sK1,sK3),X0) != iProver_top ),
% 7.15/1.51      inference(superposition,[status(thm)],[c_2299,c_1095]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_31635,plain,
% 7.15/1.51      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
% 7.15/1.51      inference(superposition,[status(thm)],[c_1799,c_2594]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_394,plain,
% 7.15/1.51      ( r2_hidden(X0,X1)
% 7.15/1.51      | v1_xboole_0(X1)
% 7.15/1.51      | k1_zfmisc_1(sK1) != X1
% 7.15/1.51      | sK2 != X0 ),
% 7.15/1.51      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_395,plain,
% 7.15/1.51      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.15/1.51      inference(unflattening,[status(thm)],[c_394]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_397,plain,
% 7.15/1.51      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 7.15/1.51      inference(global_propositional_subsumption,
% 7.15/1.51                [status(thm)],
% 7.15/1.51                [c_395,c_23]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1087,plain,
% 7.15/1.51      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.15/1.51      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_1683,plain,
% 7.15/1.51      ( r1_tarski(sK2,sK1) = iProver_top ),
% 7.15/1.51      inference(superposition,[status(thm)],[c_1087,c_1091]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_2043,plain,
% 7.15/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
% 7.15/1.51      inference(superposition,[status(thm)],[c_1683,c_1096]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_2352,plain,
% 7.15/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 7.15/1.51      inference(superposition,[status(thm)],[c_2043,c_1]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(c_31657,plain,
% 7.15/1.51      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.15/1.51      inference(light_normalisation,[status(thm)],[c_31635,c_2352]) ).
% 7.15/1.51  
% 7.15/1.51  cnf(contradiction,plain,
% 7.15/1.51      ( $false ),
% 7.15/1.51      inference(minisat,[status(thm)],[c_31657,c_1695]) ).
% 7.15/1.51  
% 7.15/1.51  
% 7.15/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.15/1.51  
% 7.15/1.51  ------                               Statistics
% 7.15/1.51  
% 7.15/1.51  ------ General
% 7.15/1.51  
% 7.15/1.51  abstr_ref_over_cycles:                  0
% 7.15/1.51  abstr_ref_under_cycles:                 0
% 7.15/1.51  gc_basic_clause_elim:                   0
% 7.15/1.51  forced_gc_time:                         0
% 7.15/1.51  parsing_time:                           0.01
% 7.15/1.51  unif_index_cands_time:                  0.
% 7.15/1.51  unif_index_add_time:                    0.
% 7.15/1.51  orderings_time:                         0.
% 7.15/1.51  out_proof_time:                         0.011
% 7.15/1.51  total_time:                             1.002
% 7.15/1.51  num_of_symbols:                         43
% 7.15/1.51  num_of_terms:                           38253
% 7.15/1.51  
% 7.15/1.51  ------ Preprocessing
% 7.15/1.51  
% 7.15/1.51  num_of_splits:                          0
% 7.15/1.51  num_of_split_atoms:                     0
% 7.15/1.51  num_of_reused_defs:                     0
% 7.15/1.51  num_eq_ax_congr_red:                    12
% 7.15/1.51  num_of_sem_filtered_clauses:            1
% 7.15/1.51  num_of_subtypes:                        0
% 7.15/1.51  monotx_restored_types:                  0
% 7.15/1.51  sat_num_of_epr_types:                   0
% 7.15/1.51  sat_num_of_non_cyclic_types:            0
% 7.15/1.51  sat_guarded_non_collapsed_types:        0
% 7.15/1.51  num_pure_diseq_elim:                    0
% 7.15/1.51  simp_replaced_by:                       0
% 7.15/1.51  res_preprocessed:                       80
% 7.15/1.51  prep_upred:                             0
% 7.15/1.51  prep_unflattend:                        46
% 7.15/1.51  smt_new_axioms:                         0
% 7.15/1.51  pred_elim_cands:                        2
% 7.15/1.51  pred_elim:                              2
% 7.15/1.51  pred_elim_cl:                           3
% 7.15/1.51  pred_elim_cycles:                       5
% 7.15/1.51  merged_defs:                            16
% 7.15/1.51  merged_defs_ncl:                        0
% 7.15/1.51  bin_hyper_res:                          17
% 7.15/1.51  prep_cycles:                            4
% 7.15/1.51  pred_elim_time:                         0.009
% 7.15/1.51  splitting_time:                         0.
% 7.15/1.51  sem_filter_time:                        0.
% 7.15/1.51  monotx_time:                            0.001
% 7.15/1.51  subtype_inf_time:                       0.
% 7.15/1.51  
% 7.15/1.51  ------ Problem properties
% 7.15/1.51  
% 7.15/1.51  clauses:                                15
% 7.15/1.51  conjectures:                            2
% 7.15/1.51  epr:                                    0
% 7.15/1.51  horn:                                   13
% 7.15/1.51  ground:                                 4
% 7.15/1.51  unary:                                  4
% 7.15/1.51  binary:                                 9
% 7.15/1.51  lits:                                   28
% 7.15/1.51  lits_eq:                                10
% 7.15/1.51  fd_pure:                                0
% 7.15/1.51  fd_pseudo:                              0
% 7.15/1.51  fd_cond:                                0
% 7.15/1.51  fd_pseudo_cond:                         2
% 7.15/1.51  ac_symbols:                             0
% 7.15/1.51  
% 7.15/1.51  ------ Propositional Solver
% 7.15/1.51  
% 7.15/1.51  prop_solver_calls:                      31
% 7.15/1.51  prop_fast_solver_calls:                 811
% 7.15/1.51  smt_solver_calls:                       0
% 7.15/1.51  smt_fast_solver_calls:                  0
% 7.15/1.51  prop_num_of_clauses:                    12786
% 7.15/1.51  prop_preprocess_simplified:             24173
% 7.15/1.51  prop_fo_subsumed:                       9
% 7.15/1.51  prop_solver_time:                       0.
% 7.15/1.51  smt_solver_time:                        0.
% 7.15/1.51  smt_fast_solver_time:                   0.
% 7.15/1.51  prop_fast_solver_time:                  0.
% 7.15/1.51  prop_unsat_core_time:                   0.001
% 7.15/1.51  
% 7.15/1.51  ------ QBF
% 7.15/1.51  
% 7.15/1.51  qbf_q_res:                              0
% 7.15/1.51  qbf_num_tautologies:                    0
% 7.15/1.51  qbf_prep_cycles:                        0
% 7.15/1.51  
% 7.15/1.51  ------ BMC1
% 7.15/1.51  
% 7.15/1.51  bmc1_current_bound:                     -1
% 7.15/1.51  bmc1_last_solved_bound:                 -1
% 7.15/1.51  bmc1_unsat_core_size:                   -1
% 7.15/1.51  bmc1_unsat_core_parents_size:           -1
% 7.15/1.51  bmc1_merge_next_fun:                    0
% 7.15/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.15/1.51  
% 7.15/1.51  ------ Instantiation
% 7.15/1.51  
% 7.15/1.51  inst_num_of_clauses:                    3354
% 7.15/1.51  inst_num_in_passive:                    2269
% 7.15/1.51  inst_num_in_active:                     1039
% 7.15/1.51  inst_num_in_unprocessed:                46
% 7.15/1.51  inst_num_of_loops:                      1140
% 7.15/1.51  inst_num_of_learning_restarts:          0
% 7.15/1.51  inst_num_moves_active_passive:          98
% 7.15/1.51  inst_lit_activity:                      0
% 7.15/1.51  inst_lit_activity_moves:                1
% 7.15/1.51  inst_num_tautologies:                   0
% 7.15/1.51  inst_num_prop_implied:                  0
% 7.15/1.51  inst_num_existing_simplified:           0
% 7.15/1.51  inst_num_eq_res_simplified:             0
% 7.15/1.51  inst_num_child_elim:                    0
% 7.15/1.51  inst_num_of_dismatching_blockings:      1827
% 7.15/1.51  inst_num_of_non_proper_insts:           2748
% 7.15/1.51  inst_num_of_duplicates:                 0
% 7.15/1.51  inst_inst_num_from_inst_to_res:         0
% 7.15/1.51  inst_dismatching_checking_time:         0.
% 7.15/1.51  
% 7.15/1.51  ------ Resolution
% 7.15/1.51  
% 7.15/1.51  res_num_of_clauses:                     0
% 7.15/1.51  res_num_in_passive:                     0
% 7.15/1.51  res_num_in_active:                      0
% 7.15/1.51  res_num_of_loops:                       84
% 7.15/1.51  res_forward_subset_subsumed:            177
% 7.15/1.51  res_backward_subset_subsumed:           8
% 7.15/1.51  res_forward_subsumed:                   3
% 7.15/1.51  res_backward_subsumed:                  0
% 7.15/1.51  res_forward_subsumption_resolution:     2
% 7.15/1.51  res_backward_subsumption_resolution:    0
% 7.15/1.51  res_clause_to_clause_subsumption:       12031
% 7.15/1.51  res_orphan_elimination:                 0
% 7.15/1.51  res_tautology_del:                      292
% 7.15/1.51  res_num_eq_res_simplified:              0
% 7.15/1.51  res_num_sel_changes:                    0
% 7.15/1.51  res_moves_from_active_to_pass:          0
% 7.15/1.51  
% 7.15/1.51  ------ Superposition
% 7.15/1.51  
% 7.15/1.51  sup_time_total:                         0.
% 7.15/1.51  sup_time_generating:                    0.
% 7.15/1.51  sup_time_sim_full:                      0.
% 7.15/1.51  sup_time_sim_immed:                     0.
% 7.15/1.51  
% 7.15/1.51  sup_num_of_clauses:                     1353
% 7.15/1.51  sup_num_in_active:                      210
% 7.15/1.51  sup_num_in_passive:                     1143
% 7.15/1.51  sup_num_of_loops:                       226
% 7.15/1.51  sup_fw_superposition:                   1932
% 7.15/1.51  sup_bw_superposition:                   801
% 7.15/1.51  sup_immediate_simplified:               873
% 7.15/1.51  sup_given_eliminated:                   3
% 7.15/1.51  comparisons_done:                       0
% 7.15/1.51  comparisons_avoided:                    4
% 7.15/1.51  
% 7.15/1.51  ------ Simplifications
% 7.15/1.51  
% 7.15/1.51  
% 7.15/1.51  sim_fw_subset_subsumed:                 2
% 7.15/1.51  sim_bw_subset_subsumed:                 4
% 7.15/1.51  sim_fw_subsumed:                        251
% 7.15/1.51  sim_bw_subsumed:                        16
% 7.15/1.51  sim_fw_subsumption_res:                 0
% 7.15/1.51  sim_bw_subsumption_res:                 0
% 7.15/1.51  sim_tautology_del:                      3
% 7.15/1.51  sim_eq_tautology_del:                   58
% 7.15/1.51  sim_eq_res_simp:                        0
% 7.15/1.51  sim_fw_demodulated:                     113
% 7.15/1.51  sim_bw_demodulated:                     82
% 7.15/1.51  sim_light_normalised:                   656
% 7.15/1.51  sim_joinable_taut:                      0
% 7.15/1.51  sim_joinable_simp:                      0
% 7.15/1.51  sim_ac_normalised:                      0
% 7.15/1.51  sim_smt_subsumption:                    0
% 7.15/1.51  
%------------------------------------------------------------------------------
