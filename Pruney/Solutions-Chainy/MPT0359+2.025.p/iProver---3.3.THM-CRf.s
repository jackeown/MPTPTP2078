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
% DateTime   : Thu Dec  3 11:40:05 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 225 expanded)
%              Number of clauses        :   70 (  96 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :   18
%              Number of atoms          :  316 ( 695 expanded)
%              Number of equality atoms :  161 ( 294 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,
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

fof(f30,plain,
    ( ( k2_subset_1(sK1) != sK2
      | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & ( k2_subset_1(sK1) = sK2
      | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f39,f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,
    ( k2_subset_1(sK1) != sK2
    | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_481,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_481])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_300,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_301,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_307,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_301,c_19])).

cnf(c_613,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_482,c_307])).

cnf(c_614,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_1086,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_1263,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1086])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1095,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1963,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1263,c_1095])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1093,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1658,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1093])).

cnf(c_2641,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1963,c_1658])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2653,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2641,c_7])).

cnf(c_769,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1622,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_2580,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_2581,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2580])).

cnf(c_771,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2517,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,X2)
    | X2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_2518,plain,
    ( X0 != X1
    | sK1 != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2517])).

cnf(c_2520,plain,
    ( sK2 != sK2
    | sK1 != sK2
    | r1_tarski(sK2,sK2) != iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2518])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2511,plain,
    ( r1_tarski(sK1,X0)
    | k4_xboole_0(sK1,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2512,plain,
    ( k4_xboole_0(sK1,X0) != k1_xboole_0
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2511])).

cnf(c_2514,plain,
    ( k4_xboole_0(sK1,sK2) != k1_xboole_0
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2512])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1097,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2277,plain,
    ( sK2 = sK1
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1097])).

cnf(c_1899,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1904,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1899])).

cnf(c_1506,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(sK1,sK2),X2)
    | X2 != X1
    | k4_xboole_0(sK1,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1898,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),X0)
    | ~ r1_tarski(k1_xboole_0,X1)
    | X0 != X1
    | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_1900,plain,
    ( X0 != X1
    | k4_xboole_0(sK1,sK2) != k1_xboole_0
    | r1_tarski(k4_xboole_0(sK1,sK2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1898])).

cnf(c_1902,plain,
    ( k4_xboole_0(sK1,sK2) != k1_xboole_0
    | sK2 != sK2
    | r1_tarski(k4_xboole_0(sK1,sK2),sK2) = iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1900])).

cnf(c_8,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1094,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1782,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1094])).

cnf(c_1799,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_768,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1621,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) = sK2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1091,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1112,plain,
    ( sK2 = sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1091,c_17])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_313,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_314,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_1193,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_314])).

cnf(c_1224,plain,
    ( sK2 = sK1
    | r1_tarski(k4_xboole_0(sK1,sK2),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1112,c_1193])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1092,plain,
    ( k2_subset_1(sK1) != sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1137,plain,
    ( sK2 != sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1092,c_17])).

cnf(c_1219,plain,
    ( sK2 != sK1
    | r1_tarski(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1137,c_1193])).

cnf(c_71,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_67,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_64,plain,
    ( ~ r1_tarski(sK2,sK2)
    | k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_60,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_62,plain,
    ( k4_xboole_0(sK2,sK2) != k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2653,c_2581,c_2520,c_2514,c_2277,c_1904,c_1902,c_1799,c_1621,c_1224,c_1219,c_71,c_67,c_64,c_62])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.82/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.82/1.05  
% 0.82/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.82/1.05  
% 0.82/1.05  ------  iProver source info
% 0.82/1.05  
% 0.82/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.82/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.82/1.05  git: non_committed_changes: false
% 0.82/1.05  git: last_make_outside_of_git: false
% 0.82/1.05  
% 0.82/1.05  ------ 
% 0.82/1.05  
% 0.82/1.05  ------ Input Options
% 0.82/1.05  
% 0.82/1.05  --out_options                           all
% 0.82/1.05  --tptp_safe_out                         true
% 0.82/1.05  --problem_path                          ""
% 0.82/1.05  --include_path                          ""
% 0.82/1.05  --clausifier                            res/vclausify_rel
% 0.82/1.05  --clausifier_options                    --mode clausify
% 0.82/1.05  --stdin                                 false
% 0.82/1.05  --stats_out                             all
% 0.82/1.05  
% 0.82/1.05  ------ General Options
% 0.82/1.05  
% 0.82/1.05  --fof                                   false
% 0.82/1.05  --time_out_real                         305.
% 0.82/1.05  --time_out_virtual                      -1.
% 0.82/1.05  --symbol_type_check                     false
% 0.82/1.05  --clausify_out                          false
% 0.82/1.05  --sig_cnt_out                           false
% 0.82/1.05  --trig_cnt_out                          false
% 0.82/1.05  --trig_cnt_out_tolerance                1.
% 0.82/1.05  --trig_cnt_out_sk_spl                   false
% 0.82/1.05  --abstr_cl_out                          false
% 0.82/1.05  
% 0.82/1.05  ------ Global Options
% 0.82/1.05  
% 0.82/1.05  --schedule                              default
% 0.82/1.05  --add_important_lit                     false
% 0.82/1.05  --prop_solver_per_cl                    1000
% 0.82/1.05  --min_unsat_core                        false
% 0.82/1.05  --soft_assumptions                      false
% 0.82/1.05  --soft_lemma_size                       3
% 0.82/1.05  --prop_impl_unit_size                   0
% 0.82/1.05  --prop_impl_unit                        []
% 0.82/1.05  --share_sel_clauses                     true
% 0.82/1.05  --reset_solvers                         false
% 0.82/1.05  --bc_imp_inh                            [conj_cone]
% 0.82/1.05  --conj_cone_tolerance                   3.
% 0.82/1.05  --extra_neg_conj                        none
% 0.82/1.05  --large_theory_mode                     true
% 0.82/1.05  --prolific_symb_bound                   200
% 0.82/1.05  --lt_threshold                          2000
% 0.82/1.05  --clause_weak_htbl                      true
% 0.82/1.05  --gc_record_bc_elim                     false
% 0.82/1.05  
% 0.82/1.05  ------ Preprocessing Options
% 0.82/1.05  
% 0.82/1.05  --preprocessing_flag                    true
% 0.82/1.05  --time_out_prep_mult                    0.1
% 0.82/1.05  --splitting_mode                        input
% 0.82/1.05  --splitting_grd                         true
% 0.82/1.05  --splitting_cvd                         false
% 0.82/1.05  --splitting_cvd_svl                     false
% 0.82/1.05  --splitting_nvd                         32
% 0.82/1.05  --sub_typing                            true
% 0.82/1.05  --prep_gs_sim                           true
% 0.82/1.05  --prep_unflatten                        true
% 0.82/1.05  --prep_res_sim                          true
% 0.82/1.05  --prep_upred                            true
% 0.82/1.05  --prep_sem_filter                       exhaustive
% 0.82/1.05  --prep_sem_filter_out                   false
% 0.82/1.05  --pred_elim                             true
% 0.82/1.05  --res_sim_input                         true
% 0.82/1.05  --eq_ax_congr_red                       true
% 0.82/1.05  --pure_diseq_elim                       true
% 0.82/1.05  --brand_transform                       false
% 0.82/1.05  --non_eq_to_eq                          false
% 0.82/1.05  --prep_def_merge                        true
% 0.82/1.05  --prep_def_merge_prop_impl              false
% 0.82/1.05  --prep_def_merge_mbd                    true
% 0.82/1.05  --prep_def_merge_tr_red                 false
% 0.82/1.05  --prep_def_merge_tr_cl                  false
% 0.82/1.05  --smt_preprocessing                     true
% 0.82/1.05  --smt_ac_axioms                         fast
% 0.82/1.05  --preprocessed_out                      false
% 0.82/1.05  --preprocessed_stats                    false
% 0.82/1.05  
% 0.82/1.05  ------ Abstraction refinement Options
% 0.82/1.05  
% 0.82/1.05  --abstr_ref                             []
% 0.82/1.05  --abstr_ref_prep                        false
% 0.82/1.05  --abstr_ref_until_sat                   false
% 0.82/1.05  --abstr_ref_sig_restrict                funpre
% 0.82/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/1.05  --abstr_ref_under                       []
% 0.82/1.05  
% 0.82/1.05  ------ SAT Options
% 0.82/1.05  
% 0.82/1.05  --sat_mode                              false
% 0.82/1.05  --sat_fm_restart_options                ""
% 0.82/1.05  --sat_gr_def                            false
% 0.82/1.05  --sat_epr_types                         true
% 0.82/1.05  --sat_non_cyclic_types                  false
% 0.82/1.05  --sat_finite_models                     false
% 0.82/1.05  --sat_fm_lemmas                         false
% 0.82/1.05  --sat_fm_prep                           false
% 0.82/1.05  --sat_fm_uc_incr                        true
% 0.82/1.05  --sat_out_model                         small
% 0.82/1.05  --sat_out_clauses                       false
% 0.82/1.05  
% 0.82/1.05  ------ QBF Options
% 0.82/1.05  
% 0.82/1.05  --qbf_mode                              false
% 0.82/1.05  --qbf_elim_univ                         false
% 0.82/1.05  --qbf_dom_inst                          none
% 0.82/1.05  --qbf_dom_pre_inst                      false
% 0.82/1.05  --qbf_sk_in                             false
% 0.82/1.05  --qbf_pred_elim                         true
% 0.82/1.05  --qbf_split                             512
% 0.82/1.05  
% 0.82/1.05  ------ BMC1 Options
% 0.82/1.05  
% 0.82/1.05  --bmc1_incremental                      false
% 0.82/1.05  --bmc1_axioms                           reachable_all
% 0.82/1.05  --bmc1_min_bound                        0
% 0.82/1.05  --bmc1_max_bound                        -1
% 0.82/1.05  --bmc1_max_bound_default                -1
% 0.82/1.05  --bmc1_symbol_reachability              true
% 0.82/1.05  --bmc1_property_lemmas                  false
% 0.82/1.05  --bmc1_k_induction                      false
% 0.82/1.05  --bmc1_non_equiv_states                 false
% 0.82/1.05  --bmc1_deadlock                         false
% 0.82/1.05  --bmc1_ucm                              false
% 0.82/1.05  --bmc1_add_unsat_core                   none
% 0.82/1.05  --bmc1_unsat_core_children              false
% 0.82/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/1.05  --bmc1_out_stat                         full
% 0.82/1.05  --bmc1_ground_init                      false
% 0.82/1.05  --bmc1_pre_inst_next_state              false
% 0.82/1.05  --bmc1_pre_inst_state                   false
% 0.82/1.05  --bmc1_pre_inst_reach_state             false
% 0.82/1.05  --bmc1_out_unsat_core                   false
% 0.82/1.05  --bmc1_aig_witness_out                  false
% 0.82/1.05  --bmc1_verbose                          false
% 0.82/1.05  --bmc1_dump_clauses_tptp                false
% 0.82/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.82/1.05  --bmc1_dump_file                        -
% 0.82/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.82/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.82/1.05  --bmc1_ucm_extend_mode                  1
% 0.82/1.05  --bmc1_ucm_init_mode                    2
% 0.82/1.05  --bmc1_ucm_cone_mode                    none
% 0.82/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.82/1.05  --bmc1_ucm_relax_model                  4
% 0.82/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.82/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/1.05  --bmc1_ucm_layered_model                none
% 0.82/1.05  --bmc1_ucm_max_lemma_size               10
% 0.82/1.05  
% 0.82/1.05  ------ AIG Options
% 0.82/1.05  
% 0.82/1.05  --aig_mode                              false
% 0.82/1.05  
% 0.82/1.05  ------ Instantiation Options
% 0.82/1.05  
% 0.82/1.05  --instantiation_flag                    true
% 0.82/1.05  --inst_sos_flag                         false
% 0.82/1.05  --inst_sos_phase                        true
% 0.82/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/1.05  --inst_lit_sel_side                     num_symb
% 0.82/1.05  --inst_solver_per_active                1400
% 0.82/1.05  --inst_solver_calls_frac                1.
% 0.82/1.05  --inst_passive_queue_type               priority_queues
% 0.82/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/1.05  --inst_passive_queues_freq              [25;2]
% 0.82/1.05  --inst_dismatching                      true
% 0.82/1.05  --inst_eager_unprocessed_to_passive     true
% 0.82/1.05  --inst_prop_sim_given                   true
% 0.82/1.05  --inst_prop_sim_new                     false
% 0.82/1.05  --inst_subs_new                         false
% 0.82/1.05  --inst_eq_res_simp                      false
% 0.82/1.05  --inst_subs_given                       false
% 0.82/1.05  --inst_orphan_elimination               true
% 0.82/1.05  --inst_learning_loop_flag               true
% 0.82/1.05  --inst_learning_start                   3000
% 0.82/1.05  --inst_learning_factor                  2
% 0.82/1.05  --inst_start_prop_sim_after_learn       3
% 0.82/1.05  --inst_sel_renew                        solver
% 0.82/1.05  --inst_lit_activity_flag                true
% 0.82/1.05  --inst_restr_to_given                   false
% 0.82/1.05  --inst_activity_threshold               500
% 0.82/1.05  --inst_out_proof                        true
% 0.82/1.05  
% 0.82/1.05  ------ Resolution Options
% 0.82/1.05  
% 0.82/1.05  --resolution_flag                       true
% 0.82/1.05  --res_lit_sel                           adaptive
% 0.82/1.05  --res_lit_sel_side                      none
% 0.82/1.05  --res_ordering                          kbo
% 0.82/1.05  --res_to_prop_solver                    active
% 0.82/1.05  --res_prop_simpl_new                    false
% 0.82/1.05  --res_prop_simpl_given                  true
% 0.82/1.05  --res_passive_queue_type                priority_queues
% 0.82/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/1.05  --res_passive_queues_freq               [15;5]
% 0.82/1.05  --res_forward_subs                      full
% 0.82/1.05  --res_backward_subs                     full
% 0.82/1.05  --res_forward_subs_resolution           true
% 0.82/1.05  --res_backward_subs_resolution          true
% 0.82/1.05  --res_orphan_elimination                true
% 0.82/1.05  --res_time_limit                        2.
% 0.82/1.05  --res_out_proof                         true
% 0.82/1.05  
% 0.82/1.05  ------ Superposition Options
% 0.82/1.05  
% 0.82/1.05  --superposition_flag                    true
% 0.82/1.05  --sup_passive_queue_type                priority_queues
% 0.82/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.82/1.05  --demod_completeness_check              fast
% 0.82/1.05  --demod_use_ground                      true
% 0.82/1.05  --sup_to_prop_solver                    passive
% 0.82/1.05  --sup_prop_simpl_new                    true
% 0.82/1.05  --sup_prop_simpl_given                  true
% 0.82/1.05  --sup_fun_splitting                     false
% 0.82/1.05  --sup_smt_interval                      50000
% 0.82/1.05  
% 0.82/1.05  ------ Superposition Simplification Setup
% 0.82/1.05  
% 0.82/1.05  --sup_indices_passive                   []
% 0.82/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.05  --sup_full_bw                           [BwDemod]
% 0.82/1.05  --sup_immed_triv                        [TrivRules]
% 0.82/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.05  --sup_immed_bw_main                     []
% 0.82/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/1.05  
% 0.82/1.05  ------ Combination Options
% 0.82/1.05  
% 0.82/1.05  --comb_res_mult                         3
% 0.82/1.05  --comb_sup_mult                         2
% 0.82/1.05  --comb_inst_mult                        10
% 0.82/1.05  
% 0.82/1.05  ------ Debug Options
% 0.82/1.05  
% 0.82/1.05  --dbg_backtrace                         false
% 0.82/1.05  --dbg_dump_prop_clauses                 false
% 0.82/1.05  --dbg_dump_prop_clauses_file            -
% 0.82/1.05  --dbg_out_stat                          false
% 0.82/1.05  ------ Parsing...
% 0.82/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.82/1.05  
% 0.82/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.82/1.05  
% 0.82/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.82/1.05  
% 0.82/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.82/1.05  ------ Proving...
% 0.82/1.05  ------ Problem Properties 
% 0.82/1.05  
% 0.82/1.05  
% 0.82/1.05  clauses                                 17
% 0.82/1.05  conjectures                             2
% 0.82/1.05  EPR                                     2
% 0.82/1.05  Horn                                    15
% 0.82/1.05  unary                                   5
% 0.82/1.05  binary                                  8
% 0.82/1.05  lits                                    33
% 0.82/1.05  lits eq                                 18
% 0.82/1.05  fd_pure                                 0
% 0.82/1.05  fd_pseudo                               0
% 0.82/1.05  fd_cond                                 1
% 0.82/1.05  fd_pseudo_cond                          1
% 0.82/1.05  AC symbols                              0
% 0.82/1.05  
% 0.82/1.05  ------ Schedule dynamic 5 is on 
% 0.82/1.05  
% 0.82/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.82/1.05  
% 0.82/1.05  
% 0.82/1.05  ------ 
% 0.82/1.05  Current options:
% 0.82/1.05  ------ 
% 0.82/1.05  
% 0.82/1.05  ------ Input Options
% 0.82/1.05  
% 0.82/1.05  --out_options                           all
% 0.82/1.05  --tptp_safe_out                         true
% 0.82/1.05  --problem_path                          ""
% 0.82/1.05  --include_path                          ""
% 0.82/1.05  --clausifier                            res/vclausify_rel
% 0.82/1.05  --clausifier_options                    --mode clausify
% 0.82/1.05  --stdin                                 false
% 0.82/1.05  --stats_out                             all
% 0.82/1.05  
% 0.82/1.05  ------ General Options
% 0.82/1.05  
% 0.82/1.05  --fof                                   false
% 0.82/1.05  --time_out_real                         305.
% 0.82/1.05  --time_out_virtual                      -1.
% 0.82/1.05  --symbol_type_check                     false
% 0.82/1.05  --clausify_out                          false
% 0.82/1.05  --sig_cnt_out                           false
% 0.82/1.05  --trig_cnt_out                          false
% 0.82/1.05  --trig_cnt_out_tolerance                1.
% 0.82/1.05  --trig_cnt_out_sk_spl                   false
% 0.82/1.05  --abstr_cl_out                          false
% 0.82/1.05  
% 0.82/1.05  ------ Global Options
% 0.82/1.05  
% 0.82/1.05  --schedule                              default
% 0.82/1.05  --add_important_lit                     false
% 0.82/1.05  --prop_solver_per_cl                    1000
% 0.82/1.05  --min_unsat_core                        false
% 0.82/1.05  --soft_assumptions                      false
% 0.82/1.05  --soft_lemma_size                       3
% 0.82/1.05  --prop_impl_unit_size                   0
% 0.82/1.05  --prop_impl_unit                        []
% 0.82/1.05  --share_sel_clauses                     true
% 0.82/1.05  --reset_solvers                         false
% 0.82/1.05  --bc_imp_inh                            [conj_cone]
% 0.82/1.05  --conj_cone_tolerance                   3.
% 0.82/1.05  --extra_neg_conj                        none
% 0.82/1.05  --large_theory_mode                     true
% 0.82/1.05  --prolific_symb_bound                   200
% 0.82/1.05  --lt_threshold                          2000
% 0.82/1.05  --clause_weak_htbl                      true
% 0.82/1.05  --gc_record_bc_elim                     false
% 0.82/1.05  
% 0.82/1.05  ------ Preprocessing Options
% 0.82/1.05  
% 0.82/1.05  --preprocessing_flag                    true
% 0.82/1.05  --time_out_prep_mult                    0.1
% 0.82/1.05  --splitting_mode                        input
% 0.82/1.05  --splitting_grd                         true
% 0.82/1.05  --splitting_cvd                         false
% 0.82/1.05  --splitting_cvd_svl                     false
% 0.82/1.05  --splitting_nvd                         32
% 0.82/1.05  --sub_typing                            true
% 0.82/1.05  --prep_gs_sim                           true
% 0.82/1.05  --prep_unflatten                        true
% 0.82/1.05  --prep_res_sim                          true
% 0.82/1.05  --prep_upred                            true
% 0.82/1.05  --prep_sem_filter                       exhaustive
% 0.82/1.05  --prep_sem_filter_out                   false
% 0.82/1.05  --pred_elim                             true
% 0.82/1.05  --res_sim_input                         true
% 0.82/1.05  --eq_ax_congr_red                       true
% 0.82/1.05  --pure_diseq_elim                       true
% 0.82/1.05  --brand_transform                       false
% 0.82/1.05  --non_eq_to_eq                          false
% 0.82/1.05  --prep_def_merge                        true
% 0.82/1.05  --prep_def_merge_prop_impl              false
% 0.82/1.05  --prep_def_merge_mbd                    true
% 0.82/1.05  --prep_def_merge_tr_red                 false
% 0.82/1.05  --prep_def_merge_tr_cl                  false
% 0.82/1.05  --smt_preprocessing                     true
% 0.82/1.05  --smt_ac_axioms                         fast
% 0.82/1.05  --preprocessed_out                      false
% 0.82/1.05  --preprocessed_stats                    false
% 0.82/1.05  
% 0.82/1.05  ------ Abstraction refinement Options
% 0.82/1.05  
% 0.82/1.05  --abstr_ref                             []
% 0.82/1.05  --abstr_ref_prep                        false
% 0.82/1.05  --abstr_ref_until_sat                   false
% 0.82/1.05  --abstr_ref_sig_restrict                funpre
% 0.82/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/1.05  --abstr_ref_under                       []
% 0.82/1.05  
% 0.82/1.05  ------ SAT Options
% 0.82/1.05  
% 0.82/1.05  --sat_mode                              false
% 0.82/1.05  --sat_fm_restart_options                ""
% 0.82/1.05  --sat_gr_def                            false
% 0.82/1.05  --sat_epr_types                         true
% 0.82/1.05  --sat_non_cyclic_types                  false
% 0.82/1.05  --sat_finite_models                     false
% 0.82/1.05  --sat_fm_lemmas                         false
% 0.82/1.05  --sat_fm_prep                           false
% 0.82/1.05  --sat_fm_uc_incr                        true
% 0.82/1.05  --sat_out_model                         small
% 0.82/1.05  --sat_out_clauses                       false
% 0.82/1.05  
% 0.82/1.05  ------ QBF Options
% 0.82/1.05  
% 0.82/1.05  --qbf_mode                              false
% 0.82/1.05  --qbf_elim_univ                         false
% 0.82/1.05  --qbf_dom_inst                          none
% 0.82/1.05  --qbf_dom_pre_inst                      false
% 0.82/1.05  --qbf_sk_in                             false
% 0.82/1.05  --qbf_pred_elim                         true
% 0.82/1.05  --qbf_split                             512
% 0.82/1.05  
% 0.82/1.05  ------ BMC1 Options
% 0.82/1.05  
% 0.82/1.05  --bmc1_incremental                      false
% 0.82/1.05  --bmc1_axioms                           reachable_all
% 0.82/1.05  --bmc1_min_bound                        0
% 0.82/1.05  --bmc1_max_bound                        -1
% 0.82/1.05  --bmc1_max_bound_default                -1
% 0.82/1.05  --bmc1_symbol_reachability              true
% 0.82/1.05  --bmc1_property_lemmas                  false
% 0.82/1.05  --bmc1_k_induction                      false
% 0.82/1.05  --bmc1_non_equiv_states                 false
% 0.82/1.05  --bmc1_deadlock                         false
% 0.82/1.05  --bmc1_ucm                              false
% 0.82/1.05  --bmc1_add_unsat_core                   none
% 0.82/1.05  --bmc1_unsat_core_children              false
% 0.82/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/1.05  --bmc1_out_stat                         full
% 0.82/1.05  --bmc1_ground_init                      false
% 0.82/1.05  --bmc1_pre_inst_next_state              false
% 0.82/1.05  --bmc1_pre_inst_state                   false
% 0.82/1.05  --bmc1_pre_inst_reach_state             false
% 0.82/1.05  --bmc1_out_unsat_core                   false
% 0.82/1.05  --bmc1_aig_witness_out                  false
% 0.82/1.05  --bmc1_verbose                          false
% 0.82/1.05  --bmc1_dump_clauses_tptp                false
% 0.82/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.82/1.05  --bmc1_dump_file                        -
% 0.82/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.82/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.82/1.05  --bmc1_ucm_extend_mode                  1
% 0.82/1.05  --bmc1_ucm_init_mode                    2
% 0.82/1.05  --bmc1_ucm_cone_mode                    none
% 0.82/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.82/1.05  --bmc1_ucm_relax_model                  4
% 0.82/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.82/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/1.05  --bmc1_ucm_layered_model                none
% 0.82/1.05  --bmc1_ucm_max_lemma_size               10
% 0.82/1.05  
% 0.82/1.05  ------ AIG Options
% 0.82/1.05  
% 0.82/1.05  --aig_mode                              false
% 0.82/1.05  
% 0.82/1.05  ------ Instantiation Options
% 0.82/1.05  
% 0.82/1.05  --instantiation_flag                    true
% 0.82/1.05  --inst_sos_flag                         false
% 0.82/1.05  --inst_sos_phase                        true
% 0.82/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/1.05  --inst_lit_sel_side                     none
% 0.82/1.05  --inst_solver_per_active                1400
% 0.82/1.05  --inst_solver_calls_frac                1.
% 0.82/1.05  --inst_passive_queue_type               priority_queues
% 0.82/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/1.05  --inst_passive_queues_freq              [25;2]
% 0.82/1.05  --inst_dismatching                      true
% 0.82/1.05  --inst_eager_unprocessed_to_passive     true
% 0.82/1.05  --inst_prop_sim_given                   true
% 0.82/1.05  --inst_prop_sim_new                     false
% 0.82/1.05  --inst_subs_new                         false
% 0.82/1.05  --inst_eq_res_simp                      false
% 0.82/1.05  --inst_subs_given                       false
% 0.82/1.05  --inst_orphan_elimination               true
% 0.82/1.05  --inst_learning_loop_flag               true
% 0.82/1.05  --inst_learning_start                   3000
% 0.82/1.05  --inst_learning_factor                  2
% 0.82/1.05  --inst_start_prop_sim_after_learn       3
% 0.82/1.05  --inst_sel_renew                        solver
% 0.82/1.05  --inst_lit_activity_flag                true
% 0.82/1.05  --inst_restr_to_given                   false
% 0.82/1.05  --inst_activity_threshold               500
% 0.82/1.05  --inst_out_proof                        true
% 0.82/1.05  
% 0.82/1.05  ------ Resolution Options
% 0.82/1.05  
% 0.82/1.05  --resolution_flag                       false
% 0.82/1.05  --res_lit_sel                           adaptive
% 0.82/1.05  --res_lit_sel_side                      none
% 0.82/1.05  --res_ordering                          kbo
% 0.82/1.05  --res_to_prop_solver                    active
% 0.82/1.05  --res_prop_simpl_new                    false
% 0.82/1.05  --res_prop_simpl_given                  true
% 0.82/1.05  --res_passive_queue_type                priority_queues
% 0.82/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/1.05  --res_passive_queues_freq               [15;5]
% 0.82/1.05  --res_forward_subs                      full
% 0.82/1.05  --res_backward_subs                     full
% 0.82/1.05  --res_forward_subs_resolution           true
% 0.82/1.05  --res_backward_subs_resolution          true
% 0.82/1.05  --res_orphan_elimination                true
% 0.82/1.05  --res_time_limit                        2.
% 0.82/1.05  --res_out_proof                         true
% 0.82/1.05  
% 0.82/1.05  ------ Superposition Options
% 0.82/1.05  
% 0.82/1.05  --superposition_flag                    true
% 0.82/1.05  --sup_passive_queue_type                priority_queues
% 0.82/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.82/1.05  --demod_completeness_check              fast
% 0.82/1.05  --demod_use_ground                      true
% 0.82/1.05  --sup_to_prop_solver                    passive
% 0.82/1.05  --sup_prop_simpl_new                    true
% 0.82/1.05  --sup_prop_simpl_given                  true
% 0.82/1.05  --sup_fun_splitting                     false
% 0.82/1.05  --sup_smt_interval                      50000
% 0.82/1.05  
% 0.82/1.05  ------ Superposition Simplification Setup
% 0.82/1.05  
% 0.82/1.05  --sup_indices_passive                   []
% 0.82/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.05  --sup_full_bw                           [BwDemod]
% 0.82/1.05  --sup_immed_triv                        [TrivRules]
% 0.82/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.05  --sup_immed_bw_main                     []
% 0.82/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/1.05  
% 0.82/1.05  ------ Combination Options
% 0.82/1.05  
% 0.82/1.05  --comb_res_mult                         3
% 0.82/1.05  --comb_sup_mult                         2
% 0.82/1.05  --comb_inst_mult                        10
% 0.82/1.05  
% 0.82/1.05  ------ Debug Options
% 0.82/1.05  
% 0.82/1.05  --dbg_backtrace                         false
% 0.82/1.05  --dbg_dump_prop_clauses                 false
% 0.82/1.05  --dbg_dump_prop_clauses_file            -
% 0.82/1.05  --dbg_out_stat                          false
% 0.82/1.05  
% 0.82/1.05  
% 0.82/1.05  
% 0.82/1.05  
% 0.82/1.05  ------ Proving...
% 0.82/1.05  
% 0.82/1.05  
% 0.82/1.05  % SZS status Theorem for theBenchmark.p
% 0.82/1.05  
% 0.82/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 0.82/1.05  
% 0.82/1.05  fof(f8,axiom,(
% 0.82/1.05    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f22,plain,(
% 0.82/1.05    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.82/1.05    inference(nnf_transformation,[],[f8])).
% 0.82/1.05  
% 0.82/1.05  fof(f23,plain,(
% 0.82/1.05    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.82/1.05    inference(rectify,[],[f22])).
% 0.82/1.05  
% 0.82/1.05  fof(f24,plain,(
% 0.82/1.05    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 0.82/1.05    introduced(choice_axiom,[])).
% 0.82/1.05  
% 0.82/1.05  fof(f25,plain,(
% 0.82/1.05    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.82/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 0.82/1.05  
% 0.82/1.05  fof(f41,plain,(
% 0.82/1.05    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.82/1.05    inference(cnf_transformation,[],[f25])).
% 0.82/1.05  
% 0.82/1.05  fof(f59,plain,(
% 0.82/1.05    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.82/1.05    inference(equality_resolution,[],[f41])).
% 0.82/1.05  
% 0.82/1.05  fof(f9,axiom,(
% 0.82/1.05    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f16,plain,(
% 0.82/1.05    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.82/1.05    inference(ennf_transformation,[],[f9])).
% 0.82/1.05  
% 0.82/1.05  fof(f26,plain,(
% 0.82/1.05    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.82/1.05    inference(nnf_transformation,[],[f16])).
% 0.82/1.05  
% 0.82/1.05  fof(f45,plain,(
% 0.82/1.05    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.82/1.05    inference(cnf_transformation,[],[f26])).
% 0.82/1.05  
% 0.82/1.05  fof(f13,conjecture,(
% 0.82/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f14,negated_conjecture,(
% 0.82/1.05    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.82/1.05    inference(negated_conjecture,[],[f13])).
% 0.82/1.05  
% 0.82/1.05  fof(f18,plain,(
% 0.82/1.05    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.82/1.05    inference(ennf_transformation,[],[f14])).
% 0.82/1.05  
% 0.82/1.05  fof(f27,plain,(
% 0.82/1.05    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.82/1.05    inference(nnf_transformation,[],[f18])).
% 0.82/1.05  
% 0.82/1.05  fof(f28,plain,(
% 0.82/1.05    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.82/1.05    inference(flattening,[],[f27])).
% 0.82/1.05  
% 0.82/1.05  fof(f29,plain,(
% 0.82/1.05    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 0.82/1.05    introduced(choice_axiom,[])).
% 0.82/1.05  
% 0.82/1.05  fof(f30,plain,(
% 0.82/1.05    (k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.82/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).
% 0.82/1.05  
% 0.82/1.05  fof(f52,plain,(
% 0.82/1.05    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.82/1.05    inference(cnf_transformation,[],[f30])).
% 0.82/1.05  
% 0.82/1.05  fof(f12,axiom,(
% 0.82/1.05    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f51,plain,(
% 0.82/1.05    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.82/1.05    inference(cnf_transformation,[],[f12])).
% 0.82/1.05  
% 0.82/1.05  fof(f3,axiom,(
% 0.82/1.05    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f21,plain,(
% 0.82/1.05    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.82/1.05    inference(nnf_transformation,[],[f3])).
% 0.82/1.05  
% 0.82/1.05  fof(f36,plain,(
% 0.82/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.82/1.05    inference(cnf_transformation,[],[f21])).
% 0.82/1.05  
% 0.82/1.05  fof(f1,axiom,(
% 0.82/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f31,plain,(
% 0.82/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.82/1.05    inference(cnf_transformation,[],[f1])).
% 0.82/1.05  
% 0.82/1.05  fof(f6,axiom,(
% 0.82/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f39,plain,(
% 0.82/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.82/1.05    inference(cnf_transformation,[],[f6])).
% 0.82/1.05  
% 0.82/1.05  fof(f55,plain,(
% 0.82/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.82/1.05    inference(definition_unfolding,[],[f31,f39,f39])).
% 0.82/1.05  
% 0.82/1.05  fof(f4,axiom,(
% 0.82/1.05    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f15,plain,(
% 0.82/1.05    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.82/1.05    inference(ennf_transformation,[],[f4])).
% 0.82/1.05  
% 0.82/1.05  fof(f37,plain,(
% 0.82/1.05    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 0.82/1.05    inference(cnf_transformation,[],[f15])).
% 0.82/1.05  
% 0.82/1.05  fof(f5,axiom,(
% 0.82/1.05    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f38,plain,(
% 0.82/1.05    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.82/1.05    inference(cnf_transformation,[],[f5])).
% 0.82/1.05  
% 0.82/1.05  fof(f35,plain,(
% 0.82/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.82/1.05    inference(cnf_transformation,[],[f21])).
% 0.82/1.05  
% 0.82/1.05  fof(f2,axiom,(
% 0.82/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f19,plain,(
% 0.82/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.82/1.05    inference(nnf_transformation,[],[f2])).
% 0.82/1.05  
% 0.82/1.05  fof(f20,plain,(
% 0.82/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.82/1.05    inference(flattening,[],[f19])).
% 0.82/1.05  
% 0.82/1.05  fof(f34,plain,(
% 0.82/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.82/1.05    inference(cnf_transformation,[],[f20])).
% 0.82/1.05  
% 0.82/1.05  fof(f7,axiom,(
% 0.82/1.05    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f40,plain,(
% 0.82/1.05    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 0.82/1.05    inference(cnf_transformation,[],[f7])).
% 0.82/1.05  
% 0.82/1.05  fof(f53,plain,(
% 0.82/1.05    k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 0.82/1.05    inference(cnf_transformation,[],[f30])).
% 0.82/1.05  
% 0.82/1.05  fof(f10,axiom,(
% 0.82/1.05    ! [X0] : k2_subset_1(X0) = X0),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f49,plain,(
% 0.82/1.05    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.82/1.05    inference(cnf_transformation,[],[f10])).
% 0.82/1.05  
% 0.82/1.05  fof(f11,axiom,(
% 0.82/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.82/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.05  
% 0.82/1.05  fof(f17,plain,(
% 0.82/1.05    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.82/1.05    inference(ennf_transformation,[],[f11])).
% 0.82/1.05  
% 0.82/1.05  fof(f50,plain,(
% 0.82/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.82/1.05    inference(cnf_transformation,[],[f17])).
% 0.82/1.05  
% 0.82/1.05  fof(f54,plain,(
% 0.82/1.05    k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 0.82/1.05    inference(cnf_transformation,[],[f30])).
% 0.82/1.05  
% 0.82/1.05  fof(f32,plain,(
% 0.82/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.82/1.05    inference(cnf_transformation,[],[f20])).
% 0.82/1.05  
% 0.82/1.05  fof(f57,plain,(
% 0.82/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.82/1.05    inference(equality_resolution,[],[f32])).
% 0.82/1.05  
% 0.82/1.05  cnf(c_12,plain,
% 0.82/1.05      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.82/1.05      inference(cnf_transformation,[],[f59]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_481,plain,
% 0.82/1.05      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 0.82/1.05      inference(prop_impl,[status(thm)],[c_12]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_482,plain,
% 0.82/1.05      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.82/1.05      inference(renaming,[status(thm)],[c_481]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_16,plain,
% 0.82/1.05      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 0.82/1.05      inference(cnf_transformation,[],[f45]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_22,negated_conjecture,
% 0.82/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 0.82/1.05      inference(cnf_transformation,[],[f52]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_300,plain,
% 0.82/1.05      ( r2_hidden(X0,X1)
% 0.82/1.05      | v1_xboole_0(X1)
% 0.82/1.05      | k1_zfmisc_1(sK1) != X1
% 0.82/1.05      | sK2 != X0 ),
% 0.82/1.05      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_301,plain,
% 0.82/1.05      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 0.82/1.05      inference(unflattening,[status(thm)],[c_300]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_19,plain,
% 0.82/1.05      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 0.82/1.05      inference(cnf_transformation,[],[f51]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_307,plain,
% 0.82/1.05      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 0.82/1.05      inference(forward_subsumption_resolution,
% 0.82/1.05                [status(thm)],
% 0.82/1.05                [c_301,c_19]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_613,plain,
% 0.82/1.05      ( r1_tarski(X0,X1)
% 0.82/1.05      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 0.82/1.05      | sK2 != X0 ),
% 0.82/1.05      inference(resolution_lifted,[status(thm)],[c_482,c_307]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_614,plain,
% 0.82/1.05      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 0.82/1.05      inference(unflattening,[status(thm)],[c_613]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_1086,plain,
% 0.82/1.05      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 0.82/1.05      | r1_tarski(sK2,X0) = iProver_top ),
% 0.82/1.05      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_1263,plain,
% 0.82/1.05      ( r1_tarski(sK2,sK1) = iProver_top ),
% 0.82/1.05      inference(equality_resolution,[status(thm)],[c_1086]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_4,plain,
% 0.82/1.05      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 0.82/1.05      inference(cnf_transformation,[],[f36]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_1095,plain,
% 0.82/1.05      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 0.82/1.05      | r1_tarski(X0,X1) != iProver_top ),
% 0.82/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_1963,plain,
% 0.82/1.05      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 0.82/1.05      inference(superposition,[status(thm)],[c_1263,c_1095]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_0,plain,
% 0.82/1.05      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 0.82/1.05      inference(cnf_transformation,[],[f55]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_6,plain,
% 0.82/1.05      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 0.82/1.05      inference(cnf_transformation,[],[f37]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_1093,plain,
% 0.82/1.05      ( k1_xboole_0 = X0
% 0.82/1.05      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 0.82/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_1658,plain,
% 0.82/1.05      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 0.82/1.05      | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) != iProver_top ),
% 0.82/1.05      inference(superposition,[status(thm)],[c_0,c_1093]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_2641,plain,
% 0.82/1.05      ( k4_xboole_0(sK1,sK2) = k1_xboole_0
% 0.82/1.05      | r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,k1_xboole_0)) != iProver_top ),
% 0.82/1.05      inference(superposition,[status(thm)],[c_1963,c_1658]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_7,plain,
% 0.82/1.05      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 0.82/1.05      inference(cnf_transformation,[],[f38]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_2653,plain,
% 0.82/1.05      ( k4_xboole_0(sK1,sK2) = k1_xboole_0
% 0.82/1.05      | r1_tarski(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
% 0.82/1.05      inference(demodulation,[status(thm)],[c_2641,c_7]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_769,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_1622,plain,
% 0.82/1.05      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 0.82/1.05      inference(instantiation,[status(thm)],[c_769]) ).
% 0.82/1.05  
% 0.82/1.05  cnf(c_2580,plain,
% 0.82/1.05      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 0.82/1.05      inference(instantiation,[status(thm)],[c_1622]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_2581,plain,
% 0.82/1.06      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_2580]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_771,plain,
% 0.82/1.06      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.82/1.06      theory(equality) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_2517,plain,
% 0.82/1.06      ( ~ r1_tarski(X0,X1) | r1_tarski(sK1,X2) | X2 != X1 | sK1 != X0 ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_771]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_2518,plain,
% 0.82/1.06      ( X0 != X1
% 0.82/1.06      | sK1 != X2
% 0.82/1.06      | r1_tarski(X2,X1) != iProver_top
% 0.82/1.06      | r1_tarski(sK1,X0) = iProver_top ),
% 0.82/1.06      inference(predicate_to_equality,[status(thm)],[c_2517]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_2520,plain,
% 0.82/1.06      ( sK2 != sK2
% 0.82/1.06      | sK1 != sK2
% 0.82/1.06      | r1_tarski(sK2,sK2) != iProver_top
% 0.82/1.06      | r1_tarski(sK1,sK2) = iProver_top ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_2518]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_5,plain,
% 0.82/1.06      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 0.82/1.06      inference(cnf_transformation,[],[f35]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_2511,plain,
% 0.82/1.06      ( r1_tarski(sK1,X0) | k4_xboole_0(sK1,X0) != k1_xboole_0 ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_5]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_2512,plain,
% 0.82/1.06      ( k4_xboole_0(sK1,X0) != k1_xboole_0
% 0.82/1.06      | r1_tarski(sK1,X0) = iProver_top ),
% 0.82/1.06      inference(predicate_to_equality,[status(thm)],[c_2511]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_2514,plain,
% 0.82/1.06      ( k4_xboole_0(sK1,sK2) != k1_xboole_0
% 0.82/1.06      | r1_tarski(sK1,sK2) = iProver_top ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_2512]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1,plain,
% 0.82/1.06      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 0.82/1.06      inference(cnf_transformation,[],[f34]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1097,plain,
% 0.82/1.06      ( X0 = X1
% 0.82/1.06      | r1_tarski(X0,X1) != iProver_top
% 0.82/1.06      | r1_tarski(X1,X0) != iProver_top ),
% 0.82/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_2277,plain,
% 0.82/1.06      ( sK2 = sK1 | r1_tarski(sK1,sK2) != iProver_top ),
% 0.82/1.06      inference(superposition,[status(thm)],[c_1263,c_1097]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1899,plain,
% 0.82/1.06      ( ~ r1_tarski(sK1,sK2) | k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_4]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1904,plain,
% 0.82/1.06      ( k4_xboole_0(sK1,sK2) = k1_xboole_0
% 0.82/1.06      | r1_tarski(sK1,sK2) != iProver_top ),
% 0.82/1.06      inference(predicate_to_equality,[status(thm)],[c_1899]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1506,plain,
% 0.82/1.06      ( ~ r1_tarski(X0,X1)
% 0.82/1.06      | r1_tarski(k4_xboole_0(sK1,sK2),X2)
% 0.82/1.06      | X2 != X1
% 0.82/1.06      | k4_xboole_0(sK1,sK2) != X0 ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_771]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1898,plain,
% 0.82/1.06      ( r1_tarski(k4_xboole_0(sK1,sK2),X0)
% 0.82/1.06      | ~ r1_tarski(k1_xboole_0,X1)
% 0.82/1.06      | X0 != X1
% 0.82/1.06      | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_1506]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1900,plain,
% 0.82/1.06      ( X0 != X1
% 0.82/1.06      | k4_xboole_0(sK1,sK2) != k1_xboole_0
% 0.82/1.06      | r1_tarski(k4_xboole_0(sK1,sK2),X0) = iProver_top
% 0.82/1.06      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 0.82/1.06      inference(predicate_to_equality,[status(thm)],[c_1898]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1902,plain,
% 0.82/1.06      ( k4_xboole_0(sK1,sK2) != k1_xboole_0
% 0.82/1.06      | sK2 != sK2
% 0.82/1.06      | r1_tarski(k4_xboole_0(sK1,sK2),sK2) = iProver_top
% 0.82/1.06      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_1900]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_8,plain,
% 0.82/1.06      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.82/1.06      inference(cnf_transformation,[],[f40]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1094,plain,
% 0.82/1.06      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 0.82/1.06      | r1_tarski(X0,X1) = iProver_top ),
% 0.82/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1782,plain,
% 0.82/1.06      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 0.82/1.06      inference(superposition,[status(thm)],[c_8,c_1094]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1799,plain,
% 0.82/1.06      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_1782]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_768,plain,( X0 = X0 ),theory(equality) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1621,plain,
% 0.82/1.06      ( sK1 = sK1 ),
% 0.82/1.06      inference(instantiation,[status(thm)],[c_768]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_21,negated_conjecture,
% 0.82/1.06      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) = sK2 ),
% 0.82/1.06      inference(cnf_transformation,[],[f53]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1091,plain,
% 0.82/1.06      ( k2_subset_1(sK1) = sK2
% 0.82/1.06      | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 0.82/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_17,plain,
% 0.82/1.06      ( k2_subset_1(X0) = X0 ),
% 0.82/1.06      inference(cnf_transformation,[],[f49]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1112,plain,
% 0.82/1.06      ( sK2 = sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 0.82/1.06      inference(demodulation,[status(thm)],[c_1091,c_17]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_18,plain,
% 0.82/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.82/1.06      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 0.82/1.06      inference(cnf_transformation,[],[f50]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_313,plain,
% 0.82/1.06      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 0.82/1.06      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 0.82/1.06      | sK2 != X1 ),
% 0.82/1.06      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_314,plain,
% 0.82/1.06      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 0.82/1.06      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 0.82/1.06      inference(unflattening,[status(thm)],[c_313]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1193,plain,
% 0.82/1.06      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 0.82/1.06      inference(equality_resolution,[status(thm)],[c_314]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_1224,plain,
% 0.82/1.06      ( sK2 = sK1 | r1_tarski(k4_xboole_0(sK1,sK2),sK2) = iProver_top ),
% 0.82/1.06      inference(light_normalisation,[status(thm)],[c_1112,c_1193]) ).
% 0.82/1.06  
% 0.82/1.06  cnf(c_20,negated_conjecture,
% 0.82/1.06      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) != sK2 ),
% 0.82/1.06      inference(cnf_transformation,[],[f54]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(c_1092,plain,
% 0.89/1.06      ( k2_subset_1(sK1) != sK2
% 0.89/1.06      | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 0.89/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(c_1137,plain,
% 0.89/1.06      ( sK2 != sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 0.89/1.06      inference(demodulation,[status(thm)],[c_1092,c_17]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(c_1219,plain,
% 0.89/1.06      ( sK2 != sK1 | r1_tarski(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
% 0.89/1.06      inference(light_normalisation,[status(thm)],[c_1137,c_1193]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(c_71,plain,
% 0.89/1.06      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 0.89/1.06      inference(instantiation,[status(thm)],[c_1]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(c_3,plain,
% 0.89/1.06      ( r1_tarski(X0,X0) ),
% 0.89/1.06      inference(cnf_transformation,[],[f57]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(c_67,plain,
% 0.89/1.06      ( r1_tarski(sK2,sK2) ),
% 0.89/1.06      inference(instantiation,[status(thm)],[c_3]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(c_64,plain,
% 0.89/1.06      ( ~ r1_tarski(sK2,sK2) | k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 0.89/1.06      inference(instantiation,[status(thm)],[c_4]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(c_60,plain,
% 0.89/1.06      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 0.89/1.06      | r1_tarski(X0,X1) = iProver_top ),
% 0.89/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(c_62,plain,
% 0.89/1.06      ( k4_xboole_0(sK2,sK2) != k1_xboole_0
% 0.89/1.06      | r1_tarski(sK2,sK2) = iProver_top ),
% 0.89/1.06      inference(instantiation,[status(thm)],[c_60]) ).
% 0.89/1.06  
% 0.89/1.06  cnf(contradiction,plain,
% 0.89/1.06      ( $false ),
% 0.89/1.06      inference(minisat,
% 0.89/1.06                [status(thm)],
% 0.89/1.06                [c_2653,c_2581,c_2520,c_2514,c_2277,c_1904,c_1902,c_1799,
% 0.89/1.06                 c_1621,c_1224,c_1219,c_71,c_67,c_64,c_62]) ).
% 0.89/1.06  
% 0.89/1.06  
% 0.89/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 0.89/1.06  
% 0.89/1.06  ------                               Statistics
% 0.89/1.06  
% 0.89/1.06  ------ General
% 0.89/1.06  
% 0.89/1.06  abstr_ref_over_cycles:                  0
% 0.89/1.06  abstr_ref_under_cycles:                 0
% 0.89/1.06  gc_basic_clause_elim:                   0
% 0.89/1.06  forced_gc_time:                         0
% 0.89/1.06  parsing_time:                           0.016
% 0.89/1.06  unif_index_cands_time:                  0.
% 0.89/1.06  unif_index_add_time:                    0.
% 0.89/1.06  orderings_time:                         0.
% 0.89/1.06  out_proof_time:                         0.023
% 0.89/1.06  total_time:                             0.147
% 0.89/1.06  num_of_symbols:                         43
% 0.89/1.06  num_of_terms:                           2029
% 0.89/1.06  
% 0.89/1.06  ------ Preprocessing
% 0.89/1.06  
% 0.89/1.06  num_of_splits:                          0
% 0.89/1.06  num_of_split_atoms:                     0
% 0.89/1.06  num_of_reused_defs:                     0
% 0.89/1.06  num_eq_ax_congr_red:                    6
% 0.89/1.06  num_of_sem_filtered_clauses:            1
% 0.89/1.06  num_of_subtypes:                        0
% 0.89/1.06  monotx_restored_types:                  0
% 0.89/1.06  sat_num_of_epr_types:                   0
% 0.89/1.06  sat_num_of_non_cyclic_types:            0
% 0.89/1.06  sat_guarded_non_collapsed_types:        0
% 0.89/1.06  num_pure_diseq_elim:                    0
% 0.89/1.06  simp_replaced_by:                       0
% 0.89/1.06  res_preprocessed:                       108
% 0.89/1.06  prep_upred:                             0
% 0.89/1.06  prep_unflattend:                        24
% 0.89/1.06  smt_new_axioms:                         0
% 0.89/1.06  pred_elim_cands:                        1
% 0.89/1.06  pred_elim:                              3
% 0.89/1.06  pred_elim_cl:                           5
% 0.89/1.06  pred_elim_cycles:                       6
% 0.89/1.06  merged_defs:                            24
% 0.89/1.06  merged_defs_ncl:                        0
% 0.89/1.06  bin_hyper_res:                          25
% 0.89/1.06  prep_cycles:                            5
% 0.89/1.06  pred_elim_time:                         0.006
% 0.89/1.06  splitting_time:                         0.
% 0.89/1.06  sem_filter_time:                        0.
% 0.89/1.06  monotx_time:                            0.
% 0.89/1.06  subtype_inf_time:                       0.
% 0.89/1.06  
% 0.89/1.06  ------ Problem properties
% 0.89/1.06  
% 0.89/1.06  clauses:                                17
% 0.89/1.06  conjectures:                            2
% 0.89/1.06  epr:                                    2
% 0.89/1.06  horn:                                   15
% 0.89/1.06  ground:                                 2
% 0.89/1.06  unary:                                  5
% 0.89/1.06  binary:                                 8
% 0.89/1.06  lits:                                   33
% 0.89/1.06  lits_eq:                                18
% 0.89/1.06  fd_pure:                                0
% 0.89/1.06  fd_pseudo:                              0
% 0.89/1.06  fd_cond:                                1
% 0.89/1.06  fd_pseudo_cond:                         1
% 0.89/1.06  ac_symbols:                             0
% 0.89/1.06  
% 0.89/1.06  ------ Propositional Solver
% 0.89/1.06  
% 0.89/1.06  prop_solver_calls:                      31
% 0.89/1.06  prop_fast_solver_calls:                 534
% 0.89/1.06  smt_solver_calls:                       0
% 0.89/1.06  smt_fast_solver_calls:                  0
% 0.89/1.06  prop_num_of_clauses:                    816
% 0.89/1.06  prop_preprocess_simplified:             3839
% 0.89/1.06  prop_fo_subsumed:                       1
% 0.89/1.06  prop_solver_time:                       0.
% 0.89/1.06  smt_solver_time:                        0.
% 0.89/1.06  smt_fast_solver_time:                   0.
% 0.89/1.06  prop_fast_solver_time:                  0.
% 0.89/1.06  prop_unsat_core_time:                   0.
% 0.89/1.06  
% 0.89/1.06  ------ QBF
% 0.89/1.06  
% 0.89/1.06  qbf_q_res:                              0
% 0.89/1.06  qbf_num_tautologies:                    0
% 0.89/1.06  qbf_prep_cycles:                        0
% 0.89/1.06  
% 0.89/1.06  ------ BMC1
% 0.89/1.06  
% 0.89/1.06  bmc1_current_bound:                     -1
% 0.89/1.06  bmc1_last_solved_bound:                 -1
% 0.89/1.06  bmc1_unsat_core_size:                   -1
% 0.89/1.06  bmc1_unsat_core_parents_size:           -1
% 0.89/1.06  bmc1_merge_next_fun:                    0
% 0.89/1.06  bmc1_unsat_core_clauses_time:           0.
% 0.89/1.06  
% 0.89/1.06  ------ Instantiation
% 0.89/1.06  
% 0.89/1.06  inst_num_of_clauses:                    270
% 0.89/1.06  inst_num_in_passive:                    102
% 0.89/1.06  inst_num_in_active:                     118
% 0.89/1.06  inst_num_in_unprocessed:                50
% 0.89/1.06  inst_num_of_loops:                      150
% 0.89/1.06  inst_num_of_learning_restarts:          0
% 0.89/1.06  inst_num_moves_active_passive:          30
% 0.89/1.06  inst_lit_activity:                      0
% 0.89/1.06  inst_lit_activity_moves:                0
% 0.89/1.06  inst_num_tautologies:                   0
% 0.89/1.06  inst_num_prop_implied:                  0
% 0.89/1.06  inst_num_existing_simplified:           0
% 0.89/1.06  inst_num_eq_res_simplified:             0
% 0.89/1.06  inst_num_child_elim:                    0
% 0.89/1.06  inst_num_of_dismatching_blockings:      22
% 0.89/1.06  inst_num_of_non_proper_insts:           208
% 0.89/1.06  inst_num_of_duplicates:                 0
% 0.89/1.06  inst_inst_num_from_inst_to_res:         0
% 0.89/1.06  inst_dismatching_checking_time:         0.
% 0.89/1.06  
% 0.89/1.06  ------ Resolution
% 0.89/1.06  
% 0.89/1.06  res_num_of_clauses:                     0
% 0.89/1.06  res_num_in_passive:                     0
% 0.89/1.06  res_num_in_active:                      0
% 0.89/1.06  res_num_of_loops:                       113
% 0.89/1.06  res_forward_subset_subsumed:            17
% 0.89/1.06  res_backward_subset_subsumed:           0
% 0.89/1.06  res_forward_subsumed:                   2
% 0.89/1.06  res_backward_subsumed:                  0
% 0.89/1.06  res_forward_subsumption_resolution:     2
% 0.89/1.06  res_backward_subsumption_resolution:    0
% 0.89/1.06  res_clause_to_clause_subsumption:       232
% 0.89/1.06  res_orphan_elimination:                 0
% 0.89/1.06  res_tautology_del:                      64
% 0.89/1.06  res_num_eq_res_simplified:              0
% 0.89/1.06  res_num_sel_changes:                    0
% 0.89/1.06  res_moves_from_active_to_pass:          0
% 0.89/1.06  
% 0.89/1.06  ------ Superposition
% 0.89/1.06  
% 0.89/1.06  sup_time_total:                         0.
% 0.89/1.06  sup_time_generating:                    0.
% 0.89/1.06  sup_time_sim_full:                      0.
% 0.89/1.06  sup_time_sim_immed:                     0.
% 0.89/1.06  
% 0.89/1.06  sup_num_of_clauses:                     49
% 0.89/1.06  sup_num_in_active:                      29
% 0.89/1.06  sup_num_in_passive:                     20
% 0.89/1.06  sup_num_of_loops:                       29
% 0.89/1.06  sup_fw_superposition:                   61
% 0.89/1.06  sup_bw_superposition:                   28
% 0.89/1.06  sup_immediate_simplified:               31
% 0.89/1.06  sup_given_eliminated:                   0
% 0.89/1.06  comparisons_done:                       0
% 0.89/1.06  comparisons_avoided:                    3
% 0.89/1.06  
% 0.89/1.06  ------ Simplifications
% 0.89/1.06  
% 0.89/1.06  
% 0.89/1.06  sim_fw_subset_subsumed:                 11
% 0.89/1.06  sim_bw_subset_subsumed:                 0
% 0.89/1.06  sim_fw_subsumed:                        3
% 0.89/1.06  sim_bw_subsumed:                        0
% 0.89/1.06  sim_fw_subsumption_res:                 0
% 0.89/1.06  sim_bw_subsumption_res:                 0
% 0.89/1.06  sim_tautology_del:                      2
% 0.89/1.06  sim_eq_tautology_del:                   4
% 0.89/1.06  sim_eq_res_simp:                        2
% 0.89/1.06  sim_fw_demodulated:                     14
% 0.89/1.06  sim_bw_demodulated:                     0
% 0.89/1.06  sim_light_normalised:                   13
% 0.89/1.06  sim_joinable_taut:                      0
% 0.89/1.06  sim_joinable_simp:                      0
% 0.89/1.06  sim_ac_normalised:                      0
% 0.89/1.06  sim_smt_subsumption:                    0
% 0.89/1.06  
%------------------------------------------------------------------------------
