%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:04 EST 2020

% Result     : Theorem 15.37s
% Output     : CNFRefutation 15.37s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 308 expanded)
%              Number of clauses        :   55 ( 105 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  255 ( 989 expanded)
%              Number of equality atoms :  155 ( 510 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f13,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK6 != sK7
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( sK6 != sK7
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f13,f32])).

fof(f59,plain,(
    k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) ) ),
    inference(definition_unfolding,[],[f57,f41])).

fof(f75,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2))) ),
    inference(equality_resolution,[],[f64])).

fof(f60,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    sK6 != sK7 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_34903,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34899,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_27,negated_conjecture,
    ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34896,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_35268,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_34896])).

cnf(c_35845,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_34899,c_35268])).

cnf(c_36221,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK0(sK7,X1),sK6) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_34903,c_35845])).

cnf(c_37613,plain,
    ( r2_hidden(sK0(sK7,X0),sK6) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top
    | r1_tarski(sK6,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_34903,c_36221])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_34904,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_55377,plain,
    ( r1_tarski(sK7,sK6) = iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_37613,c_34904])).

cnf(c_55484,plain,
    ( r1_tarski(sK7,sK6) = iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55377])).

cnf(c_35842,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_34899])).

cnf(c_36049,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_35842,c_34896])).

cnf(c_36342,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_34903,c_36049])).

cnf(c_36941,plain,
    ( r2_hidden(sK0(sK6,X0),sK7) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_34903,c_36342])).

cnf(c_50020,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | r1_tarski(sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_36941,c_34904])).

cnf(c_50154,plain,
    ( r1_tarski(sK7,k1_xboole_0) = iProver_top
    | r1_tarski(sK6,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50020])).

cnf(c_20,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_36259,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_19])).

cnf(c_37,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_38,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_36395,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36259,c_37,c_38])).

cnf(c_269,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_36576,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_36395,c_269])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_36581,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_36576,c_3])).

cnf(c_16916,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_16713,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,arAF0_k2_tarski_0_1(X0)))
    | ~ iProver_ARSWP_110 ),
    inference(arg_filter_abstr,[status(unp)],[c_22])).

cnf(c_16900,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,arAF0_k2_tarski_0_1(X0))) != iProver_top
    | iProver_ARSWP_110 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16713])).

cnf(c_17875,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | iProver_ARSWP_110 != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_16900])).

cnf(c_12907,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13023,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_12907])).

cnf(c_17878,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17875,c_13023])).

cnf(c_17883,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16916,c_17878])).

cnf(c_16914,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18174,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17883,c_16914])).

cnf(c_18179,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18174])).

cnf(c_36994,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36581,c_18179])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_37012,plain,
    ( ~ r1_tarski(sK6,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36994,c_26])).

cnf(c_37013,plain,
    ( r1_tarski(sK6,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37012])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_37010,plain,
    ( ~ r1_tarski(sK7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36994,c_25])).

cnf(c_37011,plain,
    ( r1_tarski(sK7,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37010])).

cnf(c_2489,plain,
    ( ~ r1_tarski(sK7,sK6)
    | ~ r1_tarski(sK6,sK7)
    | sK6 = sK7 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2490,plain,
    ( sK6 = sK7
    | r1_tarski(sK7,sK6) != iProver_top
    | r1_tarski(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2489])).

cnf(c_24,negated_conjecture,
    ( sK6 != sK7 ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55484,c_50154,c_37013,c_37011,c_2490,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:02:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 15.37/2.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.37/2.52  
% 15.37/2.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.37/2.52  
% 15.37/2.52  ------  iProver source info
% 15.37/2.52  
% 15.37/2.52  git: date: 2020-06-30 10:37:57 +0100
% 15.37/2.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.37/2.52  git: non_committed_changes: false
% 15.37/2.52  git: last_make_outside_of_git: false
% 15.37/2.52  
% 15.37/2.52  ------ 
% 15.37/2.52  ------ Parsing...
% 15.37/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  ------ Proving...
% 15.37/2.52  ------ Problem Properties 
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  clauses                                 26
% 15.37/2.52  conjectures                             4
% 15.37/2.52  EPR                                     6
% 15.37/2.52  Horn                                    20
% 15.37/2.52  unary                                   9
% 15.37/2.52  binary                                  8
% 15.37/2.52  lits                                    54
% 15.37/2.52  lits eq                                 19
% 15.37/2.52  fd_pure                                 0
% 15.37/2.52  fd_pseudo                               0
% 15.37/2.52  fd_cond                                 1
% 15.37/2.52  fd_pseudo_cond                          6
% 15.37/2.52  AC symbols                              0
% 15.37/2.52  
% 15.37/2.52  ------ Input Options Time Limit: Unbounded
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.37/2.52  Current options:
% 15.37/2.52  ------ 
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.37/2.52  
% 15.37/2.52  ------ Proving...
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  % SZS status Theorem for theBenchmark.p
% 15.37/2.52  
% 15.37/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.37/2.52  
% 15.37/2.52  fof(f1,axiom,(
% 15.37/2.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.37/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.52  
% 15.37/2.52  fof(f11,plain,(
% 15.37/2.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.37/2.52    inference(ennf_transformation,[],[f1])).
% 15.37/2.52  
% 15.37/2.52  fof(f14,plain,(
% 15.37/2.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.37/2.52    inference(nnf_transformation,[],[f11])).
% 15.37/2.52  
% 15.37/2.52  fof(f15,plain,(
% 15.37/2.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.37/2.52    inference(rectify,[],[f14])).
% 15.37/2.52  
% 15.37/2.52  fof(f16,plain,(
% 15.37/2.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.37/2.52    introduced(choice_axiom,[])).
% 15.37/2.52  
% 15.37/2.52  fof(f17,plain,(
% 15.37/2.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.37/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 15.37/2.52  
% 15.37/2.52  fof(f35,plain,(
% 15.37/2.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.37/2.52    inference(cnf_transformation,[],[f17])).
% 15.37/2.52  
% 15.37/2.52  fof(f6,axiom,(
% 15.37/2.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 15.37/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.52  
% 15.37/2.52  fof(f26,plain,(
% 15.37/2.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 15.37/2.52    inference(nnf_transformation,[],[f6])).
% 15.37/2.52  
% 15.37/2.52  fof(f27,plain,(
% 15.37/2.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 15.37/2.52    inference(flattening,[],[f26])).
% 15.37/2.52  
% 15.37/2.52  fof(f52,plain,(
% 15.37/2.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 15.37/2.52    inference(cnf_transformation,[],[f27])).
% 15.37/2.52  
% 15.37/2.52  fof(f9,conjecture,(
% 15.37/2.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.37/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.52  
% 15.37/2.52  fof(f10,negated_conjecture,(
% 15.37/2.52    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.37/2.52    inference(negated_conjecture,[],[f9])).
% 15.37/2.52  
% 15.37/2.52  fof(f12,plain,(
% 15.37/2.52    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 15.37/2.52    inference(ennf_transformation,[],[f10])).
% 15.37/2.52  
% 15.37/2.52  fof(f13,plain,(
% 15.37/2.52    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 15.37/2.52    inference(flattening,[],[f12])).
% 15.37/2.52  
% 15.37/2.52  fof(f32,plain,(
% 15.37/2.52    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK6 != sK7 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6))),
% 15.37/2.52    introduced(choice_axiom,[])).
% 15.37/2.52  
% 15.37/2.52  fof(f33,plain,(
% 15.37/2.52    sK6 != sK7 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6)),
% 15.37/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f13,f32])).
% 15.37/2.52  
% 15.37/2.52  fof(f59,plain,(
% 15.37/2.52    k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6)),
% 15.37/2.52    inference(cnf_transformation,[],[f33])).
% 15.37/2.52  
% 15.37/2.52  fof(f51,plain,(
% 15.37/2.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 15.37/2.52    inference(cnf_transformation,[],[f27])).
% 15.37/2.52  
% 15.37/2.52  fof(f36,plain,(
% 15.37/2.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.37/2.52    inference(cnf_transformation,[],[f17])).
% 15.37/2.52  
% 15.37/2.52  fof(f7,axiom,(
% 15.37/2.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.37/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.52  
% 15.37/2.52  fof(f28,plain,(
% 15.37/2.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.37/2.52    inference(nnf_transformation,[],[f7])).
% 15.37/2.52  
% 15.37/2.52  fof(f29,plain,(
% 15.37/2.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.37/2.52    inference(flattening,[],[f28])).
% 15.37/2.52  
% 15.37/2.52  fof(f53,plain,(
% 15.37/2.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 15.37/2.52    inference(cnf_transformation,[],[f29])).
% 15.37/2.52  
% 15.37/2.52  fof(f54,plain,(
% 15.37/2.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.37/2.52    inference(cnf_transformation,[],[f29])).
% 15.37/2.52  
% 15.37/2.52  fof(f74,plain,(
% 15.37/2.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.37/2.52    inference(equality_resolution,[],[f54])).
% 15.37/2.52  
% 15.37/2.52  fof(f2,axiom,(
% 15.37/2.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.37/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.52  
% 15.37/2.52  fof(f18,plain,(
% 15.37/2.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.37/2.52    inference(nnf_transformation,[],[f2])).
% 15.37/2.52  
% 15.37/2.52  fof(f19,plain,(
% 15.37/2.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.37/2.52    inference(flattening,[],[f18])).
% 15.37/2.52  
% 15.37/2.52  fof(f39,plain,(
% 15.37/2.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.37/2.52    inference(cnf_transformation,[],[f19])).
% 15.37/2.52  
% 15.37/2.52  fof(f3,axiom,(
% 15.37/2.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 15.37/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.52  
% 15.37/2.52  fof(f40,plain,(
% 15.37/2.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 15.37/2.52    inference(cnf_transformation,[],[f3])).
% 15.37/2.52  
% 15.37/2.52  fof(f8,axiom,(
% 15.37/2.52    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 15.37/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.52  
% 15.37/2.52  fof(f30,plain,(
% 15.37/2.52    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 15.37/2.52    inference(nnf_transformation,[],[f8])).
% 15.37/2.52  
% 15.37/2.52  fof(f31,plain,(
% 15.37/2.52    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 15.37/2.52    inference(flattening,[],[f30])).
% 15.37/2.52  
% 15.37/2.52  fof(f57,plain,(
% 15.37/2.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 15.37/2.52    inference(cnf_transformation,[],[f31])).
% 15.37/2.52  
% 15.37/2.52  fof(f4,axiom,(
% 15.37/2.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.37/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.37/2.52  
% 15.37/2.52  fof(f41,plain,(
% 15.37/2.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.37/2.52    inference(cnf_transformation,[],[f4])).
% 15.37/2.52  
% 15.37/2.52  fof(f64,plain,(
% 15.37/2.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 15.37/2.52    inference(definition_unfolding,[],[f57,f41])).
% 15.37/2.52  
% 15.37/2.52  fof(f75,plain,(
% 15.37/2.52    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 15.37/2.52    inference(equality_resolution,[],[f64])).
% 15.37/2.52  
% 15.37/2.52  fof(f60,plain,(
% 15.37/2.52    k1_xboole_0 != sK6),
% 15.37/2.52    inference(cnf_transformation,[],[f33])).
% 15.37/2.52  
% 15.37/2.52  fof(f61,plain,(
% 15.37/2.52    k1_xboole_0 != sK7),
% 15.37/2.52    inference(cnf_transformation,[],[f33])).
% 15.37/2.52  
% 15.37/2.52  fof(f62,plain,(
% 15.37/2.52    sK6 != sK7),
% 15.37/2.52    inference(cnf_transformation,[],[f33])).
% 15.37/2.52  
% 15.37/2.52  cnf(c_1,plain,
% 15.37/2.52      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.37/2.52      inference(cnf_transformation,[],[f35]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_34903,plain,
% 15.37/2.52      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.37/2.52      | r1_tarski(X0,X1) = iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_15,plain,
% 15.37/2.52      ( ~ r2_hidden(X0,X1)
% 15.37/2.52      | ~ r2_hidden(X2,X3)
% 15.37/2.52      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 15.37/2.52      inference(cnf_transformation,[],[f52]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_34899,plain,
% 15.37/2.52      ( r2_hidden(X0,X1) != iProver_top
% 15.37/2.52      | r2_hidden(X2,X3) != iProver_top
% 15.37/2.52      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_27,negated_conjecture,
% 15.37/2.52      ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
% 15.37/2.52      inference(cnf_transformation,[],[f59]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_16,plain,
% 15.37/2.52      ( r2_hidden(X0,X1)
% 15.37/2.52      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 15.37/2.52      inference(cnf_transformation,[],[f51]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_34896,plain,
% 15.37/2.52      ( r2_hidden(X0,X1) = iProver_top
% 15.37/2.52      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_35268,plain,
% 15.37/2.52      ( r2_hidden(X0,sK6) = iProver_top
% 15.37/2.52      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_27,c_34896]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_35845,plain,
% 15.37/2.52      ( r2_hidden(X0,sK7) != iProver_top
% 15.37/2.52      | r2_hidden(X1,sK6) != iProver_top
% 15.37/2.52      | r2_hidden(X0,sK6) = iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_34899,c_35268]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_36221,plain,
% 15.37/2.52      ( r2_hidden(X0,sK6) != iProver_top
% 15.37/2.52      | r2_hidden(sK0(sK7,X1),sK6) = iProver_top
% 15.37/2.52      | r1_tarski(sK7,X1) = iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_34903,c_35845]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_37613,plain,
% 15.37/2.52      ( r2_hidden(sK0(sK7,X0),sK6) = iProver_top
% 15.37/2.52      | r1_tarski(sK7,X0) = iProver_top
% 15.37/2.52      | r1_tarski(sK6,X1) = iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_34903,c_36221]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_0,plain,
% 15.37/2.52      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.37/2.52      inference(cnf_transformation,[],[f36]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_34904,plain,
% 15.37/2.52      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.37/2.52      | r1_tarski(X0,X1) = iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_55377,plain,
% 15.37/2.52      ( r1_tarski(sK7,sK6) = iProver_top
% 15.37/2.52      | r1_tarski(sK6,X0) = iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_37613,c_34904]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_55484,plain,
% 15.37/2.52      ( r1_tarski(sK7,sK6) = iProver_top
% 15.37/2.52      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 15.37/2.52      inference(instantiation,[status(thm)],[c_55377]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_35842,plain,
% 15.37/2.52      ( r2_hidden(X0,sK7) != iProver_top
% 15.37/2.52      | r2_hidden(X1,sK6) != iProver_top
% 15.37/2.52      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK6,sK7)) = iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_27,c_34899]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_36049,plain,
% 15.37/2.52      ( r2_hidden(X0,sK7) != iProver_top
% 15.37/2.52      | r2_hidden(X1,sK7) = iProver_top
% 15.37/2.52      | r2_hidden(X1,sK6) != iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_35842,c_34896]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_36342,plain,
% 15.37/2.52      ( r2_hidden(X0,sK7) = iProver_top
% 15.37/2.52      | r2_hidden(X0,sK6) != iProver_top
% 15.37/2.52      | r1_tarski(sK7,X1) = iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_34903,c_36049]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_36941,plain,
% 15.37/2.52      ( r2_hidden(sK0(sK6,X0),sK7) = iProver_top
% 15.37/2.52      | r1_tarski(sK7,X1) = iProver_top
% 15.37/2.52      | r1_tarski(sK6,X0) = iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_34903,c_36342]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_50020,plain,
% 15.37/2.52      ( r1_tarski(sK7,X0) = iProver_top
% 15.37/2.52      | r1_tarski(sK6,sK7) = iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_36941,c_34904]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_50154,plain,
% 15.37/2.52      ( r1_tarski(sK7,k1_xboole_0) = iProver_top
% 15.37/2.52      | r1_tarski(sK6,sK7) = iProver_top ),
% 15.37/2.52      inference(instantiation,[status(thm)],[c_50020]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_20,plain,
% 15.37/2.52      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.37/2.52      | k1_xboole_0 = X1
% 15.37/2.52      | k1_xboole_0 = X0 ),
% 15.37/2.52      inference(cnf_transformation,[],[f53]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_19,plain,
% 15.37/2.52      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.37/2.52      inference(cnf_transformation,[],[f74]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_36259,plain,
% 15.37/2.52      ( k1_xboole_0 = X0 | k1_xboole_0 = k1_xboole_0 ),
% 15.37/2.52      inference(resolution,[status(thm)],[c_20,c_19]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_37,plain,
% 15.37/2.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.37/2.52      | k1_xboole_0 = k1_xboole_0 ),
% 15.37/2.52      inference(instantiation,[status(thm)],[c_20]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_38,plain,
% 15.37/2.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.37/2.52      inference(instantiation,[status(thm)],[c_19]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_36395,plain,
% 15.37/2.52      ( k1_xboole_0 = k1_xboole_0 ),
% 15.37/2.52      inference(global_propositional_subsumption,
% 15.37/2.52                [status(thm)],
% 15.37/2.52                [c_36259,c_37,c_38]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_269,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_36576,plain,
% 15.37/2.52      ( X0 != k1_xboole_0 | k1_xboole_0 = X0 ),
% 15.37/2.52      inference(resolution,[status(thm)],[c_36395,c_269]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_3,plain,
% 15.37/2.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 15.37/2.52      inference(cnf_transformation,[],[f39]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_36581,plain,
% 15.37/2.52      ( ~ r1_tarski(X0,k1_xboole_0)
% 15.37/2.52      | ~ r1_tarski(k1_xboole_0,X0)
% 15.37/2.52      | k1_xboole_0 = X0 ),
% 15.37/2.52      inference(resolution,[status(thm)],[c_36576,c_3]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_16916,plain,
% 15.37/2.52      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.37/2.52      | r1_tarski(X0,X1) = iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_6,plain,
% 15.37/2.52      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.37/2.52      inference(cnf_transformation,[],[f40]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_22,plain,
% 15.37/2.52      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X0))) ),
% 15.37/2.52      inference(cnf_transformation,[],[f75]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_16713,plain,
% 15.37/2.52      ( ~ r2_hidden(X0,k4_xboole_0(X1,arAF0_k2_tarski_0_1(X0)))
% 15.37/2.52      | ~ iProver_ARSWP_110 ),
% 15.37/2.52      inference(arg_filter_abstr,[status(unp)],[c_22]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_16900,plain,
% 15.37/2.52      ( r2_hidden(X0,k4_xboole_0(X1,arAF0_k2_tarski_0_1(X0))) != iProver_top
% 15.37/2.52      | iProver_ARSWP_110 != iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_16713]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_17875,plain,
% 15.37/2.52      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 15.37/2.52      | iProver_ARSWP_110 != iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_6,c_16900]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_12907,plain,
% 15.37/2.52      ( r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X0))) != iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_13023,plain,
% 15.37/2.52      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_6,c_12907]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_17878,plain,
% 15.37/2.52      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.37/2.52      inference(global_propositional_subsumption,
% 15.37/2.52                [status(thm)],
% 15.37/2.52                [c_17875,c_13023]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_17883,plain,
% 15.37/2.52      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_16916,c_17878]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_16914,plain,
% 15.37/2.52      ( X0 = X1
% 15.37/2.52      | r1_tarski(X1,X0) != iProver_top
% 15.37/2.52      | r1_tarski(X0,X1) != iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_18174,plain,
% 15.37/2.52      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.37/2.52      inference(superposition,[status(thm)],[c_17883,c_16914]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_18179,plain,
% 15.37/2.52      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.37/2.52      inference(predicate_to_equality_rev,[status(thm)],[c_18174]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_36994,plain,
% 15.37/2.52      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.37/2.52      inference(global_propositional_subsumption,
% 15.37/2.52                [status(thm)],
% 15.37/2.52                [c_36581,c_18179]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_26,negated_conjecture,
% 15.37/2.52      ( k1_xboole_0 != sK6 ),
% 15.37/2.52      inference(cnf_transformation,[],[f60]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_37012,plain,
% 15.37/2.52      ( ~ r1_tarski(sK6,k1_xboole_0) ),
% 15.37/2.52      inference(resolution,[status(thm)],[c_36994,c_26]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_37013,plain,
% 15.37/2.52      ( r1_tarski(sK6,k1_xboole_0) != iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_37012]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_25,negated_conjecture,
% 15.37/2.52      ( k1_xboole_0 != sK7 ),
% 15.37/2.52      inference(cnf_transformation,[],[f61]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_37010,plain,
% 15.37/2.52      ( ~ r1_tarski(sK7,k1_xboole_0) ),
% 15.37/2.52      inference(resolution,[status(thm)],[c_36994,c_25]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_37011,plain,
% 15.37/2.52      ( r1_tarski(sK7,k1_xboole_0) != iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_37010]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_2489,plain,
% 15.37/2.52      ( ~ r1_tarski(sK7,sK6) | ~ r1_tarski(sK6,sK7) | sK6 = sK7 ),
% 15.37/2.52      inference(instantiation,[status(thm)],[c_3]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_2490,plain,
% 15.37/2.52      ( sK6 = sK7
% 15.37/2.52      | r1_tarski(sK7,sK6) != iProver_top
% 15.37/2.52      | r1_tarski(sK6,sK7) != iProver_top ),
% 15.37/2.52      inference(predicate_to_equality,[status(thm)],[c_2489]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(c_24,negated_conjecture,
% 15.37/2.52      ( sK6 != sK7 ),
% 15.37/2.52      inference(cnf_transformation,[],[f62]) ).
% 15.37/2.52  
% 15.37/2.52  cnf(contradiction,plain,
% 15.37/2.52      ( $false ),
% 15.37/2.52      inference(minisat,
% 15.37/2.52                [status(thm)],
% 15.37/2.52                [c_55484,c_50154,c_37013,c_37011,c_2490,c_24]) ).
% 15.37/2.52  
% 15.37/2.52  
% 15.37/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.37/2.52  
% 15.37/2.52  ------                               Statistics
% 15.37/2.52  
% 15.37/2.52  ------ Selected
% 15.37/2.52  
% 15.37/2.52  total_time:                             1.628
% 15.37/2.52  
%------------------------------------------------------------------------------
