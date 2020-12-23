%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:54 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 349 expanded)
%              Number of clauses        :   52 ( 114 expanded)
%              Number of leaves         :   15 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          :  226 (1297 expanded)
%              Number of equality atoms :  104 ( 450 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f24,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK4(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f29])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_704,plain,
    ( r2_hidden(sK0(k2_relat_1(X0),X1),X1)
    | r2_hidden(sK4(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | X1 = k2_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_1])).

cnf(c_133,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1458,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_133,c_2])).

cnf(c_131,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2801,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1458,c_131])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_320,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_475,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_320])).

cnf(c_481,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_475])).

cnf(c_2878,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2801,c_481])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3162,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2878,c_9])).

cnf(c_7447,plain,
    ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),X0),X0)
    | ~ v1_relat_1(k1_xboole_0)
    | X0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_704,c_3162])).

cnf(c_7449,plain,
    ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7447])).

cnf(c_2910,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2916,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2910])).

cnf(c_507,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | X0 != sK0(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_1239,plain,
    ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),X0)
    | ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | X0 != k1_xboole_0
    | sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) != sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_2909,plain,
    ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),X0))
    | ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),X0) != k1_xboole_0
    | sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) != sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1239])).

cnf(c_2912,plain,
    ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0))
    | ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) != sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2909])).

cnf(c_2892,plain,
    ( k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_321,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_658,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_321,c_475])).

cnf(c_316,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_638,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_475])).

cnf(c_752,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_638])).

cnf(c_776,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_752])).

cnf(c_850,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_776])).

cnf(c_874,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_850])).

cnf(c_1029,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_874])).

cnf(c_1053,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_1029])).

cnf(c_1422,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_658,c_1053])).

cnf(c_1125,plain,
    ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_1053])).

cnf(c_1423,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_658,c_1125])).

cnf(c_1427,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1422,c_1423])).

cnf(c_1240,plain,
    ( sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) = sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_315,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_439,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_315])).

cnf(c_441,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_439])).

cnf(c_132,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_423,plain,
    ( k1_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_424,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_35,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_34,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7449,c_2916,c_2912,c_2892,c_1427,c_1240,c_441,c_424,c_35,c_34,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:25:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.69/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/1.00  
% 2.69/1.00  ------  iProver source info
% 2.69/1.00  
% 2.69/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.69/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/1.00  git: non_committed_changes: false
% 2.69/1.00  git: last_make_outside_of_git: false
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  ------ Parsing...
% 2.69/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/1.00  ------ Proving...
% 2.69/1.00  ------ Problem Properties 
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  clauses                                 13
% 2.69/1.00  conjectures                             1
% 2.69/1.00  EPR                                     0
% 2.69/1.00  Horn                                    10
% 2.69/1.00  unary                                   4
% 2.69/1.00  binary                                  3
% 2.69/1.00  lits                                    28
% 2.69/1.00  lits eq                                 11
% 2.69/1.00  fd_pure                                 0
% 2.69/1.00  fd_pseudo                               0
% 2.69/1.00  fd_cond                                 1
% 2.69/1.00  fd_pseudo_cond                          4
% 2.69/1.00  AC symbols                              0
% 2.69/1.00  
% 2.69/1.00  ------ Input Options Time Limit: Unbounded
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  Current options:
% 2.69/1.00  ------ 
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ Proving...
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  % SZS status Theorem for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  fof(f6,axiom,(
% 2.69/1.00    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f10,plain,(
% 2.69/1.00    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.69/1.00    inference(ennf_transformation,[],[f6])).
% 2.69/1.00  
% 2.69/1.00  fof(f11,plain,(
% 2.69/1.00    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.69/1.00    inference(flattening,[],[f10])).
% 2.69/1.00  
% 2.69/1.00  fof(f24,plain,(
% 2.69/1.00    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK4(X1),k1_relat_1(X1)))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f25,plain,(
% 2.69/1.00    ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f24])).
% 2.69/1.00  
% 2.69/1.00  fof(f37,plain,(
% 2.69/1.00    ( ! [X0,X1] : (r2_hidden(sK4(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f25])).
% 2.69/1.00  
% 2.69/1.00  fof(f1,axiom,(
% 2.69/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f9,plain,(
% 2.69/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.69/1.00    inference(ennf_transformation,[],[f1])).
% 2.69/1.00  
% 2.69/1.00  fof(f13,plain,(
% 2.69/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.69/1.00    inference(nnf_transformation,[],[f9])).
% 2.69/1.00  
% 2.69/1.00  fof(f14,plain,(
% 2.69/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f15,plain,(
% 2.69/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 2.69/1.00  
% 2.69/1.00  fof(f26,plain,(
% 2.69/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f15])).
% 2.69/1.00  
% 2.69/1.00  fof(f2,axiom,(
% 2.69/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f16,plain,(
% 2.69/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.69/1.00    inference(nnf_transformation,[],[f2])).
% 2.69/1.00  
% 2.69/1.00  fof(f17,plain,(
% 2.69/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.69/1.00    inference(flattening,[],[f16])).
% 2.69/1.00  
% 2.69/1.00  fof(f30,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.69/1.00    inference(cnf_transformation,[],[f17])).
% 2.69/1.00  
% 2.69/1.00  fof(f39,plain,(
% 2.69/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.69/1.00    inference(equality_resolution,[],[f30])).
% 2.69/1.00  
% 2.69/1.00  fof(f3,axiom,(
% 2.69/1.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f31,plain,(
% 2.69/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f3])).
% 2.69/1.00  
% 2.69/1.00  fof(f4,axiom,(
% 2.69/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f18,plain,(
% 2.69/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.69/1.00    inference(nnf_transformation,[],[f4])).
% 2.69/1.00  
% 2.69/1.00  fof(f19,plain,(
% 2.69/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.69/1.00    inference(rectify,[],[f18])).
% 2.69/1.00  
% 2.69/1.00  fof(f22,plain,(
% 2.69/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f21,plain,(
% 2.69/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f20,plain,(
% 2.69/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f23,plain,(
% 2.69/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f32,plain,(
% 2.69/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.69/1.00    inference(cnf_transformation,[],[f23])).
% 2.69/1.00  
% 2.69/1.00  fof(f42,plain,(
% 2.69/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.69/1.00    inference(equality_resolution,[],[f32])).
% 2.69/1.00  
% 2.69/1.00  fof(f5,axiom,(
% 2.69/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f36,plain,(
% 2.69/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f5])).
% 2.69/1.00  
% 2.69/1.00  fof(f29,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.69/1.00    inference(cnf_transformation,[],[f17])).
% 2.69/1.00  
% 2.69/1.00  fof(f40,plain,(
% 2.69/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.69/1.00    inference(equality_resolution,[],[f29])).
% 2.69/1.00  
% 2.69/1.00  fof(f28,plain,(
% 2.69/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 2.69/1.00    inference(cnf_transformation,[],[f17])).
% 2.69/1.00  
% 2.69/1.00  fof(f7,conjecture,(
% 2.69/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f8,negated_conjecture,(
% 2.69/1.00    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 2.69/1.00    inference(negated_conjecture,[],[f7])).
% 2.69/1.00  
% 2.69/1.00  fof(f12,plain,(
% 2.69/1.00    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.69/1.00    inference(ennf_transformation,[],[f8])).
% 2.69/1.00  
% 2.69/1.00  fof(f38,plain,(
% 2.69/1.00    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.69/1.00    inference(cnf_transformation,[],[f12])).
% 2.69/1.00  
% 2.69/1.00  cnf(c_11,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.69/1.00      | r2_hidden(sK4(X1),k1_relat_1(X1))
% 2.69/1.00      | ~ v1_relat_1(X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1,plain,
% 2.69/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f26]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_704,plain,
% 2.69/1.00      ( r2_hidden(sK0(k2_relat_1(X0),X1),X1)
% 2.69/1.00      | r2_hidden(sK4(X0),k1_relat_1(X0))
% 2.69/1.00      | ~ v1_relat_1(X0)
% 2.69/1.00      | X1 = k2_relat_1(X0) ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_11,c_1]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_133,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.69/1.00      theory(equality) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2,plain,
% 2.69/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1458,plain,
% 2.69/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
% 2.69/1.00      | ~ r2_hidden(X2,k1_xboole_0)
% 2.69/1.00      | X0 != X2 ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_133,c_2]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_131,plain,( X0 = X0 ),theory(equality) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2801,plain,
% 2.69/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
% 2.69/1.00      | ~ r2_hidden(X0,k1_xboole_0) ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_1458,c_131]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_5,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_320,plain,
% 2.69/1.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_475,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2,c_320]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_481,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.69/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_475]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2878,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.69/1.00      inference(global_propositional_subsumption,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_2801,c_481]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_9,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.69/1.00      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.69/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3162,plain,
% 2.69/1.00      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_2878,c_9]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_7447,plain,
% 2.69/1.00      ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),X0),X0)
% 2.69/1.00      | ~ v1_relat_1(k1_xboole_0)
% 2.69/1.00      | X0 = k2_relat_1(k1_xboole_0) ),
% 2.69/1.00      inference(resolution,[status(thm)],[c_704,c_3162]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_7449,plain,
% 2.69/1.00      ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 2.69/1.00      | ~ v1_relat_1(k1_xboole_0)
% 2.69/1.00      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_7447]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2910,plain,
% 2.69/1.00      ( ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),X0)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2916,plain,
% 2.69/1.00      ( ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_2910]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_507,plain,
% 2.69/1.00      ( r2_hidden(X0,X1)
% 2.69/1.00      | ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 2.69/1.00      | X0 != sK0(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 2.69/1.00      | X1 != k1_xboole_0 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_133]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1239,plain,
% 2.69/1.00      ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),X0)
% 2.69/1.00      | ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 2.69/1.00      | X0 != k1_xboole_0
% 2.69/1.00      | sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) != sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_507]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2909,plain,
% 2.69/1.00      ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),X0))
% 2.69/1.00      | ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 2.69/1.00      | k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),X0) != k1_xboole_0
% 2.69/1.00      | sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) != sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_1239]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2912,plain,
% 2.69/1.00      ( r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0))
% 2.69/1.00      | ~ r2_hidden(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 2.69/1.00      | k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 2.69/1.00      | sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) != sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_2909]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2892,plain,
% 2.69/1.00      ( k2_zfmisc_1(sK0(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_321,plain,
% 2.69/1.00      ( X0 = X1
% 2.69/1.00      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.69/1.00      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_658,plain,
% 2.69/1.00      ( k1_xboole_0 = X0
% 2.69/1.00      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_321,c_475]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_316,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.69/1.00      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_638,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_316,c_475]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_752,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_xboole_0))) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_316,c_638]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_776,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_316,c_752]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_850,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_316,c_776]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_874,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_316,c_850]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1029,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))))) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_316,c_874]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1053,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))))) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_316,c_1029]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1422,plain,
% 2.69/1.00      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))))) = k1_xboole_0 ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_658,c_1053]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1125,plain,
% 2.69/1.00      ( r2_hidden(X0,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))))))) != iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_316,c_1053]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1423,plain,
% 2.69/1.00      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))))) = k1_xboole_0 ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_658,c_1125]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1427,plain,
% 2.69/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.69/1.00      inference(demodulation,[status(thm)],[c_1422,c_1423]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1240,plain,
% 2.69/1.00      ( sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) = sK0(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_131]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_10,plain,
% 2.69/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_315,plain,
% 2.69/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_439,plain,
% 2.69/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_2,c_315]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_441,plain,
% 2.69/1.00      ( v1_relat_1(k1_xboole_0) ),
% 2.69/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_439]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_132,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_423,plain,
% 2.69/1.00      ( k1_relat_1(k1_xboole_0) != X0
% 2.69/1.00      | k1_xboole_0 != X0
% 2.69/1.00      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_132]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_424,plain,
% 2.69/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.69/1.00      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.69/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_423]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_3,plain,
% 2.69/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_35,plain,
% 2.69/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_4,plain,
% 2.69/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.69/1.00      | k1_xboole_0 = X1
% 2.69/1.00      | k1_xboole_0 = X0 ),
% 2.69/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_34,plain,
% 2.69/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.69/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.69/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_12,negated_conjecture,
% 2.69/1.00      ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
% 2.69/1.00      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.69/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(contradiction,plain,
% 2.69/1.00      ( $false ),
% 2.69/1.00      inference(minisat,
% 2.69/1.00                [status(thm)],
% 2.69/1.00                [c_7449,c_2916,c_2912,c_2892,c_1427,c_1240,c_441,c_424,
% 2.69/1.00                 c_35,c_34,c_12]) ).
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  ------                               Statistics
% 2.69/1.00  
% 2.69/1.00  ------ Selected
% 2.69/1.00  
% 2.69/1.00  total_time:                             0.29
% 2.69/1.00  
%------------------------------------------------------------------------------
