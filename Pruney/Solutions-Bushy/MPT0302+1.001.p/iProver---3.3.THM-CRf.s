%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0302+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:58 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 207 expanded)
%              Number of clauses        :   44 (  75 expanded)
%              Number of leaves         :    9 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  206 ( 722 expanded)
%              Number of equality atoms :  139 ( 394 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f15])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f10])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f8])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK2 != sK3
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( sK2 != sK3
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f17])).

fof(f25,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_189,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_188,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_193,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,negated_conjecture,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_191,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_424,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_191])).

cnf(c_561,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_193,c_424])).

cnf(c_646,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_188,c_561])).

cnf(c_857,plain,
    ( sK3 = k1_xboole_0
    | sK2 = X0
    | r2_hidden(sK0(sK2,X0),X0) = iProver_top
    | r2_hidden(sK0(sK2,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_189,c_646])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_77,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_84,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_78,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_245,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_246,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_256,plain,
    ( ~ r2_hidden(sK0(sK3,sK2),sK3)
    | ~ r2_hidden(sK0(sK3,sK2),sK2)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_257,plain,
    ( sK2 = sK3
    | r2_hidden(sK0(sK3,sK2),sK3) != iProver_top
    | r2_hidden(sK0(sK3,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_248,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_335,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_336,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_648,plain,
    ( sK3 = X0
    | r2_hidden(X1,sK3) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(sK0(sK3,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_189,c_561])).

cnf(c_190,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1181,plain,
    ( sK3 = X0
    | sK3 = X1
    | r2_hidden(sK0(X1,sK3),X1) != iProver_top
    | r2_hidden(sK0(X1,sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_190])).

cnf(c_1201,plain,
    ( sK3 = sK2
    | r2_hidden(sK0(sK3,sK2),sK2) = iProver_top
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1181])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_192,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_483,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_192])).

cnf(c_562,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_193,c_483])).

cnf(c_818,plain,
    ( sK3 = X0
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_189,c_562])).

cnf(c_1208,plain,
    ( sK3 = X0
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_188,c_818])).

cnf(c_1242,plain,
    ( sK3 = sK2
    | sK2 = k1_xboole_0
    | r2_hidden(sK0(sK2,sK3),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1208])).

cnf(c_856,plain,
    ( sK3 = k1_xboole_0
    | sK2 = X0
    | r2_hidden(sK0(X0,sK2),X0) = iProver_top
    | r2_hidden(sK0(X0,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_189,c_646])).

cnf(c_1920,plain,
    ( sK3 = sK2
    | sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK2),sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_856])).

cnf(c_1922,plain,
    ( sK3 = sK2
    | sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,sK2),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1920])).

cnf(c_2357,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_857,c_8,c_6,c_84,c_246,c_257,c_335,c_336,c_1201,c_1242,c_1922])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2372,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2357,c_7])).

cnf(c_2376,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2372])).


%------------------------------------------------------------------------------
