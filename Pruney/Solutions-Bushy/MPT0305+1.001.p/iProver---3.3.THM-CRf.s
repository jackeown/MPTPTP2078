%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0305+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:58 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 248 expanded)
%              Number of clauses        :   44 (  92 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :   23
%              Number of atoms          :  216 ( 868 expanded)
%              Number of equality atoms :  113 ( 249 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
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

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f9])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 )
   => ( ~ r1_tarski(sK3,sK4)
      & ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4))
        | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) )
      & k1_xboole_0 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_tarski(sK3,sK4)
    & ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4))
      | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) )
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f17])).

fof(f27,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4))
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_286,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_281,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4))
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_279,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_284,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_285,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_673,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
    | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_285])).

cnf(c_1279,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK4)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_279,c_673])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_283,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1546,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_283])).

cnf(c_1578,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_281,c_1546])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_106,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_360,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_391,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_105,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_392,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_1934,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1578,c_9,c_391,c_392])).

cnf(c_767,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_281,c_285])).

cnf(c_974,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_767,c_285])).

cnf(c_2385,plain,
    ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(sK3,sK2)),X1) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1934,c_974])).

cnf(c_4287,plain,
    ( k2_zfmisc_1(sK3,sK2) = k1_xboole_0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(sK3,sK2)),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK2),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_285])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,plain,
    ( r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1943,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X2,sK3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1934,c_673])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_282,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4237,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X2,sK4) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1943,c_282])).

cnf(c_4620,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_281,c_4237])).

cnf(c_4700,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4620,c_9,c_391,c_392])).

cnf(c_4710,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK0(sK3,X1),sK4) = iProver_top
    | r1_tarski(sK3,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_286,c_4700])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_287,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5340,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4710,c_287])).

cnf(c_5872,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4287,c_11,c_5340])).

cnf(c_5873,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5872])).

cnf(c_5878,plain,
    ( r2_hidden(sK0(sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_286,c_5873])).

cnf(c_6186,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5878,c_287])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6186,c_11])).


%------------------------------------------------------------------------------
