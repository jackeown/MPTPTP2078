%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0321+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:00 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 743 expanded)
%              Number of clauses        :   67 ( 214 expanded)
%              Number of leaves         :   11 ( 180 expanded)
%              Depth                    :   18
%              Number of atoms          :  294 (2259 expanded)
%              Number of equality atoms :  224 (1678 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f19])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f32,f23])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f10])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK3 != sK5
        | sK2 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( sK3 != sK5
      | sK2 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f11,f21])).

fof(f33,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f34,f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f23,f23,f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f28,f23,f23])).

fof(f44,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f35,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    o_0_0_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f35,f23])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,
    ( sK3 != sK5
    | sK2 != sK4 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_193,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_198,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12,negated_conjecture,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_197,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_740,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_197])).

cnf(c_1016,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_198,c_740])).

cnf(c_1154,plain,
    ( sK2 = o_0_0_xboole_0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_193,c_1016])).

cnf(c_11,negated_conjecture,
    ( o_0_0_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_83,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_276,plain,
    ( sK2 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_277,plain,
    ( sK2 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_1735,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1154,c_11,c_22,c_23,c_277])).

cnf(c_1743,plain,
    ( sK3 = o_0_0_xboole_0
    | r2_hidden(sK1(sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_193,c_1735])).

cnf(c_10,negated_conjecture,
    ( o_0_0_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_274,plain,
    ( sK3 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_275,plain,
    ( sK3 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_1770,plain,
    ( r2_hidden(sK1(sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1743,c_10,c_22,c_23,c_275])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_196,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_453,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_196])).

cnf(c_1015,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_198,c_453])).

cnf(c_1146,plain,
    ( sK2 = o_0_0_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_193,c_1015])).

cnf(c_2159,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(sK2),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1146,c_11,c_22,c_23,c_277])).

cnf(c_2167,plain,
    ( sK3 = o_0_0_xboole_0
    | r2_hidden(sK1(sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_193,c_2159])).

cnf(c_2571,plain,
    ( r2_hidden(sK1(sK2),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2167,c_10,c_22,c_23,c_275])).

cnf(c_1012,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_198])).

cnf(c_1064,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_197])).

cnf(c_2580,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2571,c_1064])).

cnf(c_2991,plain,
    ( r2_hidden(sK1(sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_2580])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_194,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1400,plain,
    ( sK2 = X0
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(sK0(X0,sK2),X0) = iProver_top
    | r2_hidden(sK0(X0,sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_194,c_1015])).

cnf(c_3628,plain,
    ( sK2 = X0
    | r2_hidden(sK0(X0,sK2),X0) = iProver_top
    | r2_hidden(sK0(X0,sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2991,c_1400])).

cnf(c_16985,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK4,sK2),sK4) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3628])).

cnf(c_16987,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK4,sK2),sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_16985])).

cnf(c_1065,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_196])).

cnf(c_1873,plain,
    ( sK4 = X0
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(sK0(sK4,X0),X0) = iProver_top
    | r2_hidden(sK0(sK4,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_194,c_1065])).

cnf(c_3548,plain,
    ( sK4 = X0
    | r2_hidden(sK0(sK4,X0),X0) = iProver_top
    | r2_hidden(sK0(sK4,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_1873])).

cnf(c_16612,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK4,sK2),sK2) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3548])).

cnf(c_16614,plain,
    ( sK4 = sK2
    | r2_hidden(sK0(sK4,sK2),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_16612])).

cnf(c_2990,plain,
    ( sK5 = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | r2_hidden(sK0(sK5,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_194,c_2580])).

cnf(c_10205,plain,
    ( sK5 = sK3
    | r2_hidden(sK0(sK5,sK3),sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2990])).

cnf(c_10207,plain,
    ( sK5 = sK3
    | r2_hidden(sK0(sK5,sK3),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10205])).

cnf(c_1744,plain,
    ( sK3 = X0
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_194,c_1735])).

cnf(c_4615,plain,
    ( sK5 = sK3
    | r2_hidden(sK0(sK5,sK3),sK5) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1744])).

cnf(c_4617,plain,
    ( sK5 = sK3
    | r2_hidden(sK0(sK5,sK3),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4615])).

cnf(c_321,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_2143,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_272,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_1127,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_82,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_442,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_412,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_316,plain,
    ( ~ r2_hidden(sK0(sK5,sK3),sK5)
    | ~ r2_hidden(sK0(sK5,sK3),sK3)
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_317,plain,
    ( sK3 = sK5
    | r2_hidden(sK0(sK5,sK3),sK5) != iProver_top
    | r2_hidden(sK0(sK5,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_278,plain,
    ( ~ r2_hidden(sK0(sK4,sK2),sK4)
    | ~ r2_hidden(sK0(sK4,sK2),sK2)
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_279,plain,
    ( sK2 = sK4
    | r2_hidden(sK0(sK4,sK2),sK4) != iProver_top
    | r2_hidden(sK0(sK4,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_9,negated_conjecture,
    ( sK2 != sK4
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16987,c_16614,c_10207,c_4617,c_2143,c_1127,c_442,c_412,c_317,c_279,c_9])).


%------------------------------------------------------------------------------
