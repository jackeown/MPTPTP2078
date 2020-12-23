%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0326+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:01 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 184 expanded)
%              Number of clauses        :   37 (  71 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 ( 534 expanded)
%              Number of equality atoms :   96 ( 196 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
     => ( ~ r1_tarski(sK1,sK3)
        & ( r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,sK2))
          | r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(sK2,sK3)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r1_tarski(sK1,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14,f13])).

fof(f25,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f8])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(definition_unfolding,[],[f21,f16])).

fof(f26,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f24,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f16,f16,f16])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(definition_unfolding,[],[f22,f16])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f23,f16])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_212,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
    | k2_zfmisc_1(X0,X2) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_215,plain,
    ( k2_zfmisc_1(X0,X1) = o_0_0_xboole_0
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_366,plain,
    ( k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) = iProver_top
    | r1_tarski(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_212,c_215])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,plain,
    ( r1_tarski(sK1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_77,plain,
    ( sK0 != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_273,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,sK3)
    | sK3 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_279,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(sK1,sK3)
    | sK3 != sK3
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_282,plain,
    ( r1_tarski(sK1,sK3)
    | ~ r1_tarski(o_0_0_xboole_0,sK3)
    | sK3 != sK3
    | sK1 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_119,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_280,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_120,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_278,plain,
    ( sK0 != X0
    | sK0 = o_0_0_xboole_0
    | o_0_0_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_286,plain,
    ( sK0 != sK0
    | sK0 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_287,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_295,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_314,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_316,plain,
    ( sK1 != sK1
    | sK1 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_315,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_344,plain,
    ( k2_zfmisc_1(X0,sK1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_403,plain,
    ( k2_zfmisc_1(sK0,sK1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))
    | k2_zfmisc_1(X2,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_216,plain,
    ( k2_zfmisc_1(X0,X1) = o_0_0_xboole_0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X3,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_447,plain,
    ( k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) = iProver_top
    | r1_tarski(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_212,c_216])).

cnf(c_6,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_541,plain,
    ( r1_tarski(o_0_0_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_560,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_7,c_12,c_77,c_282,c_280,c_286,c_287,c_316,c_315,c_403,c_447,c_541])).

cnf(c_566,plain,
    ( k2_zfmisc_1(sK1,sK0) = o_0_0_xboole_0
    | r1_tarski(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_560,c_215])).

cnf(c_301,plain,
    ( k2_zfmisc_1(X0,sK0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_395,plain,
    ( k2_zfmisc_1(sK1,sK0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_566,c_541,c_395,c_315,c_316,c_287,c_286,c_280,c_282,c_77,c_12,c_7])).


%------------------------------------------------------------------------------
