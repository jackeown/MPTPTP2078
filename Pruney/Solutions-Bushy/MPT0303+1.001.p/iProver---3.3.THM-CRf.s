%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0303+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:58 EST 2020

% Result     : Theorem 0.94s
% Output     : CNFRefutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 103 expanded)
%              Number of clauses        :   30 (  39 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  145 ( 348 expanded)
%              Number of equality atoms :   85 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f11,plain,(
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

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f8])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) )
   => ( sK1 != sK2
      & k2_zfmisc_1(sK1,sK1) = k2_zfmisc_1(sK2,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( sK1 != sK2
    & k2_zfmisc_1(sK1,sK1) = k2_zfmisc_1(sK2,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f7,f13])).

fof(f21,plain,(
    k2_zfmisc_1(sK1,sK1) = k2_zfmisc_1(sK2,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f22,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_158,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_162,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,negated_conjecture,
    ( k2_zfmisc_1(sK1,sK1) = k2_zfmisc_1(sK2,sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_161,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_379,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_161])).

cnf(c_458,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_162,c_379])).

cnf(c_609,plain,
    ( sK1 = X0
    | r2_hidden(X1,sK1) != iProver_top
    | r2_hidden(sK0(X0,sK1),X0) = iProver_top
    | r2_hidden(sK0(X0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_158,c_458])).

cnf(c_802,plain,
    ( sK1 = X0
    | sK1 = X1
    | r2_hidden(sK0(X0,sK1),X0) = iProver_top
    | r2_hidden(sK0(X1,sK1),X1) = iProver_top
    | r2_hidden(sK0(X1,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_158,c_609])).

cnf(c_1006,plain,
    ( sK2 = sK1
    | r2_hidden(sK0(sK2,sK1),sK2) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_802])).

cnf(c_1139,plain,
    ( sK2 = sK1
    | r2_hidden(sK0(sK2,sK1),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1006])).

cnf(c_454,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_162])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_160,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_510,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_160])).

cnf(c_634,plain,
    ( sK2 = X0
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(sK0(sK2,X0),X0) = iProver_top
    | r2_hidden(sK0(sK2,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_158,c_510])).

cnf(c_930,plain,
    ( sK2 = X0
    | sK2 = X1
    | r2_hidden(sK0(sK2,X0),X0) = iProver_top
    | r2_hidden(sK0(sK2,X1),X1) = iProver_top
    | r2_hidden(sK0(sK2,X1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_158,c_634])).

cnf(c_953,plain,
    ( sK2 = sK1
    | r2_hidden(sK0(sK2,sK1),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_206,plain,
    ( ~ r2_hidden(sK0(sK2,sK1),sK2)
    | ~ r2_hidden(sK0(sK2,sK1),sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_207,plain,
    ( sK1 = sK2
    | r2_hidden(sK0(sK2,sK1),sK2) != iProver_top
    | r2_hidden(sK0(sK2,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_64,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_204,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_205,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_63,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_70,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_5,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1139,c_953,c_207,c_205,c_70,c_5])).


%------------------------------------------------------------------------------
