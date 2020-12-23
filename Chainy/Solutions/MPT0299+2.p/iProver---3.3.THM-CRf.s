%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0299+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:34 EST 2020

% Result     : Theorem 11.59s
% Output     : CNFRefutation 11.59s
% Verified   : 
% Statistics : Number of formulae       :   27 (  38 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 103 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f712,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f316])).

fof(f713,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f712])).

fof(f1181,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f713])).

fof(f317,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
     => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f318,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
       => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    inference(negated_conjecture,[],[f317])).

fof(f531,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f318])).

fof(f714,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
        & r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ~ r2_hidden(k4_tarski(sK41,sK40),k2_zfmisc_1(sK43,sK42))
      & r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) ) ),
    introduced(choice_axiom,[])).

fof(f715,plain,
    ( ~ r2_hidden(k4_tarski(sK41,sK40),k2_zfmisc_1(sK43,sK42))
    & r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK40,sK41,sK42,sK43])],[f531,f714])).

fof(f1183,plain,(
    ~ r2_hidden(k4_tarski(sK41,sK40),k2_zfmisc_1(sK43,sK42)) ),
    inference(cnf_transformation,[],[f715])).

fof(f1179,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f713])).

fof(f1180,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f713])).

fof(f1182,plain,(
    r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) ),
    inference(cnf_transformation,[],[f715])).

cnf(c_422,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1181])).

cnf(c_12292,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_425,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK41,sK40),k2_zfmisc_1(sK43,sK42)) ),
    inference(cnf_transformation,[],[f1183])).

cnf(c_12278,plain,
    ( r2_hidden(k4_tarski(sK41,sK40),k2_zfmisc_1(sK43,sK42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_24611,plain,
    ( r2_hidden(sK40,sK42) != iProver_top
    | r2_hidden(sK41,sK43) != iProver_top ),
    inference(superposition,[status(thm)],[c_12292,c_12278])).

cnf(c_424,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1179])).

cnf(c_15707,plain,
    ( ~ r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43))
    | r2_hidden(sK40,sK42) ),
    inference(instantiation,[status(thm)],[c_424])).

cnf(c_15708,plain,
    ( r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) != iProver_top
    | r2_hidden(sK40,sK42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15707])).

cnf(c_423,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f1180])).

cnf(c_15703,plain,
    ( ~ r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43))
    | r2_hidden(sK41,sK43) ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_15704,plain,
    ( r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) != iProver_top
    | r2_hidden(sK41,sK43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15703])).

cnf(c_426,negated_conjecture,
    ( r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) ),
    inference(cnf_transformation,[],[f1182])).

cnf(c_549,plain,
    ( r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24611,c_15708,c_15704,c_549])).

%------------------------------------------------------------------------------
