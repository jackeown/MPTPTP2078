%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0298+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:34 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :   31 (  51 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 207 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f317,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f316])).

fof(f530,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <~> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f317])).

fof(f711,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f530])).

fof(f712,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f711])).

fof(f713,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) )
        & ( ( r2_hidden(X1,X3)
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) )
   => ( ( ~ r2_hidden(sK41,sK43)
        | ~ r2_hidden(sK40,sK42)
        | ~ r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) )
      & ( ( r2_hidden(sK41,sK43)
          & r2_hidden(sK40,sK42) )
        | r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) ) ) ),
    introduced(choice_axiom,[])).

fof(f714,plain,
    ( ( ~ r2_hidden(sK41,sK43)
      | ~ r2_hidden(sK40,sK42)
      | ~ r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) )
    & ( ( r2_hidden(sK41,sK43)
        & r2_hidden(sK40,sK42) )
      | r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK40,sK41,sK42,sK43])],[f712,f713])).

fof(f1180,plain,
    ( ~ r2_hidden(sK41,sK43)
    | ~ r2_hidden(sK40,sK42)
    | ~ r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) ),
    inference(cnf_transformation,[],[f714])).

fof(f310,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f703,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f310])).

fof(f704,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f703])).

fof(f1164,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f704])).

fof(f1179,plain,
    ( r2_hidden(sK41,sK43)
    | r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) ),
    inference(cnf_transformation,[],[f714])).

fof(f1163,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f704])).

fof(f1178,plain,
    ( r2_hidden(sK40,sK42)
    | r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) ),
    inference(cnf_transformation,[],[f714])).

fof(f1165,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f704])).

cnf(c_422,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43))
    | ~ r2_hidden(sK40,sK42)
    | ~ r2_hidden(sK41,sK43) ),
    inference(cnf_transformation,[],[f1180])).

cnf(c_15961,plain,
    ( r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) != iProver_top
    | r2_hidden(sK40,sK42) != iProver_top
    | r2_hidden(sK41,sK43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_408,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f1164])).

cnf(c_15974,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_423,negated_conjecture,
    ( r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43))
    | r2_hidden(sK41,sK43) ),
    inference(cnf_transformation,[],[f1179])).

cnf(c_15960,plain,
    ( r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) = iProver_top
    | r2_hidden(sK41,sK43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_16713,plain,
    ( r2_hidden(sK41,sK43) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_15974,c_15960])).

cnf(c_409,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1163])).

cnf(c_15973,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_424,negated_conjecture,
    ( r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43))
    | r2_hidden(sK40,sK42) ),
    inference(cnf_transformation,[],[f1178])).

cnf(c_15959,plain,
    ( r2_hidden(k4_tarski(sK40,sK41),k2_zfmisc_1(sK42,sK43)) = iProver_top
    | r2_hidden(sK40,sK42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_16706,plain,
    ( r2_hidden(sK40,sK42) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_15973,c_15959])).

cnf(c_407,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1165])).

cnf(c_15975,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_17189,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15961,c_16713,c_16706,c_15975])).

%------------------------------------------------------------------------------
