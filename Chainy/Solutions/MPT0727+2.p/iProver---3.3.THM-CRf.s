%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0727+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 27.40s
% Output     : CNFRefutation 27.40s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  78 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1077,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f2723,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1077])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1079,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f2109,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1079])).

fof(f2110,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2109])).

fof(f2111,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2112,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK18(X0,X1),X1)
          & r2_hidden(sK18(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f2110,f2111])).

fof(f2731,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2112])).

fof(f1058,conjecture,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1059,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r1_tarski(X1,X0)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f1058])).

fof(f2076,plain,(
    ? [X0,X1] :
      ( r1_tarski(X1,X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1059])).

fof(f2721,plain,
    ( ? [X0,X1] :
        ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) )
   => ( r1_tarski(sK236,sK235)
      & r2_hidden(sK235,sK236) ) ),
    introduced(choice_axiom,[])).

fof(f2722,plain,
    ( r1_tarski(sK236,sK235)
    & r2_hidden(sK235,sK236) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK235,sK236])],[f2076,f2721])).

fof(f4443,plain,(
    r1_tarski(sK236,sK235) ),
    inference(cnf_transformation,[],[f2722])).

fof(f4442,plain,(
    r2_hidden(sK235,sK236) ),
    inference(cnf_transformation,[],[f2722])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f2723])).

cnf(c_98310,plain,
    ( ~ r2_hidden(sK235,sK235) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f2731])).

cnf(c_61713,plain,
    ( ~ r1_tarski(sK236,X0)
    | r2_hidden(sK235,X0)
    | ~ r2_hidden(sK235,sK236) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_74303,plain,
    ( ~ r1_tarski(sK236,sK235)
    | r2_hidden(sK235,sK235)
    | ~ r2_hidden(sK235,sK236) ),
    inference(instantiation,[status(thm)],[c_61713])).

cnf(c_1705,negated_conjecture,
    ( r1_tarski(sK236,sK235) ),
    inference(cnf_transformation,[],[f4443])).

cnf(c_1706,negated_conjecture,
    ( r2_hidden(sK235,sK236) ),
    inference(cnf_transformation,[],[f4442])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_98310,c_74303,c_1705,c_1706])).

%------------------------------------------------------------------------------
