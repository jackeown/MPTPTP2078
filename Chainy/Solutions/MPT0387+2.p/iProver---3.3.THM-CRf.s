%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0387+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 14.86s
% Output     : CNFRefutation 14.86s
% Verified   : 
% Statistics : Number of formulae       :   25 (  36 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  61 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f554,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f914,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f554])).

fof(f2111,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f914])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f627,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f1379,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f627])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1240,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2214,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f1379,f1240,f1240])).

fof(f556,conjecture,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f557,negated_conjecture,(
    ~ ! [X0] :
        ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(negated_conjecture,[],[f556])).

fof(f917,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_setfam_1(X0)
      & r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f557])).

fof(f1231,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_setfam_1(X0)
        & r2_hidden(k1_xboole_0,X0) )
   => ( k1_xboole_0 != k1_setfam_1(sK96)
      & r2_hidden(k1_xboole_0,sK96) ) ),
    introduced(choice_axiom,[])).

fof(f1232,plain,
    ( k1_xboole_0 != k1_setfam_1(sK96)
    & r2_hidden(k1_xboole_0,sK96) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK96])],[f917,f1231])).

fof(f2114,plain,(
    k1_xboole_0 != k1_setfam_1(sK96) ),
    inference(cnf_transformation,[],[f1232])).

fof(f2581,plain,(
    o_0_0_xboole_0 != k1_setfam_1(sK96) ),
    inference(definition_unfolding,[],[f2114,f1240])).

fof(f2113,plain,(
    r2_hidden(k1_xboole_0,sK96) ),
    inference(cnf_transformation,[],[f1232])).

fof(f2582,plain,(
    r2_hidden(o_0_0_xboole_0,sK96) ),
    inference(definition_unfolding,[],[f2113,f1240])).

cnf(c_864,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f2111])).

cnf(c_43526,plain,
    ( r1_tarski(k1_setfam_1(sK96),o_0_0_xboole_0)
    | ~ r2_hidden(o_0_0_xboole_0,sK96) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f2214])).

cnf(c_43111,plain,
    ( ~ r1_tarski(k1_setfam_1(sK96),o_0_0_xboole_0)
    | o_0_0_xboole_0 = k1_setfam_1(sK96) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_866,negated_conjecture,
    ( o_0_0_xboole_0 != k1_setfam_1(sK96) ),
    inference(cnf_transformation,[],[f2581])).

cnf(c_867,negated_conjecture,
    ( r2_hidden(o_0_0_xboole_0,sK96) ),
    inference(cnf_transformation,[],[f2582])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43526,c_43111,c_866,c_867])).

%------------------------------------------------------------------------------
