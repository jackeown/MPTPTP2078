%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0067+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:17 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  59 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f98])).

fof(f367,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f165])).

fof(f99,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f166,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f99])).

fof(f167,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f166])).

fof(f368,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f167])).

fof(f102,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f103,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f102])).

fof(f170,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f103])).

fof(f230,plain,
    ( ? [X0,X1] :
        ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) )
   => ( r2_xboole_0(sK16,sK15)
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f231,plain,
    ( r2_xboole_0(sK16,sK15)
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f170,f230])).

fof(f372,plain,(
    r2_xboole_0(sK16,sK15) ),
    inference(cnf_transformation,[],[f231])).

fof(f371,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f231])).

cnf(c_132,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f367])).

cnf(c_5758,plain,
    ( ~ r2_xboole_0(sK16,sK16) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_133,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X2,X0)
    | r2_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f368])).

cnf(c_4964,plain,
    ( ~ r1_tarski(sK15,X0)
    | r2_xboole_0(sK16,X0)
    | ~ r2_xboole_0(sK16,sK15) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_5442,plain,
    ( ~ r1_tarski(sK15,sK16)
    | ~ r2_xboole_0(sK16,sK15)
    | r2_xboole_0(sK16,sK16) ),
    inference(instantiation,[status(thm)],[c_4964])).

cnf(c_136,negated_conjecture,
    ( r2_xboole_0(sK16,sK15) ),
    inference(cnf_transformation,[],[f372])).

cnf(c_137,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f371])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5758,c_5442,c_136,c_137])).

%------------------------------------------------------------------------------
