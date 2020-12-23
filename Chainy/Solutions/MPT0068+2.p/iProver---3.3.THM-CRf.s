%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0068+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:17 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   25 (  34 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  66 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f336,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f66])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f241,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f429,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f336,f241])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f203,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f203])).

fof(f268,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f204])).

fof(f103,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f104,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => r2_xboole_0(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f103])).

fof(f172,plain,(
    ? [X0] :
      ( ~ r2_xboole_0(k1_xboole_0,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f104])).

fof(f232,plain,
    ( ? [X0] :
        ( ~ r2_xboole_0(k1_xboole_0,X0)
        & k1_xboole_0 != X0 )
   => ( ~ r2_xboole_0(k1_xboole_0,sK15)
      & k1_xboole_0 != sK15 ) ),
    introduced(choice_axiom,[])).

fof(f233,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK15)
    & k1_xboole_0 != sK15 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f172,f232])).

fof(f375,plain,(
    ~ r2_xboole_0(k1_xboole_0,sK15) ),
    inference(cnf_transformation,[],[f233])).

fof(f447,plain,(
    ~ r2_xboole_0(o_0_0_xboole_0,sK15) ),
    inference(definition_unfolding,[],[f375,f241])).

fof(f374,plain,(
    k1_xboole_0 != sK15 ),
    inference(cnf_transformation,[],[f233])).

fof(f448,plain,(
    o_0_0_xboole_0 != sK15 ),
    inference(definition_unfolding,[],[f374,f241])).

cnf(c_100,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f429])).

cnf(c_5376,plain,
    ( r1_tarski(o_0_0_xboole_0,sK15) ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f268])).

cnf(c_4979,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK15)
    | r2_xboole_0(o_0_0_xboole_0,sK15)
    | o_0_0_xboole_0 = sK15 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_137,negated_conjecture,
    ( ~ r2_xboole_0(o_0_0_xboole_0,sK15) ),
    inference(cnf_transformation,[],[f447])).

cnf(c_138,negated_conjecture,
    ( o_0_0_xboole_0 != sK15 ),
    inference(cnf_transformation,[],[f448])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5376,c_4979,c_137,c_138])).

%------------------------------------------------------------------------------
