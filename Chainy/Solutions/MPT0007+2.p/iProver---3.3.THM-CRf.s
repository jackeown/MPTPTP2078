%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0007+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:10 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  72 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f61,f62])).

fof(f107,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f36,conjecture,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] : ~ r2_hidden(X1,X0)
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f36])).

fof(f59,plain,(
    ? [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f37])).

fof(f99,plain,
    ( ? [X0] :
        ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 )
   => ( ! [X1] : ~ r2_hidden(X1,sK12)
      & k1_xboole_0 != sK12 ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK12)
    & k1_xboole_0 != sK12 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f59,f99])).

fof(f164,plain,(
    ! [X1] : ~ r2_hidden(X1,sK12) ),
    inference(cnf_transformation,[],[f100])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f138,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f169,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f138,f108])).

fof(f163,plain,(
    k1_xboole_0 != sK12 ),
    inference(cnf_transformation,[],[f100])).

fof(f178,plain,(
    o_0_0_xboole_0 != sK12 ),
    inference(definition_unfolding,[],[f163,f108])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2410,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_60,negated_conjecture,
    ( ~ r2_hidden(X0,sK12) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_2361,plain,
    ( r2_hidden(X0,sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_2927,plain,
    ( v1_xboole_0(sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_2361])).

cnf(c_35,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f169])).

cnf(c_2785,plain,
    ( ~ v1_xboole_0(sK12)
    | o_0_0_xboole_0 = sK12 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2786,plain,
    ( o_0_0_xboole_0 = sK12
    | v1_xboole_0(sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2785])).

cnf(c_61,negated_conjecture,
    ( o_0_0_xboole_0 != sK12 ),
    inference(cnf_transformation,[],[f178])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2927,c_2786,c_61])).

%------------------------------------------------------------------------------
