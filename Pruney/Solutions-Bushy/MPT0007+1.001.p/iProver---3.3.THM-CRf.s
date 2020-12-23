%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0007+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:14 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f9])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] : ~ r2_hidden(X1,X0)
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,
    ( ? [X0] :
        ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 )
   => ( ! [X1] : ~ r2_hidden(X1,sK1)
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f11])).

fof(f16,plain,(
    ! [X1] : ~ r2_hidden(X1,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_2,negated_conjecture,
    ( ~ r2_hidden(X0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_40,plain,
    ( v1_xboole_0(X0)
    | sK0(X0) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_41,plain,
    ( v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_40])).

cnf(c_49,plain,
    ( sK1 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_41])).

cnf(c_50,plain,
    ( k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_49])).

cnf(c_3,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50,c_3])).


%------------------------------------------------------------------------------
