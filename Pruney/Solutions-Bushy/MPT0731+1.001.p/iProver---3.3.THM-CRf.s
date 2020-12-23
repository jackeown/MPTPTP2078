%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0731+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:00 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,conjecture,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0] : k1_ordinal1(X0) = X0 ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,
    ( ? [X0] : k1_ordinal1(X0) = X0
   => k1_ordinal1(sK0) = sK0 ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    k1_ordinal1(sK0) = sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f11,plain,(
    k1_ordinal1(sK0) = sK0 ),
    inference(cnf_transformation,[],[f8])).

cnf(c_31,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_107,plain,
    ( X0 != X1
    | X0 = k1_ordinal1(X2)
    | k1_ordinal1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_108,plain,
    ( k1_ordinal1(sK0) != sK0
    | sK0 = k1_ordinal1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_96,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_ordinal1(X0))
    | X1 != k1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_98,plain,
    ( ~ r2_hidden(sK0,k1_ordinal1(sK0))
    | r2_hidden(sK0,sK0)
    | sK0 != k1_ordinal1(sK0) ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_30,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_37,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_4,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,negated_conjecture,
    ( k1_ordinal1(sK0) = sK0 ),
    inference(cnf_transformation,[],[f11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_108,c_98,c_37,c_7,c_4,c_2])).


%------------------------------------------------------------------------------
