%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0272+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:53 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 (  76 expanded)
%              Number of equality atoms :   51 (  63 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f14,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f15,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_117,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_175,plain,
    ( k1_tarski(sK0) = k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_118,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_154,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != X0_34
    | k1_tarski(sK0) != X0_34
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_155,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | k1_tarski(sK0) != k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_0,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_40,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_44,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_84,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_44])).

cnf(c_99,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ),
    inference(prop_impl,[status(thm)],[c_84])).

cnf(c_100,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_99])).

cnf(c_113,plain,
    ( k4_xboole_0(k1_tarski(X0_36),X0_35) = k1_tarski(X0_36)
    | k4_xboole_0(k1_tarski(X0_36),X0_35) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_100])).

cnf(c_122,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) = k1_tarski(sK0)
    | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_5,negated_conjecture,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_115,negated_conjecture,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4,negated_conjecture,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_116,negated_conjecture,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_175,c_155,c_122,c_115,c_116])).


%------------------------------------------------------------------------------
