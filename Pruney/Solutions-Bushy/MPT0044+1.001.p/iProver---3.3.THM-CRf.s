%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:19 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  91 expanded)
%              Number of equality atoms :   36 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
      <=> r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <~> r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(X0,X1)
          | k4_xboole_0(X0,X1) != k1_xboole_0 )
        & ( r1_tarski(X0,X1)
          | k4_xboole_0(X0,X1) = k1_xboole_0 ) )
   => ( ( ~ r1_tarski(sK0,sK1)
        | k4_xboole_0(sK0,sK1) != k1_xboole_0 )
      & ( r1_tarski(sK0,sK1)
        | k4_xboole_0(sK0,sK1) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ( ~ r1_tarski(sK0,sK1)
      | k4_xboole_0(sK0,sK1) != k1_xboole_0 )
    & ( r1_tarski(sK0,sK1)
      | k4_xboole_0(sK0,sK1) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f11,plain,
    ( r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_34,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_3,negated_conjecture,
    ( r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_38,plain,
    ( r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_76,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | k4_xboole_0(sK0,sK1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_38])).

cnf(c_77,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_76])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_32,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_2,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_36,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_71,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k4_xboole_0(sK0,sK1) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_36])).

cnf(c_72,plain,
    ( k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_77,c_72])).


%------------------------------------------------------------------------------
