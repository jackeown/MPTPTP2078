%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0122+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:32 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   26 (  36 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  76 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,
    ( ? [X0] : r2_xboole_0(X0,k1_xboole_0)
   => r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f14])).

fof(f23,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f17])).

cnf(c_7,negated_conjecture,
    ( r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_65,plain,
    ( ~ r2_xboole_0(X0,X1)
    | X2 != X0
    | k1_xboole_0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_66,plain,
    ( ~ r2_xboole_0(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_65])).

cnf(c_83,plain,
    ( sK0 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_66])).

cnf(c_84,plain,
    ( k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_83])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_78,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_79,plain,
    ( k1_xboole_0 != sK0 ),
    inference(unflattening,[status(thm)],[c_78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_84,c_79])).


%------------------------------------------------------------------------------
