%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0258+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:51 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   28 (  40 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 112 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f8])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k2_tarski(X0,X2)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k2_tarski(X0,X2)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k2_tarski(X0,X2)
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK0,sK2),sK1) != k2_tarski(sK0,sK2)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( k3_xboole_0(k2_tarski(sK0,sK2),sK1) != k2_tarski(sK0,sK2)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f18,plain,(
    k3_xboole_0(k2_tarski(sK0,sK2),sK1) != k2_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_115,plain,
    ( ~ r2_hidden(X0_35,X0_36)
    | ~ r2_hidden(X1_35,X0_36)
    | r1_tarski(k2_tarski(X1_35,X0_35),X0_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_304,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK0,sK1)
    | r1_tarski(k2_tarski(sK0,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_116,plain,
    ( ~ r1_tarski(X0_37,X0_36)
    | k3_xboole_0(X0_37,X0_36) = X0_37 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_282,plain,
    ( ~ r1_tarski(k2_tarski(X0_35,X1_35),X0_36)
    | k3_xboole_0(k2_tarski(X0_35,X1_35),X0_36) = k2_tarski(X0_35,X1_35) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_296,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK2),sK1)
    | k3_xboole_0(k2_tarski(sK0,sK2),sK1) = k2_tarski(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_4,negated_conjecture,
    ( k3_xboole_0(k2_tarski(sK0,sK2),sK1) != k2_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_112,negated_conjecture,
    ( k3_xboole_0(k2_tarski(sK0,sK2),sK1) != k2_tarski(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_304,c_296,c_112,c_5,c_6])).


%------------------------------------------------------------------------------
