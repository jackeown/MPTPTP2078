%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0245+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:48 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   21 (  33 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 (  91 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f4])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
          | r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        & ~ r2_hidden(X2,X0)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
      & ~ r2_hidden(sK2,sK0)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    & ~ r2_hidden(sK2,sK0)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f12,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_0,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X1,k4_xboole_0(X2,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_2,negated_conjecture,
    ( ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_38,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k4_xboole_0(X0,k1_tarski(sK2))) ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_71,plain,
    ( ~ r1_tarski(sK0,X0_36)
    | r1_tarski(sK0,k4_xboole_0(X0_36,k1_tarski(sK2))) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_77,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_1,negated_conjecture,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_3,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_77,c_1,c_3])).


%------------------------------------------------------------------------------
