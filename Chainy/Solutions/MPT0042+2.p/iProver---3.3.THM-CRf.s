%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0042+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:14 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 118 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f118,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f117])).

fof(f271,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f68,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f128,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f290,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f128])).

fof(f67,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f127,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f69,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f69])).

fof(f129,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f130,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f129])).

fof(f187,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK16,sK17))
      & r1_tarski(sK17,sK18)
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f188,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK16,sK17))
    & r1_tarski(sK17,sK18)
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18])],[f130,f187])).

fof(f293,plain,(
    ~ r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f188])).

fof(f292,plain,(
    r1_tarski(sK17,sK18) ),
    inference(cnf_transformation,[],[f188])).

fof(f291,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f188])).

cnf(c_80,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f271])).

cnf(c_4265,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(sK16,sK17))
    | ~ r1_tarski(k4_xboole_0(sK15,sK18),X0)
    | r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK16,sK17)) ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_4915,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,X0),k4_xboole_0(sK16,sK17))
    | r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK16,sK17))
    | ~ r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK15,X0)) ),
    inference(instantiation,[status(thm)],[c_4265])).

cnf(c_6538,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK17),k4_xboole_0(sK16,sK17))
    | r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK16,sK17))
    | ~ r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_4915])).

cnf(c_99,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f290])).

cnf(c_4916,plain,
    ( ~ r1_tarski(X0,sK18)
    | r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK15,X0)) ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_5856,plain,
    ( r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK15,sK17))
    | ~ r1_tarski(sK17,sK18) ),
    inference(instantiation,[status(thm)],[c_4916])).

cnf(c_98,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f289])).

cnf(c_4557,plain,
    ( ~ r1_tarski(X0,sK16)
    | r1_tarski(k4_xboole_0(X0,sK17),k4_xboole_0(sK16,sK17)) ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_5280,plain,
    ( r1_tarski(k4_xboole_0(sK15,sK17),k4_xboole_0(sK16,sK17))
    | ~ r1_tarski(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_4557])).

cnf(c_100,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK18),k4_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f293])).

cnf(c_101,negated_conjecture,
    ( r1_tarski(sK17,sK18) ),
    inference(cnf_transformation,[],[f292])).

cnf(c_102,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f291])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6538,c_5856,c_5280,c_100,c_101,c_102])).

%------------------------------------------------------------------------------
