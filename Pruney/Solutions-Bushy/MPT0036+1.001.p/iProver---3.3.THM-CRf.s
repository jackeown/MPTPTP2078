%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0036+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:18 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,
    ( ? [X0,X1,X2] : ~ r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))
   => ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f14,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_42,plain,
    ( ~ r1_tarski(X0_34,X1_34)
    | ~ r1_tarski(X2_34,X0_34)
    | r1_tarski(X2_34,X1_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_64,plain,
    ( ~ r1_tarski(X0_34,X1_34)
    | ~ r1_tarski(X1_34,k2_xboole_0(X1_34,X0_36))
    | r1_tarski(X0_34,k2_xboole_0(X1_34,X0_36)) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_72,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ r1_tarski(sK0,k2_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_2,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_41,plain,
    ( r1_tarski(X0_34,k2_xboole_0(X0_34,X0_36)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_49,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_0,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_43,plain,
    ( r1_tarski(k3_xboole_0(X0_34,X0_35),X0_34) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_45,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_3,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_72,c_49,c_45,c_3])).


%------------------------------------------------------------------------------
