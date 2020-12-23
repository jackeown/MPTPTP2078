%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0017+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:11 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 (  83 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f79])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f51,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f215,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f137,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f40])).

fof(f78,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f133,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK13,k2_xboole_0(sK15,sK14))
      & r1_tarski(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f134,plain,
    ( ~ r1_tarski(sK13,k2_xboole_0(sK15,sK14))
    & r1_tarski(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f78,f133])).

fof(f205,plain,(
    ~ r1_tarski(sK13,k2_xboole_0(sK15,sK14)) ),
    inference(cnf_transformation,[],[f134])).

fof(f204,plain,(
    r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_70,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f207])).

cnf(c_3421,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK13,X0)
    | r1_tarski(sK13,X1) ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_4567,plain,
    ( ~ r1_tarski(sK14,X0)
    | r1_tarski(sK13,X0)
    | ~ r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_3421])).

cnf(c_6002,plain,
    ( ~ r1_tarski(sK14,k2_xboole_0(sK14,X0))
    | r1_tarski(sK13,k2_xboole_0(sK14,X0))
    | ~ r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_4567])).

cnf(c_10033,plain,
    ( ~ r1_tarski(sK14,k2_xboole_0(sK14,sK15))
    | r1_tarski(sK13,k2_xboole_0(sK14,sK15))
    | ~ r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_6002])).

cnf(c_78,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f215])).

cnf(c_4244,plain,
    ( r1_tarski(sK14,k2_xboole_0(sK14,X0)) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_9700,plain,
    ( r1_tarski(sK14,k2_xboole_0(sK14,sK15)) ),
    inference(instantiation,[status(thm)],[c_4244])).

cnf(c_1421,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3197,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK13,k2_xboole_0(sK15,sK14))
    | k2_xboole_0(sK15,sK14) != X1
    | sK13 != X0 ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_3547,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(sK14,sK15))
    | r1_tarski(sK13,k2_xboole_0(sK15,sK14))
    | k2_xboole_0(sK15,sK14) != k2_xboole_0(sK14,sK15)
    | sK13 != X0 ),
    inference(instantiation,[status(thm)],[c_3197])).

cnf(c_4266,plain,
    ( ~ r1_tarski(sK13,k2_xboole_0(sK14,sK15))
    | r1_tarski(sK13,k2_xboole_0(sK15,sK14))
    | k2_xboole_0(sK15,sK14) != k2_xboole_0(sK14,sK15)
    | sK13 != sK13 ),
    inference(instantiation,[status(thm)],[c_3547])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_3548,plain,
    ( k2_xboole_0(sK15,sK14) = k2_xboole_0(sK14,sK15) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1416,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3465,plain,
    ( sK13 = sK13 ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_67,negated_conjecture,
    ( ~ r1_tarski(sK13,k2_xboole_0(sK15,sK14)) ),
    inference(cnf_transformation,[],[f205])).

cnf(c_68,negated_conjecture,
    ( r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f204])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10033,c_9700,c_4266,c_3548,c_3465,c_67,c_68])).

%------------------------------------------------------------------------------
