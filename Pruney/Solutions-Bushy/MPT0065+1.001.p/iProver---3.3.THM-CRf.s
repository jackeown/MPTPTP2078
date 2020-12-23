%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0065+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:23 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   52 (  99 expanded)
%              Number of clauses        :   26 (  30 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 310 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f25,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f12])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f16])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_136,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_368,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_370,plain,
    ( r1_tarski(sK2,sK0)
    | ~ r1_tarski(sK0,sK0)
    | sK2 != sK0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_290,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_326,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_312,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_314,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK2,sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_287,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7,negated_conjecture,
    ( ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,negated_conjecture,
    ( r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_98,plain,
    ( sK1 != sK2
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_5,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_86,plain,
    ( r1_tarski(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_87,plain,
    ( r1_tarski(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_86])).

cnf(c_3,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_76,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_77,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK2 = sK0 ),
    inference(unflattening,[status(thm)],[c_76])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_24,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_21,plain,
    ( r2_xboole_0(sK0,sK0)
    | ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_18,plain,
    ( ~ r2_xboole_0(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_370,c_326,c_314,c_287,c_98,c_87,c_77,c_24,c_21,c_18,c_8])).


%------------------------------------------------------------------------------
