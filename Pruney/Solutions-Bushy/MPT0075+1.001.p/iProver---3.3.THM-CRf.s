%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0075+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:24 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 109 expanded)
%              Number of clauses        :   16 (  26 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 371 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f12])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X2,X0)
        & ~ v1_xboole_0(X2) )
   => ( r1_xboole_0(sK2,sK3)
      & r1_tarski(sK4,sK3)
      & r1_tarski(sK4,sK2)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( r1_xboole_0(sK2,sK3)
    & r1_tarski(sK4,sK3)
    & r1_tarski(sK4,sK2)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f18])).

fof(f27,plain,(
    r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    r1_tarski(sK4,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f16])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f14])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_98,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_1,c_6])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK4,sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_109,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_1,c_7])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_152,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2) ),
    inference(resolution,[status(thm)],[c_2,c_5])).

cnf(c_179,plain,
    ( ~ r2_hidden(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_109,c_98,c_152])).

cnf(c_186,plain,
    ( ~ r2_hidden(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_98,c_109,c_152])).

cnf(c_341,plain,
    ( ~ r2_hidden(X0_37,sK4) ),
    inference(subtyping,[status(esa)],[c_186])).

cnf(c_375,plain,
    ( ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_22,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_375,c_22,c_8])).


%------------------------------------------------------------------------------
