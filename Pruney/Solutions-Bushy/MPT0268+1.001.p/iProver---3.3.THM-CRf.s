%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0268+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   47 (  76 expanded)
%              Number of clauses        :   26 (  34 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 191 expanded)
%              Number of equality atoms :   42 (  74 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 )
      & ( ~ r2_hidden(sK1,sK0)
        | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ( r2_hidden(sK1,sK0)
      | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 )
    & ( ~ r2_hidden(sK1,sK0)
      | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f21,plain,
    ( r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_468,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),sK0)
    | r1_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_427,plain,
    ( ~ r1_xboole_0(sK0,k1_tarski(sK1))
    | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_428,plain,
    ( r1_xboole_0(k1_tarski(sK1),sK0)
    | ~ r1_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_429,plain,
    ( r1_xboole_0(k1_tarski(sK1),sK0) = iProver_top
    | r1_xboole_0(sK0,k1_tarski(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_409,plain,
    ( r1_xboole_0(sK0,k1_tarski(sK1))
    | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_410,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) != sK0
    | r1_xboole_0(sK0,k1_tarski(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_57,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_58,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_57])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_65,plain,
    ( r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_128,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_58,c_65])).

cnf(c_129,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_130,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) != sK0
    | r1_xboole_0(k1_tarski(sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_129])).

cnf(c_1,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_59,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_60,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_59])).

cnf(c_6,negated_conjecture,
    ( ~ r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_67,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_118,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_60,c_67])).

cnf(c_119,plain,
    ( r1_xboole_0(k1_tarski(sK1),sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ),
    inference(unflattening,[status(thm)],[c_118])).

cnf(c_120,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) = sK0
    | r1_xboole_0(k1_tarski(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_119])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_468,c_427,c_429,c_410,c_130,c_120,c_119])).


%------------------------------------------------------------------------------
