%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0273+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:53 EST 2020

% Result     : Theorem 0.80s
% Output     : CNFRefutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 108 expanded)
%              Number of clauses        :   25 (  35 expanded)
%              Number of leaves         :    3 (  18 expanded)
%              Depth                    :   14
%              Number of atoms          :  150 ( 536 expanded)
%              Number of equality atoms :   90 ( 288 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f5])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(k2_tarski(X1,X1),X2) = k1_tarski(X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f14])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK1,sK2) )
        | r2_hidden(sK0,sK2)
        | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) )
      & ( ( ( sK0 = sK1
            | r2_hidden(sK1,sK2) )
          & ~ r2_hidden(sK0,sK2) )
        | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK1,sK2) )
      | r2_hidden(sK0,sK2)
      | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) )
    & ( ( ( sK0 = sK1
          | r2_hidden(sK1,sK2) )
        & ~ r2_hidden(sK0,sK2) )
      | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f17,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_0,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X0),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_341,plain,
    ( r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK0),sK2) = k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_234,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    | r2_hidden(sK1,sK2) != iProver_top
    | r2_hidden(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_236,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_232,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0)
    | r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_251,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_236,c_232])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k2_tarski(X2,X0),X1) = k1_tarski(X2) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_238,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_287,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_234,c_251,c_238])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | X2 = X0
    | k4_xboole_0(k2_tarski(X2,X0),X1) != k1_tarski(X2) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_237,plain,
    ( X0 = X1
    | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,negated_conjecture,
    ( r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0)
    | sK0 = sK1 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_233,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0)
    | sK0 = sK1
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_266,plain,
    ( sK1 = sK0
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_237,c_233])).

cnf(c_289,plain,
    ( sK1 = sK0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_287,c_266])).

cnf(c_4,negated_conjecture,
    ( r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_235,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    | sK0 != sK1
    | r2_hidden(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_275,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    | sK1 != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_235,c_251])).

cnf(c_292,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK2) != k1_tarski(sK0)
    | sK0 != sK0 ),
    inference(demodulation,[status(thm)],[c_289,c_275])).

cnf(c_294,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK2) != k1_tarski(sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_292])).

cnf(c_298,plain,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_251])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_341,c_294,c_298])).


%------------------------------------------------------------------------------
