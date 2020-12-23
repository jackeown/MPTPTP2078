%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:46 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 142 expanded)
%              Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  273 ( 470 expanded)
%              Number of equality atoms :  128 ( 229 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f57,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f52,f52])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK2,sK3)
      & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r2_hidden(sK2,sK3)
    & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f26])).

fof(f50,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f64,plain,(
    r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(definition_unfolding,[],[f50,f53,f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f70,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f71,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f70])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f72,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f73,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f51,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4522,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4625,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11,c_4522])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4529,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5043,plain,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = sK3
    | r1_tarski(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4625,c_4529])).

cnf(c_10,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4527,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5402,plain,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5043,c_4527])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4526,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4532,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5993,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)) = iProver_top
    | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_4532])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4531,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6433,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_enumset1(X3,X3,X3,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5993,c_4531])).

cnf(c_6765,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_6433])).

cnf(c_6870,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5402,c_6765])).

cnf(c_6884,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6870])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_30,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6884,c_30,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.54/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.98  
% 3.54/0.98  ------  iProver source info
% 3.54/0.98  
% 3.54/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.98  git: non_committed_changes: false
% 3.54/0.98  git: last_make_outside_of_git: false
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  ------ Parsing...
% 3.54/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  ------ Proving...
% 3.54/0.98  ------ Problem Properties 
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  clauses                                 19
% 3.54/0.98  conjectures                             3
% 3.54/0.98  EPR                                     3
% 3.54/0.98  Horn                                    13
% 3.54/0.98  unary                                   8
% 3.54/0.98  binary                                  2
% 3.54/0.98  lits                                    41
% 3.54/0.98  lits eq                                 15
% 3.54/0.98  fd_pure                                 0
% 3.54/0.98  fd_pseudo                               0
% 3.54/0.98  fd_cond                                 0
% 3.54/0.98  fd_pseudo_cond                          7
% 3.54/0.98  AC symbols                              0
% 3.54/0.98  
% 3.54/0.98  ------ Input Options Time Limit: Unbounded
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing...
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.54/0.98  Current options:
% 3.54/0.98  ------ 
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing...
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  % SZS status Theorem for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  fof(f5,axiom,(
% 3.54/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f39,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f5])).
% 3.54/0.98  
% 3.54/0.98  fof(f8,axiom,(
% 3.54/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f47,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f8])).
% 3.54/0.98  
% 3.54/0.98  fof(f9,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f48,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f9])).
% 3.54/0.98  
% 3.54/0.98  fof(f52,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f47,f48])).
% 3.54/0.98  
% 3.54/0.98  fof(f57,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f39,f52,f52])).
% 3.54/0.98  
% 3.54/0.98  fof(f11,conjecture,(
% 3.54/0.98    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f12,negated_conjecture,(
% 3.54/0.98    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.54/0.98    inference(negated_conjecture,[],[f11])).
% 3.54/0.98  
% 3.54/0.98  fof(f13,plain,(
% 3.54/0.98    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 3.54/0.98    inference(ennf_transformation,[],[f12])).
% 3.54/0.98  
% 3.54/0.98  fof(f26,plain,(
% 3.54/0.98    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f27,plain,(
% 3.54/0.98    ~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f26])).
% 3.54/0.98  
% 3.54/0.98  fof(f50,plain,(
% 3.54/0.98    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 3.54/0.98    inference(cnf_transformation,[],[f27])).
% 3.54/0.98  
% 3.54/0.98  fof(f10,axiom,(
% 3.54/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f49,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f10])).
% 3.54/0.98  
% 3.54/0.98  fof(f53,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.54/0.98    inference(definition_unfolding,[],[f49,f52])).
% 3.54/0.98  
% 3.54/0.98  fof(f7,axiom,(
% 3.54/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f46,plain,(
% 3.54/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f7])).
% 3.54/0.98  
% 3.54/0.98  fof(f54,plain,(
% 3.54/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f46,f52])).
% 3.54/0.98  
% 3.54/0.98  fof(f64,plain,(
% 3.54/0.98    r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3)),
% 3.54/0.98    inference(definition_unfolding,[],[f50,f53,f54])).
% 3.54/0.98  
% 3.54/0.98  fof(f2,axiom,(
% 3.54/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f19,plain,(
% 3.54/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.98    inference(nnf_transformation,[],[f2])).
% 3.54/0.98  
% 3.54/0.98  fof(f20,plain,(
% 3.54/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.98    inference(flattening,[],[f19])).
% 3.54/0.98  
% 3.54/0.98  fof(f36,plain,(
% 3.54/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f20])).
% 3.54/0.98  
% 3.54/0.98  fof(f4,axiom,(
% 3.54/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f38,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f4])).
% 3.54/0.98  
% 3.54/0.98  fof(f56,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.54/0.98    inference(definition_unfolding,[],[f38,f53])).
% 3.54/0.98  
% 3.54/0.98  fof(f6,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f21,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.54/0.98    inference(nnf_transformation,[],[f6])).
% 3.54/0.98  
% 3.54/0.98  fof(f22,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.54/0.98    inference(flattening,[],[f21])).
% 3.54/0.98  
% 3.54/0.98  fof(f23,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.54/0.98    inference(rectify,[],[f22])).
% 3.54/0.98  
% 3.54/0.98  fof(f24,plain,(
% 3.54/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f25,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 3.54/0.98  
% 3.54/0.98  fof(f42,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.54/0.98    inference(cnf_transformation,[],[f25])).
% 3.54/0.98  
% 3.54/0.98  fof(f61,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.54/0.98    inference(definition_unfolding,[],[f42,f52])).
% 3.54/0.98  
% 3.54/0.98  fof(f70,plain,(
% 3.54/0.98    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 3.54/0.98    inference(equality_resolution,[],[f61])).
% 3.54/0.98  
% 3.54/0.98  fof(f71,plain,(
% 3.54/0.98    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 3.54/0.98    inference(equality_resolution,[],[f70])).
% 3.54/0.98  
% 3.54/0.98  fof(f3,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f37,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f3])).
% 3.54/0.98  
% 3.54/0.98  fof(f55,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 3.54/0.98    inference(definition_unfolding,[],[f37,f53])).
% 3.54/0.98  
% 3.54/0.98  fof(f1,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f14,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.54/0.98    inference(nnf_transformation,[],[f1])).
% 3.54/0.98  
% 3.54/0.98  fof(f15,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.54/0.98    inference(flattening,[],[f14])).
% 3.54/0.98  
% 3.54/0.98  fof(f16,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.54/0.98    inference(rectify,[],[f15])).
% 3.54/0.98  
% 3.54/0.98  fof(f17,plain,(
% 3.54/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f18,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 3.54/0.98  
% 3.54/0.98  fof(f30,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.54/0.98    inference(cnf_transformation,[],[f18])).
% 3.54/0.98  
% 3.54/0.98  fof(f65,plain,(
% 3.54/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.54/0.98    inference(equality_resolution,[],[f30])).
% 3.54/0.98  
% 3.54/0.98  fof(f29,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.54/0.98    inference(cnf_transformation,[],[f18])).
% 3.54/0.98  
% 3.54/0.98  fof(f66,plain,(
% 3.54/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.54/0.98    inference(equality_resolution,[],[f29])).
% 3.54/0.98  
% 3.54/0.98  fof(f41,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.54/0.98    inference(cnf_transformation,[],[f25])).
% 3.54/0.98  
% 3.54/0.98  fof(f62,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.54/0.98    inference(definition_unfolding,[],[f41,f52])).
% 3.54/0.98  
% 3.54/0.98  fof(f72,plain,(
% 3.54/0.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.54/0.98    inference(equality_resolution,[],[f62])).
% 3.54/0.98  
% 3.54/0.98  fof(f73,plain,(
% 3.54/0.98    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.54/0.98    inference(equality_resolution,[],[f72])).
% 3.54/0.98  
% 3.54/0.98  fof(f51,plain,(
% 3.54/0.98    ~r2_hidden(sK2,sK3)),
% 3.54/0.98    inference(cnf_transformation,[],[f27])).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11,plain,
% 3.54/0.98      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_19,negated_conjecture,
% 3.54/0.98      ( r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) ),
% 3.54/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4522,plain,
% 3.54/0.98      ( r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4625,plain,
% 3.54/0.98      ( r1_tarski(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_11,c_4522]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6,plain,
% 3.54/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.54/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4529,plain,
% 3.54/0.98      ( X0 = X1
% 3.54/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.54/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5043,plain,
% 3.54/0.98      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = sK3
% 3.54/0.98      | r1_tarski(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_4625,c_4529]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_10,plain,
% 3.54/0.98      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 3.54/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4527,plain,
% 3.54/0.98      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5402,plain,
% 3.54/0.98      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = sK3 ),
% 3.54/0.98      inference(forward_subsumption_resolution,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_5043,c_4527]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_15,plain,
% 3.54/0.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4526,plain,
% 3.54/0.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9,plain,
% 3.54/0.98      ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.54/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3,plain,
% 3.54/0.98      ( ~ r2_hidden(X0,X1)
% 3.54/0.98      | r2_hidden(X0,X2)
% 3.54/0.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4532,plain,
% 3.54/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.54/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.54/0.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5993,plain,
% 3.54/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.54/0.98      | r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3)) = iProver_top
% 3.54/0.98      | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X3))) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_9,c_4532]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4,negated_conjecture,
% 3.54/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4531,plain,
% 3.54/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.54/0.98      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6433,plain,
% 3.54/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.54/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.54/0.98      | r2_hidden(X0,k3_tarski(k2_enumset1(X3,X3,X3,X2))) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_5993,c_4531]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6765,plain,
% 3.54/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.54/0.98      | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_4526,c_6433]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6870,plain,
% 3.54/0.98      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.54/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_5402,c_6765]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6884,plain,
% 3.54/0.98      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.54/0.98      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_6870]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_16,plain,
% 3.54/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_28,plain,
% 3.54/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_30,plain,
% 3.54/0.98      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_28]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_18,negated_conjecture,
% 3.54/0.98      ( ~ r2_hidden(sK2,sK3) ),
% 3.54/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_21,plain,
% 3.54/0.98      ( r2_hidden(sK2,sK3) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(contradiction,plain,
% 3.54/0.98      ( $false ),
% 3.54/0.98      inference(minisat,[status(thm)],[c_6884,c_30,c_21]) ).
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  ------                               Statistics
% 3.54/0.98  
% 3.54/0.98  ------ Selected
% 3.54/0.98  
% 3.54/0.98  total_time:                             0.191
% 3.54/0.98  
%------------------------------------------------------------------------------
