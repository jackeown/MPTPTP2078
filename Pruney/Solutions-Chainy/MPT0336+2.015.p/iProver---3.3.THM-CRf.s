%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:36 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 290 expanded)
%              Number of clauses        :   66 ( 115 expanded)
%              Number of leaves         :   20 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  267 ( 649 expanded)
%              Number of equality atoms :   91 ( 217 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f26])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f33])).

fof(f54,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f65,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f64,plain,(
    ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_370,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_365,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_1393,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X2_41,X1_41)
    | X2_41 != X0_41 ),
    inference(resolution,[status(thm)],[c_370,c_365])).

cnf(c_367,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_1292,plain,
    ( X0_41 != X1_41
    | X1_41 = X0_41 ),
    inference(resolution,[status(thm)],[c_367,c_365])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_209,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_210,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_339,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_210])).

cnf(c_10,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_363,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_339,c_10,c_1])).

cnf(c_2404,plain,
    ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_1292,c_363])).

cnf(c_4355,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))),X0_41)
    | r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
    inference(resolution,[status(thm)],[c_1393,c_2404])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_347,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(X1_41,X0_41) ),
    inference(theory_normalisation,[status(thm)],[c_347,c_10,c_1])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_348,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41)
    | r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1140,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) ),
    inference(resolution,[status(thm)],[c_359,c_348])).

cnf(c_5636,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
    inference(resolution,[status(thm)],[c_4355,c_1140])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_342,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_362,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))),sK3) ),
    inference(theory_normalisation,[status(thm)],[c_342,c_10,c_1])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_352,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_358,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X1_41,X0_41) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_352,c_10,c_1])).

cnf(c_794,plain,
    ( ~ r1_xboole_0(sK4,sK3)
    | k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_1325,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_1323,plain,
    ( X0_41 != X1_41
    | k1_xboole_0 != X1_41
    | k1_xboole_0 = X0_41 ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1324,plain,
    ( X0_41 != k1_xboole_0
    | k1_xboole_0 = X0_41
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_2110,plain,
    ( k3_xboole_0(sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK3,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_353,plain,
    ( r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_357,plain,
    ( r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X1_41,X0_41) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_353,c_10,c_1])).

cnf(c_1611,plain,
    ( r1_xboole_0(X0_41,sK3)
    | k3_xboole_0(sK3,X0_41) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_3414,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))),sK3)
    | k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1611])).

cnf(c_857,plain,
    ( k3_xboole_0(X0_41,X1_41) != X2_41
    | k3_xboole_0(X0_41,X1_41) = k1_xboole_0
    | k1_xboole_0 != X2_41 ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_2252,plain,
    ( k3_xboole_0(X0_41,X1_41) != k3_xboole_0(sK3,sK4)
    | k3_xboole_0(X0_41,X1_41) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_3768,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(sK4,k3_xboole_0(X0_41,sK4)))) != k3_xboole_0(sK3,sK4)
    | k3_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(sK4,k3_xboole_0(X0_41,sK4)))) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_9466,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) != k3_xboole_0(sK3,sK4)
    | k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3768])).

cnf(c_2400,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k1_xboole_0 = k3_xboole_0(X1_41,X0_41) ),
    inference(resolution,[status(thm)],[c_1292,c_358])).

cnf(c_2563,plain,
    ( X0_41 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
    | k3_xboole_0(sK2,sK3) = X0_41 ),
    inference(resolution,[status(thm)],[c_2404,c_367])).

cnf(c_12755,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2400,c_2563])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_344,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_361,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X1_41,X2_41)))) = k3_xboole_0(X0_41,X2_41) ),
    inference(theory_normalisation,[status(thm)],[c_344,c_10,c_1])).

cnf(c_1171,plain,
    ( ~ r1_xboole_0(sK3,X0_41)
    | k3_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(X1_41,k3_xboole_0(X0_41,X1_41)))) = k3_xboole_0(sK3,X1_41) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_2090,plain,
    ( ~ r1_xboole_0(sK3,X0_41)
    | k3_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(sK4,k3_xboole_0(X0_41,sK4)))) = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_14539,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_1599,plain,
    ( r1_xboole_0(sK3,X0_41)
    | k3_xboole_0(X0_41,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_30236,plain,
    ( r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_34269,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5636,c_15,c_362,c_794,c_1325,c_2110,c_3414,c_9466,c_12755,c_14539,c_30236])).

cnf(c_34908,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
    inference(resolution,[status(thm)],[c_34269,c_1140])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_343,plain,
    ( r2_hidden(X0_42,X0_41)
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_916,plain,
    ( r2_hidden(X0_42,sK3)
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_918,plain,
    ( r2_hidden(sK5,sK3)
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_350,plain,
    ( ~ r2_hidden(X0_42,X0_41)
    | ~ r2_hidden(X0_42,X1_41)
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_817,plain,
    ( ~ r2_hidden(X0_42,sK3)
    | ~ r2_hidden(X0_42,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_819,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34908,c_918,c_819,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.02/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.02/1.49  
% 8.02/1.49  ------  iProver source info
% 8.02/1.49  
% 8.02/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.02/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.02/1.49  git: non_committed_changes: false
% 8.02/1.49  git: last_make_outside_of_git: false
% 8.02/1.49  
% 8.02/1.49  ------ 
% 8.02/1.49  ------ Parsing...
% 8.02/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.02/1.49  ------ Proving...
% 8.02/1.49  ------ Problem Properties 
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  clauses                                 17
% 8.02/1.49  conjectures                             3
% 8.02/1.49  EPR                                     4
% 8.02/1.49  Horn                                    13
% 8.02/1.49  unary                                   7
% 8.02/1.49  binary                                  9
% 8.02/1.49  lits                                    28
% 8.02/1.49  lits eq                                 7
% 8.02/1.49  fd_pure                                 0
% 8.02/1.49  fd_pseudo                               0
% 8.02/1.49  fd_cond                                 0
% 8.02/1.49  fd_pseudo_cond                          0
% 8.02/1.49  AC symbols                              1
% 8.02/1.49  
% 8.02/1.49  ------ Input Options Time Limit: Unbounded
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  ------ 
% 8.02/1.49  Current options:
% 8.02/1.49  ------ 
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  ------ Proving...
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  % SZS status Theorem for theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  fof(f9,axiom,(
% 8.02/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f23,plain,(
% 8.02/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 8.02/1.49    inference(ennf_transformation,[],[f9])).
% 8.02/1.49  
% 8.02/1.49  fof(f47,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f23])).
% 8.02/1.49  
% 8.02/1.49  fof(f16,conjecture,(
% 8.02/1.49    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f17,negated_conjecture,(
% 8.02/1.49    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 8.02/1.49    inference(negated_conjecture,[],[f16])).
% 8.02/1.49  
% 8.02/1.49  fof(f26,plain,(
% 8.02/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 8.02/1.49    inference(ennf_transformation,[],[f17])).
% 8.02/1.49  
% 8.02/1.49  fof(f27,plain,(
% 8.02/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 8.02/1.49    inference(flattening,[],[f26])).
% 8.02/1.49  
% 8.02/1.49  fof(f33,plain,(
% 8.02/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f34,plain,(
% 8.02/1.49    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 8.02/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f33])).
% 8.02/1.49  
% 8.02/1.49  fof(f54,plain,(
% 8.02/1.49    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 8.02/1.49    inference(cnf_transformation,[],[f34])).
% 8.02/1.49  
% 8.02/1.49  fof(f12,axiom,(
% 8.02/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f50,plain,(
% 8.02/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f12])).
% 8.02/1.49  
% 8.02/1.49  fof(f13,axiom,(
% 8.02/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f51,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f13])).
% 8.02/1.49  
% 8.02/1.49  fof(f14,axiom,(
% 8.02/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f52,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f14])).
% 8.02/1.49  
% 8.02/1.49  fof(f59,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 8.02/1.49    inference(definition_unfolding,[],[f51,f52])).
% 8.02/1.49  
% 8.02/1.49  fof(f60,plain,(
% 8.02/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 8.02/1.49    inference(definition_unfolding,[],[f50,f59])).
% 8.02/1.49  
% 8.02/1.49  fof(f65,plain,(
% 8.02/1.49    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 8.02/1.49    inference(definition_unfolding,[],[f54,f60])).
% 8.02/1.49  
% 8.02/1.49  fof(f8,axiom,(
% 8.02/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f46,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f8])).
% 8.02/1.49  
% 8.02/1.49  fof(f2,axiom,(
% 8.02/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f36,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f2])).
% 8.02/1.49  
% 8.02/1.49  fof(f6,axiom,(
% 8.02/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f19,plain,(
% 8.02/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 8.02/1.49    inference(rectify,[],[f6])).
% 8.02/1.49  
% 8.02/1.49  fof(f22,plain,(
% 8.02/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 8.02/1.49    inference(ennf_transformation,[],[f19])).
% 8.02/1.49  
% 8.02/1.49  fof(f31,plain,(
% 8.02/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f32,plain,(
% 8.02/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 8.02/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).
% 8.02/1.49  
% 8.02/1.49  fof(f44,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 8.02/1.49    inference(cnf_transformation,[],[f32])).
% 8.02/1.49  
% 8.02/1.49  fof(f5,axiom,(
% 8.02/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f18,plain,(
% 8.02/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 8.02/1.49    inference(rectify,[],[f5])).
% 8.02/1.49  
% 8.02/1.49  fof(f21,plain,(
% 8.02/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 8.02/1.49    inference(ennf_transformation,[],[f18])).
% 8.02/1.49  
% 8.02/1.49  fof(f29,plain,(
% 8.02/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f30,plain,(
% 8.02/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 8.02/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f29])).
% 8.02/1.49  
% 8.02/1.49  fof(f40,plain,(
% 8.02/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f30])).
% 8.02/1.49  
% 8.02/1.49  fof(f56,plain,(
% 8.02/1.49    r1_xboole_0(sK4,sK3)),
% 8.02/1.49    inference(cnf_transformation,[],[f34])).
% 8.02/1.49  
% 8.02/1.49  fof(f57,plain,(
% 8.02/1.49    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 8.02/1.49    inference(cnf_transformation,[],[f34])).
% 8.02/1.49  
% 8.02/1.49  fof(f11,axiom,(
% 8.02/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f49,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.02/1.49    inference(cnf_transformation,[],[f11])).
% 8.02/1.49  
% 8.02/1.49  fof(f7,axiom,(
% 8.02/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f45,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.02/1.49    inference(cnf_transformation,[],[f7])).
% 8.02/1.49  
% 8.02/1.49  fof(f58,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 8.02/1.49    inference(definition_unfolding,[],[f49,f45])).
% 8.02/1.49  
% 8.02/1.49  fof(f64,plain,(
% 8.02/1.49    ~r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3)),
% 8.02/1.49    inference(definition_unfolding,[],[f57,f58])).
% 8.02/1.49  
% 8.02/1.49  fof(f3,axiom,(
% 8.02/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f28,plain,(
% 8.02/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 8.02/1.49    inference(nnf_transformation,[],[f3])).
% 8.02/1.49  
% 8.02/1.49  fof(f37,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f28])).
% 8.02/1.49  
% 8.02/1.49  fof(f38,plain,(
% 8.02/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 8.02/1.49    inference(cnf_transformation,[],[f28])).
% 8.02/1.49  
% 8.02/1.49  fof(f10,axiom,(
% 8.02/1.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f24,plain,(
% 8.02/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 8.02/1.49    inference(ennf_transformation,[],[f10])).
% 8.02/1.49  
% 8.02/1.49  fof(f48,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f24])).
% 8.02/1.49  
% 8.02/1.49  fof(f62,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 8.02/1.49    inference(definition_unfolding,[],[f48,f58])).
% 8.02/1.49  
% 8.02/1.49  fof(f15,axiom,(
% 8.02/1.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 8.02/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f25,plain,(
% 8.02/1.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 8.02/1.49    inference(ennf_transformation,[],[f15])).
% 8.02/1.49  
% 8.02/1.49  fof(f53,plain,(
% 8.02/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f25])).
% 8.02/1.49  
% 8.02/1.49  fof(f63,plain,(
% 8.02/1.49    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 8.02/1.49    inference(definition_unfolding,[],[f53,f60])).
% 8.02/1.49  
% 8.02/1.49  fof(f42,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f30])).
% 8.02/1.49  
% 8.02/1.49  fof(f55,plain,(
% 8.02/1.49    r2_hidden(sK5,sK4)),
% 8.02/1.49    inference(cnf_transformation,[],[f34])).
% 8.02/1.49  
% 8.02/1.49  cnf(c_370,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | r1_xboole_0(X2_41,X3_41)
% 8.02/1.49      | X2_41 != X0_41
% 8.02/1.49      | X3_41 != X1_41 ),
% 8.02/1.49      theory(equality) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_365,plain,( X0_41 = X0_41 ),theory(equality) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1393,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | r1_xboole_0(X2_41,X1_41)
% 8.02/1.49      | X2_41 != X0_41 ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_370,c_365]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_367,plain,
% 8.02/1.49      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 8.02/1.49      theory(equality) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1292,plain,
% 8.02/1.49      ( X0_41 != X1_41 | X1_41 = X0_41 ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_367,c_365]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_11,plain,
% 8.02/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 8.02/1.49      inference(cnf_transformation,[],[f47]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_17,negated_conjecture,
% 8.02/1.49      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 8.02/1.49      inference(cnf_transformation,[],[f65]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_209,plain,
% 8.02/1.49      ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 8.02/1.49      | k3_xboole_0(X1,X0) = X1
% 8.02/1.49      | k3_xboole_0(sK2,sK3) != X1 ),
% 8.02/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_210,plain,
% 8.02/1.49      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 8.02/1.49      inference(unflattening,[status(thm)],[c_209]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_339,plain,
% 8.02/1.49      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 8.02/1.49      inference(subtyping,[status(esa)],[c_210]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_10,plain,
% 8.02/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 8.02/1.49      inference(cnf_transformation,[],[f46]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1,plain,
% 8.02/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f36]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_363,plain,
% 8.02/1.49      ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
% 8.02/1.49      inference(theory_normalisation,[status(thm)],[c_339,c_10,c_1]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2404,plain,
% 8.02/1.49      ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_1292,c_363]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4355,plain,
% 8.02/1.49      ( ~ r1_xboole_0(k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))),X0_41)
% 8.02/1.49      | r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_1393,c_2404]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8,plain,
% 8.02/1.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 8.02/1.49      inference(cnf_transformation,[],[f44]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_347,plain,
% 8.02/1.49      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
% 8.02/1.49      | ~ r1_xboole_0(X0_41,X1_41) ),
% 8.02/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_359,plain,
% 8.02/1.49      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
% 8.02/1.49      | ~ r1_xboole_0(X1_41,X0_41) ),
% 8.02/1.49      inference(theory_normalisation,[status(thm)],[c_347,c_10,c_1]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_7,plain,
% 8.02/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f40]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_348,plain,
% 8.02/1.49      ( r2_hidden(sK0(X0_41,X1_41),X0_41) | r1_xboole_0(X0_41,X1_41) ),
% 8.02/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1140,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_359,c_348]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5636,plain,
% 8.02/1.49      ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 8.02/1.49      | r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_4355,c_1140]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_15,negated_conjecture,
% 8.02/1.49      ( r1_xboole_0(sK4,sK3) ),
% 8.02/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_14,negated_conjecture,
% 8.02/1.49      ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
% 8.02/1.49      inference(cnf_transformation,[],[f64]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_342,negated_conjecture,
% 8.02/1.49      ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
% 8.02/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_362,negated_conjecture,
% 8.02/1.49      ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))),sK3) ),
% 8.02/1.49      inference(theory_normalisation,[status(thm)],[c_342,c_10,c_1]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 8.02/1.49      inference(cnf_transformation,[],[f37]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_352,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
% 8.02/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_358,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | k3_xboole_0(X1_41,X0_41) = k1_xboole_0 ),
% 8.02/1.49      inference(theory_normalisation,[status(thm)],[c_352,c_10,c_1]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_794,plain,
% 8.02/1.49      ( ~ r1_xboole_0(sK4,sK3) | k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_358]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1325,plain,
% 8.02/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_365]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1323,plain,
% 8.02/1.49      ( X0_41 != X1_41 | k1_xboole_0 != X1_41 | k1_xboole_0 = X0_41 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_367]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1324,plain,
% 8.02/1.49      ( X0_41 != k1_xboole_0
% 8.02/1.49      | k1_xboole_0 = X0_41
% 8.02/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_1323]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2110,plain,
% 8.02/1.49      ( k3_xboole_0(sK3,sK4) != k1_xboole_0
% 8.02/1.49      | k1_xboole_0 = k3_xboole_0(sK3,sK4)
% 8.02/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_1324]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2,plain,
% 8.02/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 8.02/1.49      inference(cnf_transformation,[],[f38]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_353,plain,
% 8.02/1.49      ( r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
% 8.02/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_357,plain,
% 8.02/1.49      ( r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | k3_xboole_0(X1_41,X0_41) != k1_xboole_0 ),
% 8.02/1.49      inference(theory_normalisation,[status(thm)],[c_353,c_10,c_1]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1611,plain,
% 8.02/1.49      ( r1_xboole_0(X0_41,sK3) | k3_xboole_0(sK3,X0_41) != k1_xboole_0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_357]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3414,plain,
% 8.02/1.49      ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))),sK3)
% 8.02/1.49      | k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) != k1_xboole_0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_1611]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_857,plain,
% 8.02/1.49      ( k3_xboole_0(X0_41,X1_41) != X2_41
% 8.02/1.49      | k3_xboole_0(X0_41,X1_41) = k1_xboole_0
% 8.02/1.49      | k1_xboole_0 != X2_41 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_367]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2252,plain,
% 8.02/1.49      ( k3_xboole_0(X0_41,X1_41) != k3_xboole_0(sK3,sK4)
% 8.02/1.49      | k3_xboole_0(X0_41,X1_41) = k1_xboole_0
% 8.02/1.49      | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_857]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3768,plain,
% 8.02/1.49      ( k3_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(sK4,k3_xboole_0(X0_41,sK4)))) != k3_xboole_0(sK3,sK4)
% 8.02/1.49      | k3_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(sK4,k3_xboole_0(X0_41,sK4)))) = k1_xboole_0
% 8.02/1.49      | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_2252]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9466,plain,
% 8.02/1.49      ( k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) != k3_xboole_0(sK3,sK4)
% 8.02/1.49      | k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) = k1_xboole_0
% 8.02/1.49      | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_3768]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2400,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | k1_xboole_0 = k3_xboole_0(X1_41,X0_41) ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_1292,c_358]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2563,plain,
% 8.02/1.49      ( X0_41 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
% 8.02/1.49      | k3_xboole_0(sK2,sK3) = X0_41 ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_2404,c_367]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_12755,plain,
% 8.02/1.49      ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 8.02/1.49      | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_2400,c_2563]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_12,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0,X1)
% 8.02/1.49      | k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,X2) ),
% 8.02/1.49      inference(cnf_transformation,[],[f62]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_344,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41) ),
% 8.02/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_361,plain,
% 8.02/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 8.02/1.49      | k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X1_41,X2_41)))) = k3_xboole_0(X0_41,X2_41) ),
% 8.02/1.49      inference(theory_normalisation,[status(thm)],[c_344,c_10,c_1]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1171,plain,
% 8.02/1.49      ( ~ r1_xboole_0(sK3,X0_41)
% 8.02/1.49      | k3_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(X1_41,k3_xboole_0(X0_41,X1_41)))) = k3_xboole_0(sK3,X1_41) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_361]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2090,plain,
% 8.02/1.49      ( ~ r1_xboole_0(sK3,X0_41)
% 8.02/1.49      | k3_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(sK4,k3_xboole_0(X0_41,sK4)))) = k3_xboole_0(sK3,sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_1171]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_14539,plain,
% 8.02/1.49      ( ~ r1_xboole_0(sK3,sK2)
% 8.02/1.49      | k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) = k3_xboole_0(sK3,sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_2090]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1599,plain,
% 8.02/1.49      ( r1_xboole_0(sK3,X0_41) | k3_xboole_0(X0_41,sK3) != k1_xboole_0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_357]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_30236,plain,
% 8.02/1.49      ( r1_xboole_0(sK3,sK2) | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_1599]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_34269,plain,
% 8.02/1.49      ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_5636,c_15,c_362,c_794,c_1325,c_2110,c_3414,c_9466,
% 8.02/1.49                 c_12755,c_14539,c_30236]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_34908,plain,
% 8.02/1.49      ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
% 8.02/1.49      inference(resolution,[status(thm)],[c_34269,c_1140]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_13,plain,
% 8.02/1.49      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f63]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_343,plain,
% 8.02/1.49      ( r2_hidden(X0_42,X0_41)
% 8.02/1.49      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) ),
% 8.02/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_916,plain,
% 8.02/1.49      ( r2_hidden(X0_42,sK3)
% 8.02/1.49      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_343]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_918,plain,
% 8.02/1.49      ( r2_hidden(sK5,sK3)
% 8.02/1.49      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_916]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5,plain,
% 8.02/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f42]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_350,plain,
% 8.02/1.49      ( ~ r2_hidden(X0_42,X0_41)
% 8.02/1.49      | ~ r2_hidden(X0_42,X1_41)
% 8.02/1.49      | ~ r1_xboole_0(X0_41,X1_41) ),
% 8.02/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_817,plain,
% 8.02/1.49      ( ~ r2_hidden(X0_42,sK3)
% 8.02/1.49      | ~ r2_hidden(X0_42,sK4)
% 8.02/1.49      | ~ r1_xboole_0(sK4,sK3) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_350]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_819,plain,
% 8.02/1.49      ( ~ r2_hidden(sK5,sK3)
% 8.02/1.49      | ~ r2_hidden(sK5,sK4)
% 8.02/1.49      | ~ r1_xboole_0(sK4,sK3) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_817]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_16,negated_conjecture,
% 8.02/1.49      ( r2_hidden(sK5,sK4) ),
% 8.02/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(contradiction,plain,
% 8.02/1.49      ( $false ),
% 8.02/1.49      inference(minisat,[status(thm)],[c_34908,c_918,c_819,c_15,c_16]) ).
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  ------                               Statistics
% 8.02/1.49  
% 8.02/1.49  ------ Selected
% 8.02/1.49  
% 8.02/1.49  total_time:                             0.885
% 8.02/1.49  
%------------------------------------------------------------------------------
