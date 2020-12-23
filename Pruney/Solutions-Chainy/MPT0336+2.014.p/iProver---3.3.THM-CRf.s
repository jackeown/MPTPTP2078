%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:36 EST 2020

% Result     : Theorem 11.40s
% Output     : CNFRefutation 11.40s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 300 expanded)
%              Number of clauses        :   57 ( 112 expanded)
%              Number of leaves         :   20 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  261 ( 654 expanded)
%              Number of equality atoms :   58 ( 210 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f27])).

fof(f34,plain,
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

fof(f35,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f34])).

fof(f58,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f63])).

fof(f71,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f58,f64])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f19,plain,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(definition_unfolding,[],[f61,f62])).

cnf(c_430,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_428,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_1571,plain,
    ( X0_41 != X1_41
    | X1_41 = X0_41 ),
    inference(resolution,[status(thm)],[c_430,c_428])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_414,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_10,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_420,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X1_41,X0_41) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_414,c_10,c_1])).

cnf(c_3701,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k1_xboole_0 = k3_xboole_0(X1_41,X0_41) ),
    inference(resolution,[status(thm)],[c_1571,c_420])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_245,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_246,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_398,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_246])).

cnf(c_426,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_398,c_10,c_1])).

cnf(c_3705,plain,
    ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_1571,c_426])).

cnf(c_3949,plain,
    ( X0_41 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
    | k3_xboole_0(sK2,sK3) = X0_41 ),
    inference(resolution,[status(thm)],[c_3705,c_430])).

cnf(c_29801,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3701,c_3949])).

cnf(c_1569,plain,
    ( X0_41 != k3_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = X0_41 ),
    inference(resolution,[status(thm)],[c_430,c_426])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_415,plain,
    ( r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_419,plain,
    ( r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X1_41,X0_41) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_415,c_10,c_1])).

cnf(c_1927,plain,
    ( r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_1569,c_419])).

cnf(c_33372,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_29801,c_1927])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_412,plain,
    ( ~ r2_hidden(X0_42,X0_41)
    | ~ r2_hidden(X0_42,X1_41)
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1038,plain,
    ( ~ r2_hidden(X0_42,sK3)
    | ~ r2_hidden(X0_42,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_1040,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_402,plain,
    ( r2_hidden(X0_42,X0_41)
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1165,plain,
    ( r2_hidden(X0_42,sK3)
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_1167,plain,
    ( r2_hidden(sK5,sK3)
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_409,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_421,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(X1_41,X0_41) ),
    inference(theory_normalisation,[status(thm)],[c_409,c_10,c_1])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_410,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41)
    | r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3938,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) ),
    inference(resolution,[status(thm)],[c_421,c_410])).

cnf(c_33374,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29801,c_3938])).

cnf(c_33376,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33372,c_19,c_18,c_1040,c_1167,c_33374])).

cnf(c_34323,plain,
    ( r1_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_33376,c_419])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_403,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | ~ r1_xboole_0(X0_41,X2_41)
    | r1_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_424,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | ~ r1_xboole_0(X0_41,X2_41)
    | r1_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X1_41,X2_41)))) ),
    inference(theory_normalisation,[status(thm)],[c_403,c_10,c_1])).

cnf(c_1103,plain,
    ( ~ r1_xboole_0(sK3,X0_41)
    | r1_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(sK4,k3_xboole_0(X0_41,sK4))))
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_424])).

cnf(c_3370,plain,
    ( r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_413,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1414,plain,
    ( r1_xboole_0(X0_41,sK3)
    | ~ r1_xboole_0(sK3,X0_41) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_2520,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))),sK3)
    | ~ r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_1414])).

cnf(c_990,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_401,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_425,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))),sK3) ),
    inference(theory_normalisation,[status(thm)],[c_401,c_10,c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34323,c_3370,c_2520,c_990,c_425,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:44:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.40/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/1.98  
% 11.40/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.40/1.98  
% 11.40/1.98  ------  iProver source info
% 11.40/1.98  
% 11.40/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.40/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.40/1.98  git: non_committed_changes: false
% 11.40/1.98  git: last_make_outside_of_git: false
% 11.40/1.98  
% 11.40/1.98  ------ 
% 11.40/1.98  ------ Parsing...
% 11.40/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.40/1.98  
% 11.40/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.40/1.98  
% 11.40/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.40/1.98  
% 11.40/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.40/1.98  ------ Proving...
% 11.40/1.98  ------ Problem Properties 
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  clauses                                 20
% 11.40/1.98  conjectures                             3
% 11.40/1.98  EPR                                     5
% 11.40/1.98  Horn                                    16
% 11.40/1.98  unary                                   8
% 11.40/1.98  binary                                  10
% 11.40/1.98  lits                                    34
% 11.40/1.98  lits eq                                 6
% 11.40/1.98  fd_pure                                 0
% 11.40/1.98  fd_pseudo                               0
% 11.40/1.98  fd_cond                                 0
% 11.40/1.98  fd_pseudo_cond                          0
% 11.40/1.98  AC symbols                              1
% 11.40/1.98  
% 11.40/1.98  ------ Input Options Time Limit: Unbounded
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  ------ 
% 11.40/1.98  Current options:
% 11.40/1.98  ------ 
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  ------ Proving...
% 11.40/1.98  
% 11.40/1.98  
% 11.40/1.98  % SZS status Theorem for theBenchmark.p
% 11.40/1.98  
% 11.40/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.40/1.98  
% 11.40/1.98  fof(f3,axiom,(
% 11.40/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f29,plain,(
% 11.40/1.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.40/1.98    inference(nnf_transformation,[],[f3])).
% 11.40/1.98  
% 11.40/1.98  fof(f38,plain,(
% 11.40/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f29])).
% 11.40/1.98  
% 11.40/1.98  fof(f8,axiom,(
% 11.40/1.98    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f47,plain,(
% 11.40/1.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f8])).
% 11.40/1.98  
% 11.40/1.98  fof(f2,axiom,(
% 11.40/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f37,plain,(
% 11.40/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f2])).
% 11.40/1.98  
% 11.40/1.98  fof(f9,axiom,(
% 11.40/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f24,plain,(
% 11.40/1.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.40/1.98    inference(ennf_transformation,[],[f9])).
% 11.40/1.98  
% 11.40/1.98  fof(f48,plain,(
% 11.40/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f24])).
% 11.40/1.98  
% 11.40/1.98  fof(f17,conjecture,(
% 11.40/1.98    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f18,negated_conjecture,(
% 11.40/1.98    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 11.40/1.98    inference(negated_conjecture,[],[f17])).
% 11.40/1.98  
% 11.40/1.98  fof(f27,plain,(
% 11.40/1.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 11.40/1.98    inference(ennf_transformation,[],[f18])).
% 11.40/1.98  
% 11.40/1.98  fof(f28,plain,(
% 11.40/1.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 11.40/1.98    inference(flattening,[],[f27])).
% 11.40/1.98  
% 11.40/1.98  fof(f34,plain,(
% 11.40/1.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 11.40/1.98    introduced(choice_axiom,[])).
% 11.40/1.98  
% 11.40/1.98  fof(f35,plain,(
% 11.40/1.98    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 11.40/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f34])).
% 11.40/1.98  
% 11.40/1.98  fof(f58,plain,(
% 11.40/1.98    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 11.40/1.98    inference(cnf_transformation,[],[f35])).
% 11.40/1.98  
% 11.40/1.98  fof(f13,axiom,(
% 11.40/1.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f54,plain,(
% 11.40/1.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f13])).
% 11.40/1.98  
% 11.40/1.98  fof(f14,axiom,(
% 11.40/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f55,plain,(
% 11.40/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f14])).
% 11.40/1.98  
% 11.40/1.98  fof(f15,axiom,(
% 11.40/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f56,plain,(
% 11.40/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.40/1.98    inference(cnf_transformation,[],[f15])).
% 11.40/1.98  
% 11.40/1.98  fof(f63,plain,(
% 11.40/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.40/1.98    inference(definition_unfolding,[],[f55,f56])).
% 11.40/1.98  
% 11.40/1.98  fof(f64,plain,(
% 11.40/1.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.40/1.98    inference(definition_unfolding,[],[f54,f63])).
% 11.40/1.98  
% 11.40/1.98  fof(f71,plain,(
% 11.40/1.98    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 11.40/1.98    inference(definition_unfolding,[],[f58,f64])).
% 11.40/1.98  
% 11.40/1.98  fof(f39,plain,(
% 11.40/1.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.40/1.98    inference(cnf_transformation,[],[f29])).
% 11.40/1.98  
% 11.40/1.98  fof(f59,plain,(
% 11.40/1.98    r2_hidden(sK5,sK4)),
% 11.40/1.98    inference(cnf_transformation,[],[f35])).
% 11.40/1.98  
% 11.40/1.98  fof(f60,plain,(
% 11.40/1.98    r1_xboole_0(sK4,sK3)),
% 11.40/1.98    inference(cnf_transformation,[],[f35])).
% 11.40/1.98  
% 11.40/1.98  fof(f5,axiom,(
% 11.40/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.40/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.98  
% 11.40/1.98  fof(f19,plain,(
% 11.40/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.40/1.98    inference(rectify,[],[f5])).
% 11.40/1.98  
% 11.40/1.98  fof(f22,plain,(
% 11.40/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.40/1.98    inference(ennf_transformation,[],[f19])).
% 11.40/1.98  
% 11.40/1.98  fof(f30,plain,(
% 11.40/1.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.40/1.98    introduced(choice_axiom,[])).
% 11.40/1.98  
% 11.40/1.98  fof(f31,plain,(
% 11.40/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.40/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f30])).
% 11.40/1.98  
% 11.40/1.98  fof(f43,plain,(
% 11.40/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.40/1.99    inference(cnf_transformation,[],[f31])).
% 11.40/1.99  
% 11.40/1.99  fof(f16,axiom,(
% 11.40/1.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 11.40/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.99  
% 11.40/1.99  fof(f26,plain,(
% 11.40/1.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 11.40/1.99    inference(ennf_transformation,[],[f16])).
% 11.40/1.99  
% 11.40/1.99  fof(f57,plain,(
% 11.40/1.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 11.40/1.99    inference(cnf_transformation,[],[f26])).
% 11.40/1.99  
% 11.40/1.99  fof(f69,plain,(
% 11.40/1.99    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 11.40/1.99    inference(definition_unfolding,[],[f57,f64])).
% 11.40/1.99  
% 11.40/1.99  fof(f6,axiom,(
% 11.40/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.40/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.99  
% 11.40/1.99  fof(f20,plain,(
% 11.40/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.40/1.99    inference(rectify,[],[f6])).
% 11.40/1.99  
% 11.40/1.99  fof(f23,plain,(
% 11.40/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.40/1.99    inference(ennf_transformation,[],[f20])).
% 11.40/1.99  
% 11.40/1.99  fof(f32,plain,(
% 11.40/1.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 11.40/1.99    introduced(choice_axiom,[])).
% 11.40/1.99  
% 11.40/1.99  fof(f33,plain,(
% 11.40/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.40/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f32])).
% 11.40/1.99  
% 11.40/1.99  fof(f45,plain,(
% 11.40/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.40/1.99    inference(cnf_transformation,[],[f33])).
% 11.40/1.99  
% 11.40/1.99  fof(f41,plain,(
% 11.40/1.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 11.40/1.99    inference(cnf_transformation,[],[f31])).
% 11.40/1.99  
% 11.40/1.99  fof(f11,axiom,(
% 11.40/1.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 11.40/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.99  
% 11.40/1.99  fof(f25,plain,(
% 11.40/1.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 11.40/1.99    inference(ennf_transformation,[],[f11])).
% 11.40/1.99  
% 11.40/1.99  fof(f50,plain,(
% 11.40/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 11.40/1.99    inference(cnf_transformation,[],[f25])).
% 11.40/1.99  
% 11.40/1.99  fof(f12,axiom,(
% 11.40/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.40/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.99  
% 11.40/1.99  fof(f53,plain,(
% 11.40/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.40/1.99    inference(cnf_transformation,[],[f12])).
% 11.40/1.99  
% 11.40/1.99  fof(f7,axiom,(
% 11.40/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.40/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.99  
% 11.40/1.99  fof(f46,plain,(
% 11.40/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.40/1.99    inference(cnf_transformation,[],[f7])).
% 11.40/1.99  
% 11.40/1.99  fof(f62,plain,(
% 11.40/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 11.40/1.99    inference(definition_unfolding,[],[f53,f46])).
% 11.40/1.99  
% 11.40/1.99  fof(f68,plain,(
% 11.40/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) )),
% 11.40/1.99    inference(definition_unfolding,[],[f50,f62])).
% 11.40/1.99  
% 11.40/1.99  fof(f4,axiom,(
% 11.40/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.40/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.40/1.99  
% 11.40/1.99  fof(f21,plain,(
% 11.40/1.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.40/1.99    inference(ennf_transformation,[],[f4])).
% 11.40/1.99  
% 11.40/1.99  fof(f40,plain,(
% 11.40/1.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.40/1.99    inference(cnf_transformation,[],[f21])).
% 11.40/1.99  
% 11.40/1.99  fof(f61,plain,(
% 11.40/1.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 11.40/1.99    inference(cnf_transformation,[],[f35])).
% 11.40/1.99  
% 11.40/1.99  fof(f70,plain,(
% 11.40/1.99    ~r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3)),
% 11.40/1.99    inference(definition_unfolding,[],[f61,f62])).
% 11.40/1.99  
% 11.40/1.99  cnf(c_430,plain,
% 11.40/1.99      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 11.40/1.99      theory(equality) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_428,plain,( X0_41 = X0_41 ),theory(equality) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1571,plain,
% 11.40/1.99      ( X0_41 != X1_41 | X1_41 = X0_41 ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_430,c_428]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_3,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.40/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_414,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 11.40/1.99      | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_3]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_10,plain,
% 11.40/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 11.40/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1,plain,
% 11.40/1.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.40/1.99      inference(cnf_transformation,[],[f37]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_420,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 11.40/1.99      | k3_xboole_0(X1_41,X0_41) = k1_xboole_0 ),
% 11.40/1.99      inference(theory_normalisation,[status(thm)],[c_414,c_10,c_1]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_3701,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 11.40/1.99      | k1_xboole_0 = k3_xboole_0(X1_41,X0_41) ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_1571,c_420]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_11,plain,
% 11.40/1.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.40/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_20,negated_conjecture,
% 11.40/1.99      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 11.40/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_245,plain,
% 11.40/1.99      ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 11.40/1.99      | k3_xboole_0(X1,X0) = X1
% 11.40/1.99      | k3_xboole_0(sK2,sK3) != X1 ),
% 11.40/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_246,plain,
% 11.40/1.99      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 11.40/1.99      inference(unflattening,[status(thm)],[c_245]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_398,plain,
% 11.40/1.99      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_246]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_426,plain,
% 11.40/1.99      ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
% 11.40/1.99      inference(theory_normalisation,[status(thm)],[c_398,c_10,c_1]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_3705,plain,
% 11.40/1.99      ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_1571,c_426]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_3949,plain,
% 11.40/1.99      ( X0_41 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
% 11.40/1.99      | k3_xboole_0(sK2,sK3) = X0_41 ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_3705,c_430]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_29801,plain,
% 11.40/1.99      ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 11.40/1.99      | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_3701,c_3949]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1569,plain,
% 11.40/1.99      ( X0_41 != k3_xboole_0(sK2,sK3)
% 11.40/1.99      | k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = X0_41 ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_430,c_426]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_2,plain,
% 11.40/1.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.40/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_415,plain,
% 11.40/1.99      ( r1_xboole_0(X0_41,X1_41)
% 11.40/1.99      | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_2]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_419,plain,
% 11.40/1.99      ( r1_xboole_0(X0_41,X1_41)
% 11.40/1.99      | k3_xboole_0(X1_41,X0_41) != k1_xboole_0 ),
% 11.40/1.99      inference(theory_normalisation,[status(thm)],[c_415,c_10,c_1]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1927,plain,
% 11.40/1.99      ( r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 11.40/1.99      | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_1569,c_419]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_33372,plain,
% 11.40/1.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0
% 11.40/1.99      | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_29801,c_1927]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_19,negated_conjecture,
% 11.40/1.99      ( r2_hidden(sK5,sK4) ),
% 11.40/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_18,negated_conjecture,
% 11.40/1.99      ( r1_xboole_0(sK4,sK3) ),
% 11.40/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_5,plain,
% 11.40/1.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 11.40/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_412,plain,
% 11.40/1.99      ( ~ r2_hidden(X0_42,X0_41)
% 11.40/1.99      | ~ r2_hidden(X0_42,X1_41)
% 11.40/1.99      | ~ r1_xboole_0(X0_41,X1_41) ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_5]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1038,plain,
% 11.40/1.99      ( ~ r2_hidden(X0_42,sK3)
% 11.40/1.99      | ~ r2_hidden(X0_42,sK4)
% 11.40/1.99      | ~ r1_xboole_0(sK4,sK3) ),
% 11.40/1.99      inference(instantiation,[status(thm)],[c_412]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1040,plain,
% 11.40/1.99      ( ~ r2_hidden(sK5,sK3)
% 11.40/1.99      | ~ r2_hidden(sK5,sK4)
% 11.40/1.99      | ~ r1_xboole_0(sK4,sK3) ),
% 11.40/1.99      inference(instantiation,[status(thm)],[c_1038]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_16,plain,
% 11.40/1.99      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 11.40/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_402,plain,
% 11.40/1.99      ( r2_hidden(X0_42,X0_41)
% 11.40/1.99      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_16]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1165,plain,
% 11.40/1.99      ( r2_hidden(X0_42,sK3)
% 11.40/1.99      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) ),
% 11.40/1.99      inference(instantiation,[status(thm)],[c_402]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1167,plain,
% 11.40/1.99      ( r2_hidden(sK5,sK3)
% 11.40/1.99      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
% 11.40/1.99      inference(instantiation,[status(thm)],[c_1165]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_8,plain,
% 11.40/1.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 11.40/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_409,plain,
% 11.40/1.99      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
% 11.40/1.99      | ~ r1_xboole_0(X0_41,X1_41) ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_8]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_421,plain,
% 11.40/1.99      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
% 11.40/1.99      | ~ r1_xboole_0(X1_41,X0_41) ),
% 11.40/1.99      inference(theory_normalisation,[status(thm)],[c_409,c_10,c_1]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_7,plain,
% 11.40/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 11.40/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_410,plain,
% 11.40/1.99      ( r2_hidden(sK0(X0_41,X1_41),X0_41) | r1_xboole_0(X0_41,X1_41) ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_7]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_3938,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 11.40/1.99      | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_421,c_410]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_33374,plain,
% 11.40/1.99      ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
% 11.40/1.99      | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_29801,c_3938]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_33376,plain,
% 11.40/1.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 11.40/1.99      inference(global_propositional_subsumption,
% 11.40/1.99                [status(thm)],
% 11.40/1.99                [c_33372,c_19,c_18,c_1040,c_1167,c_33374]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_34323,plain,
% 11.40/1.99      ( r1_xboole_0(sK3,sK2) ),
% 11.40/1.99      inference(resolution,[status(thm)],[c_33376,c_419]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_15,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.40/1.99      | ~ r1_xboole_0(X0,X2)
% 11.40/1.99      | r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 11.40/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_403,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 11.40/1.99      | ~ r1_xboole_0(X0_41,X2_41)
% 11.40/1.99      | r1_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_15]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_424,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 11.40/1.99      | ~ r1_xboole_0(X0_41,X2_41)
% 11.40/1.99      | r1_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X1_41,X2_41)))) ),
% 11.40/1.99      inference(theory_normalisation,[status(thm)],[c_403,c_10,c_1]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1103,plain,
% 11.40/1.99      ( ~ r1_xboole_0(sK3,X0_41)
% 11.40/1.99      | r1_xboole_0(sK3,k5_xboole_0(X0_41,k5_xboole_0(sK4,k3_xboole_0(X0_41,sK4))))
% 11.40/1.99      | ~ r1_xboole_0(sK3,sK4) ),
% 11.40/1.99      inference(instantiation,[status(thm)],[c_424]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_3370,plain,
% 11.40/1.99      ( r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))))
% 11.40/1.99      | ~ r1_xboole_0(sK3,sK4)
% 11.40/1.99      | ~ r1_xboole_0(sK3,sK2) ),
% 11.40/1.99      inference(instantiation,[status(thm)],[c_1103]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_4,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.40/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_413,plain,
% 11.40/1.99      ( ~ r1_xboole_0(X0_41,X1_41) | r1_xboole_0(X1_41,X0_41) ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_4]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_1414,plain,
% 11.40/1.99      ( r1_xboole_0(X0_41,sK3) | ~ r1_xboole_0(sK3,X0_41) ),
% 11.40/1.99      inference(instantiation,[status(thm)],[c_413]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_2520,plain,
% 11.40/1.99      ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))),sK3)
% 11.40/1.99      | ~ r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4)))) ),
% 11.40/1.99      inference(instantiation,[status(thm)],[c_1414]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_990,plain,
% 11.40/1.99      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 11.40/1.99      inference(instantiation,[status(thm)],[c_413]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_17,negated_conjecture,
% 11.40/1.99      ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
% 11.40/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_401,negated_conjecture,
% 11.40/1.99      ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
% 11.40/1.99      inference(subtyping,[status(esa)],[c_17]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(c_425,negated_conjecture,
% 11.40/1.99      ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK2,sK4))),sK3) ),
% 11.40/1.99      inference(theory_normalisation,[status(thm)],[c_401,c_10,c_1]) ).
% 11.40/1.99  
% 11.40/1.99  cnf(contradiction,plain,
% 11.40/1.99      ( $false ),
% 11.40/1.99      inference(minisat,
% 11.40/1.99                [status(thm)],
% 11.40/1.99                [c_34323,c_3370,c_2520,c_990,c_425,c_18]) ).
% 11.40/1.99  
% 11.40/1.99  
% 11.40/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.40/1.99  
% 11.40/1.99  ------                               Statistics
% 11.40/1.99  
% 11.40/1.99  ------ Selected
% 11.40/1.99  
% 11.40/1.99  total_time:                             1.181
% 11.40/1.99  
%------------------------------------------------------------------------------
