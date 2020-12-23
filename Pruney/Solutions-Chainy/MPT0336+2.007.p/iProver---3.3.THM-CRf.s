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
% DateTime   : Thu Dec  3 11:38:35 EST 2020

% Result     : Theorem 15.88s
% Output     : CNFRefutation 15.88s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 276 expanded)
%              Number of clauses        :   56 (  86 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  314 ( 839 expanded)
%              Number of equality atoms :   72 ( 166 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f24])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f34])).

fof(f60,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f67,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f65])).

fof(f61,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_487,plain,
    ( X0 != X1
    | X2 != X3
    | k3_xboole_0(X0,X2) = k3_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_485,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5675,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != k3_xboole_0(X1,X3)
    | k3_xboole_0(X0,X2) = X4 ),
    inference(resolution,[status(thm)],[c_487,c_485])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_300,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_301,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_13,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_479,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_301,c_13,c_1])).

cnf(c_30573,plain,
    ( X0 != sK3
    | X1 != sK2
    | k3_xboole_0(X1,X0) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_5675,c_479])).

cnf(c_489,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2848,plain,
    ( r1_xboole_0(X0,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ r1_xboole_0(X1,k3_xboole_0(sK2,sK3))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_489,c_479])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1649,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_7,c_12])).

cnf(c_1832,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_11,c_1649])).

cnf(c_3581,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
    | X2 != k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_2848,c_1832])).

cnf(c_31408,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ r1_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
    | X1 != sK3
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_30573,c_3581])).

cnf(c_22,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1095,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1472,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1254,plain,
    ( ~ r1_xboole_0(sK3,X0)
    | r1_xboole_0(sK3,k2_xboole_0(X0,sK4))
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2284,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1400,plain,
    ( r1_xboole_0(sK3,X0)
    | k3_xboole_0(sK3,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_35566,plain,
    ( r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK3,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_484,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2790,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_485,c_484])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8843,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_2790,c_9])).

cnf(c_2782,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_485,c_1])).

cnf(c_14656,plain,
    ( k3_xboole_0(sK3,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_2782,c_479])).

cnf(c_15279,plain,
    ( X0 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
    | k3_xboole_0(sK3,sK2) = X0 ),
    inference(resolution,[status(thm)],[c_14656,c_485])).

cnf(c_55964,plain,
    ( ~ r1_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
    | k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8843,c_15279])).

cnf(c_70074,plain,
    ( ~ r1_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31408,c_22,c_21,c_1095,c_1472,c_2284,c_35566,c_55964])).

cnf(c_1842,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_1832,c_10])).

cnf(c_70099,plain,
    ( ~ r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(resolution,[status(thm)],[c_70074,c_1842])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_13,c_1])).

cnf(c_4143,plain,
    ( r2_hidden(X0,k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_4150,plain,
    ( r2_hidden(sK5,k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_4143])).

cnf(c_3343,plain,
    ( ~ r1_xboole_0(sK4,sK3)
    | ~ r2_hidden(X0,k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3345,plain,
    ( ~ r1_xboole_0(sK4,sK3)
    | ~ r2_hidden(sK5,k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_3343])).

cnf(c_20,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2329,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
    | r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2335,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
    | r2_hidden(sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_2329])).

cnf(c_1140,plain,
    ( r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1693,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
    | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1696,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
    | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_70099,c_4150,c_3345,c_2335,c_1696,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 15.88/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.88/2.48  
% 15.88/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.88/2.48  
% 15.88/2.48  ------  iProver source info
% 15.88/2.48  
% 15.88/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.88/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.88/2.48  git: non_committed_changes: false
% 15.88/2.48  git: last_make_outside_of_git: false
% 15.88/2.48  
% 15.88/2.48  ------ 
% 15.88/2.48  ------ Parsing...
% 15.88/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.88/2.48  
% 15.88/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.88/2.48  
% 15.88/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.88/2.48  
% 15.88/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.88/2.48  ------ Proving...
% 15.88/2.48  ------ Problem Properties 
% 15.88/2.48  
% 15.88/2.48  
% 15.88/2.48  clauses                                 24
% 15.88/2.48  conjectures                             3
% 15.88/2.48  EPR                                     4
% 15.88/2.48  Horn                                    20
% 15.88/2.48  unary                                   9
% 15.88/2.48  binary                                  10
% 15.88/2.48  lits                                    45
% 15.88/2.48  lits eq                                 10
% 15.88/2.48  fd_pure                                 0
% 15.88/2.48  fd_pseudo                               0
% 15.88/2.48  fd_cond                                 0
% 15.88/2.48  fd_pseudo_cond                          3
% 15.88/2.48  AC symbols                              1
% 15.88/2.48  
% 15.88/2.48  ------ Input Options Time Limit: Unbounded
% 15.88/2.48  
% 15.88/2.48  
% 15.88/2.48  ------ 
% 15.88/2.48  Current options:
% 15.88/2.48  ------ 
% 15.88/2.48  
% 15.88/2.48  
% 15.88/2.48  
% 15.88/2.48  
% 15.88/2.48  ------ Proving...
% 15.88/2.48  
% 15.88/2.48  
% 15.88/2.48  % SZS status Theorem for theBenchmark.p
% 15.88/2.48  
% 15.88/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.88/2.48  
% 15.88/2.48  fof(f9,axiom,(
% 15.88/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.88/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.48  
% 15.88/2.48  fof(f21,plain,(
% 15.88/2.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.88/2.48    inference(ennf_transformation,[],[f9])).
% 15.88/2.48  
% 15.88/2.48  fof(f51,plain,(
% 15.88/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.88/2.48    inference(cnf_transformation,[],[f21])).
% 15.88/2.48  
% 15.88/2.48  fof(f16,conjecture,(
% 15.88/2.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 15.88/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.48  
% 15.88/2.48  fof(f17,negated_conjecture,(
% 15.88/2.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 15.88/2.48    inference(negated_conjecture,[],[f16])).
% 15.88/2.48  
% 15.88/2.48  fof(f24,plain,(
% 15.88/2.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 15.88/2.48    inference(ennf_transformation,[],[f17])).
% 15.88/2.48  
% 15.88/2.48  fof(f25,plain,(
% 15.88/2.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 15.88/2.48    inference(flattening,[],[f24])).
% 15.88/2.48  
% 15.88/2.48  fof(f34,plain,(
% 15.88/2.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 15.88/2.48    introduced(choice_axiom,[])).
% 15.88/2.48  
% 15.88/2.48  fof(f35,plain,(
% 15.88/2.48    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 15.88/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f34])).
% 15.88/2.48  
% 15.88/2.48  fof(f60,plain,(
% 15.88/2.48    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 15.88/2.48    inference(cnf_transformation,[],[f35])).
% 15.88/2.48  
% 15.88/2.48  fof(f12,axiom,(
% 15.88/2.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.88/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.48  
% 15.88/2.48  fof(f56,plain,(
% 15.88/2.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.88/2.48    inference(cnf_transformation,[],[f12])).
% 15.88/2.48  
% 15.88/2.48  fof(f13,axiom,(
% 15.88/2.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.88/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.48  
% 15.88/2.48  fof(f57,plain,(
% 15.88/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.88/2.48    inference(cnf_transformation,[],[f13])).
% 15.88/2.48  
% 15.88/2.48  fof(f14,axiom,(
% 15.88/2.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.88/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.48  
% 15.88/2.48  fof(f58,plain,(
% 15.88/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.88/2.48    inference(cnf_transformation,[],[f14])).
% 15.88/2.48  
% 15.88/2.48  fof(f64,plain,(
% 15.88/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.88/2.48    inference(definition_unfolding,[],[f57,f58])).
% 15.88/2.48  
% 15.88/2.48  fof(f65,plain,(
% 15.88/2.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 15.88/2.48    inference(definition_unfolding,[],[f56,f64])).
% 15.88/2.48  
% 15.88/2.48  fof(f67,plain,(
% 15.88/2.48    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 15.88/2.48    inference(definition_unfolding,[],[f60,f65])).
% 15.88/2.48  
% 15.88/2.48  fof(f7,axiom,(
% 15.88/2.48    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.88/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.48  
% 15.88/2.48  fof(f49,plain,(
% 15.88/2.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.88/2.48    inference(cnf_transformation,[],[f7])).
% 15.88/2.48  
% 15.88/2.48  fof(f2,axiom,(
% 15.88/2.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.88/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.48  
% 15.88/2.48  fof(f37,plain,(
% 15.88/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.88/2.48    inference(cnf_transformation,[],[f2])).
% 15.88/2.48  
% 15.88/2.48  fof(f6,axiom,(
% 15.88/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.88/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.48  
% 15.88/2.48  fof(f18,plain,(
% 15.88/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.88/2.48    inference(rectify,[],[f6])).
% 15.88/2.48  
% 15.88/2.48  fof(f20,plain,(
% 15.88/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.88/2.48    inference(ennf_transformation,[],[f18])).
% 15.88/2.48  
% 15.88/2.48  fof(f32,plain,(
% 15.88/2.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 15.88/2.48    introduced(choice_axiom,[])).
% 15.88/2.48  
% 15.88/2.48  fof(f33,plain,(
% 15.88/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.88/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f32])).
% 15.88/2.49  
% 15.88/2.49  fof(f48,plain,(
% 15.88/2.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 15.88/2.49    inference(cnf_transformation,[],[f33])).
% 15.88/2.49  
% 15.88/2.49  fof(f3,axiom,(
% 15.88/2.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.88/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.49  
% 15.88/2.49  fof(f26,plain,(
% 15.88/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.88/2.49    inference(nnf_transformation,[],[f3])).
% 15.88/2.49  
% 15.88/2.49  fof(f27,plain,(
% 15.88/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.88/2.49    inference(flattening,[],[f26])).
% 15.88/2.49  
% 15.88/2.49  fof(f28,plain,(
% 15.88/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.88/2.49    inference(rectify,[],[f27])).
% 15.88/2.49  
% 15.88/2.49  fof(f29,plain,(
% 15.88/2.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.88/2.49    introduced(choice_axiom,[])).
% 15.88/2.49  
% 15.88/2.49  fof(f30,plain,(
% 15.88/2.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.88/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 15.88/2.49  
% 15.88/2.49  fof(f38,plain,(
% 15.88/2.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.88/2.49    inference(cnf_transformation,[],[f30])).
% 15.88/2.49  
% 15.88/2.49  fof(f70,plain,(
% 15.88/2.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 15.88/2.49    inference(equality_resolution,[],[f38])).
% 15.88/2.49  
% 15.88/2.49  fof(f47,plain,(
% 15.88/2.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 15.88/2.49    inference(cnf_transformation,[],[f33])).
% 15.88/2.49  
% 15.88/2.49  fof(f62,plain,(
% 15.88/2.49    r1_xboole_0(sK4,sK3)),
% 15.88/2.49    inference(cnf_transformation,[],[f35])).
% 15.88/2.49  
% 15.88/2.49  fof(f63,plain,(
% 15.88/2.49    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 15.88/2.49    inference(cnf_transformation,[],[f35])).
% 15.88/2.49  
% 15.88/2.49  fof(f5,axiom,(
% 15.88/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.88/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.49  
% 15.88/2.49  fof(f19,plain,(
% 15.88/2.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.88/2.49    inference(ennf_transformation,[],[f5])).
% 15.88/2.49  
% 15.88/2.49  fof(f46,plain,(
% 15.88/2.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.88/2.49    inference(cnf_transformation,[],[f19])).
% 15.88/2.49  
% 15.88/2.49  fof(f11,axiom,(
% 15.88/2.49    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 15.88/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.49  
% 15.88/2.49  fof(f22,plain,(
% 15.88/2.49    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 15.88/2.49    inference(ennf_transformation,[],[f11])).
% 15.88/2.49  
% 15.88/2.49  fof(f53,plain,(
% 15.88/2.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 15.88/2.49    inference(cnf_transformation,[],[f22])).
% 15.88/2.49  
% 15.88/2.49  fof(f4,axiom,(
% 15.88/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.88/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.49  
% 15.88/2.49  fof(f31,plain,(
% 15.88/2.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.88/2.49    inference(nnf_transformation,[],[f4])).
% 15.88/2.49  
% 15.88/2.49  fof(f45,plain,(
% 15.88/2.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.88/2.49    inference(cnf_transformation,[],[f31])).
% 15.88/2.49  
% 15.88/2.49  fof(f44,plain,(
% 15.88/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.88/2.49    inference(cnf_transformation,[],[f31])).
% 15.88/2.49  
% 15.88/2.49  fof(f40,plain,(
% 15.88/2.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 15.88/2.49    inference(cnf_transformation,[],[f30])).
% 15.88/2.49  
% 15.88/2.49  fof(f68,plain,(
% 15.88/2.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 15.88/2.49    inference(equality_resolution,[],[f40])).
% 15.88/2.49  
% 15.88/2.49  fof(f15,axiom,(
% 15.88/2.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 15.88/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.88/2.49  
% 15.88/2.49  fof(f23,plain,(
% 15.88/2.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 15.88/2.49    inference(ennf_transformation,[],[f15])).
% 15.88/2.49  
% 15.88/2.49  fof(f59,plain,(
% 15.88/2.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 15.88/2.49    inference(cnf_transformation,[],[f23])).
% 15.88/2.49  
% 15.88/2.49  fof(f66,plain,(
% 15.88/2.49    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 15.88/2.49    inference(definition_unfolding,[],[f59,f65])).
% 15.88/2.49  
% 15.88/2.49  fof(f61,plain,(
% 15.88/2.49    r2_hidden(sK5,sK4)),
% 15.88/2.49    inference(cnf_transformation,[],[f35])).
% 15.88/2.49  
% 15.88/2.49  cnf(c_487,plain,
% 15.88/2.49      ( X0 != X1 | X2 != X3 | k3_xboole_0(X0,X2) = k3_xboole_0(X1,X3) ),
% 15.88/2.49      theory(equality) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_485,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_5675,plain,
% 15.88/2.49      ( X0 != X1
% 15.88/2.49      | X2 != X3
% 15.88/2.49      | X4 != k3_xboole_0(X1,X3)
% 15.88/2.49      | k3_xboole_0(X0,X2) = X4 ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_487,c_485]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_15,plain,
% 15.88/2.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.88/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_24,negated_conjecture,
% 15.88/2.49      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 15.88/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_300,plain,
% 15.88/2.49      ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 15.88/2.49      | k3_xboole_0(X1,X0) = X1
% 15.88/2.49      | k3_xboole_0(sK2,sK3) != X1 ),
% 15.88/2.49      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_301,plain,
% 15.88/2.49      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 15.88/2.49      inference(unflattening,[status(thm)],[c_300]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_13,plain,
% 15.88/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 15.88/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1,plain,
% 15.88/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.88/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_479,plain,
% 15.88/2.49      ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
% 15.88/2.49      inference(theory_normalisation,[status(thm)],[c_301,c_13,c_1]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_30573,plain,
% 15.88/2.49      ( X0 != sK3
% 15.88/2.49      | X1 != sK2
% 15.88/2.49      | k3_xboole_0(X1,X0) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_5675,c_479]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_489,plain,
% 15.88/2.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.88/2.49      theory(equality) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_2848,plain,
% 15.88/2.49      ( r1_xboole_0(X0,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
% 15.88/2.49      | ~ r1_xboole_0(X1,k3_xboole_0(sK2,sK3))
% 15.88/2.49      | X0 != X1 ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_489,c_479]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_11,plain,
% 15.88/2.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 15.88/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_7,plain,
% 15.88/2.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 15.88/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_12,plain,
% 15.88/2.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 15.88/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1649,plain,
% 15.88/2.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_7,c_12]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1832,plain,
% 15.88/2.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_11,c_1649]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_3581,plain,
% 15.88/2.49      ( ~ r1_xboole_0(X0,X1)
% 15.88/2.49      | r1_xboole_0(X2,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
% 15.88/2.49      | X2 != k3_xboole_0(X0,X1) ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_2848,c_1832]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_31408,plain,
% 15.88/2.49      ( r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
% 15.88/2.49      | ~ r1_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
% 15.88/2.49      | X1 != sK3
% 15.88/2.49      | X0 != sK2 ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_30573,c_3581]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_22,negated_conjecture,
% 15.88/2.49      ( r1_xboole_0(sK4,sK3) ),
% 15.88/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_21,negated_conjecture,
% 15.88/2.49      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 15.88/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_10,plain,
% 15.88/2.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.88/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1095,plain,
% 15.88/2.49      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1472,plain,
% 15.88/2.49      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 15.88/2.49      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_19,plain,
% 15.88/2.49      ( ~ r1_xboole_0(X0,X1)
% 15.88/2.49      | ~ r1_xboole_0(X0,X2)
% 15.88/2.49      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.88/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1254,plain,
% 15.88/2.49      ( ~ r1_xboole_0(sK3,X0)
% 15.88/2.49      | r1_xboole_0(sK3,k2_xboole_0(X0,sK4))
% 15.88/2.49      | ~ r1_xboole_0(sK3,sK4) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_19]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_2284,plain,
% 15.88/2.49      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 15.88/2.49      | ~ r1_xboole_0(sK3,sK4)
% 15.88/2.49      | ~ r1_xboole_0(sK3,sK2) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_1254]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_8,plain,
% 15.88/2.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.88/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1400,plain,
% 15.88/2.49      ( r1_xboole_0(sK3,X0) | k3_xboole_0(sK3,X0) != k1_xboole_0 ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_8]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_35566,plain,
% 15.88/2.49      ( r1_xboole_0(sK3,sK2) | k3_xboole_0(sK3,sK2) != k1_xboole_0 ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_1400]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_484,plain,( X0 = X0 ),theory(equality) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_2790,plain,
% 15.88/2.49      ( X0 != X1 | X1 = X0 ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_485,c_484]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_9,plain,
% 15.88/2.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.88/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_8843,plain,
% 15.88/2.49      ( ~ r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1) ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_2790,c_9]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_2782,plain,
% 15.88/2.49      ( X0 != k3_xboole_0(X1,X2) | k3_xboole_0(X2,X1) = X0 ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_485,c_1]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_14656,plain,
% 15.88/2.49      ( k3_xboole_0(sK3,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_2782,c_479]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_15279,plain,
% 15.88/2.49      ( X0 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
% 15.88/2.49      | k3_xboole_0(sK3,sK2) = X0 ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_14656,c_485]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_55964,plain,
% 15.88/2.49      ( ~ r1_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
% 15.88/2.49      | k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_8843,c_15279]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_70074,plain,
% 15.88/2.49      ( ~ r1_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 15.88/2.49      inference(global_propositional_subsumption,
% 15.88/2.49                [status(thm)],
% 15.88/2.49                [c_31408,c_22,c_21,c_1095,c_1472,c_2284,c_35566,c_55964]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1842,plain,
% 15.88/2.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_1832,c_10]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_70099,plain,
% 15.88/2.49      ( ~ r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 15.88/2.49      inference(resolution,[status(thm)],[c_70074,c_1842]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_5,plain,
% 15.88/2.49      ( ~ r2_hidden(X0,X1)
% 15.88/2.49      | ~ r2_hidden(X0,X2)
% 15.88/2.49      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 15.88/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_482,plain,
% 15.88/2.49      ( ~ r2_hidden(X0,X1)
% 15.88/2.49      | ~ r2_hidden(X0,X2)
% 15.88/2.49      | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 15.88/2.49      inference(theory_normalisation,[status(thm)],[c_5,c_13,c_1]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_4143,plain,
% 15.88/2.49      ( r2_hidden(X0,k3_xboole_0(sK4,sK3))
% 15.88/2.49      | ~ r2_hidden(X0,sK3)
% 15.88/2.49      | ~ r2_hidden(X0,sK4) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_482]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_4150,plain,
% 15.88/2.49      ( r2_hidden(sK5,k3_xboole_0(sK4,sK3))
% 15.88/2.49      | ~ r2_hidden(sK5,sK3)
% 15.88/2.49      | ~ r2_hidden(sK5,sK4) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_4143]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_3343,plain,
% 15.88/2.49      ( ~ r1_xboole_0(sK4,sK3) | ~ r2_hidden(X0,k3_xboole_0(sK4,sK3)) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_11]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_3345,plain,
% 15.88/2.49      ( ~ r1_xboole_0(sK4,sK3) | ~ r2_hidden(sK5,k3_xboole_0(sK4,sK3)) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_3343]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_20,plain,
% 15.88/2.49      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 15.88/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_2329,plain,
% 15.88/2.49      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) | r2_hidden(X0,sK3) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_20]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_2335,plain,
% 15.88/2.49      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
% 15.88/2.49      | r2_hidden(sK5,sK3) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_2329]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1140,plain,
% 15.88/2.49      ( r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
% 15.88/2.49      | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X0) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1693,plain,
% 15.88/2.49      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
% 15.88/2.49      | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_1140]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_1696,plain,
% 15.88/2.49      ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
% 15.88/2.49      | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 15.88/2.49      inference(instantiation,[status(thm)],[c_1693]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(c_23,negated_conjecture,
% 15.88/2.49      ( r2_hidden(sK5,sK4) ),
% 15.88/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.88/2.49  
% 15.88/2.49  cnf(contradiction,plain,
% 15.88/2.49      ( $false ),
% 15.88/2.49      inference(minisat,
% 15.88/2.49                [status(thm)],
% 15.88/2.49                [c_70099,c_4150,c_3345,c_2335,c_1696,c_22,c_23]) ).
% 15.88/2.49  
% 15.88/2.49  
% 15.88/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.88/2.49  
% 15.88/2.49  ------                               Statistics
% 15.88/2.49  
% 15.88/2.49  ------ Selected
% 15.88/2.49  
% 15.88/2.49  total_time:                             1.754
% 15.88/2.49  
%------------------------------------------------------------------------------
