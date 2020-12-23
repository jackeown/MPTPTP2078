%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:45 EST 2020

% Result     : Theorem 11.96s
% Output     : CNFRefutation 11.96s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 258 expanded)
%              Number of clauses        :   58 (  74 expanded)
%              Number of leaves         :   19 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  270 ( 720 expanded)
%              Number of equality atoms :   48 (  86 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f16,plain,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,
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

fof(f33,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f32])).

fof(f56,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f54,f43,f58])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f43,f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f57,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2415,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(resolution,[status(thm)],[c_11,c_2])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1501,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,X2))
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X2) ),
    inference(resolution,[status(thm)],[c_16,c_9])).

cnf(c_10384,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X3) ),
    inference(resolution,[status(thm)],[c_2415,c_1501])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_50994,plain,
    ( ~ r2_hidden(X0,sK4)
    | r1_xboole_0(k1_enumset1(X0,X0,X0),sK3)
    | ~ r1_xboole_0(sK4,X1) ),
    inference(resolution,[status(thm)],[c_10384,c_18])).

cnf(c_1675,plain,
    ( r2_hidden(X0,sK3)
    | r1_xboole_0(k1_enumset1(X0,X0,X0),sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2303,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

cnf(c_51585,plain,
    ( r1_xboole_0(k1_enumset1(X0,X0,X0),sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_50994,c_1675,c_2303])).

cnf(c_51586,plain,
    ( ~ r2_hidden(X0,sK4)
    | r1_xboole_0(k1_enumset1(X0,X0,X0),sK3) ),
    inference(renaming,[status(thm)],[c_51585])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3666,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,X3)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_271,c_15])).

cnf(c_266,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_10674,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(resolution,[status(thm)],[c_3666,c_266])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20674,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(resolution,[status(thm)],[c_10674,c_7])).

cnf(c_51605,plain,
    ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
    | ~ r2_hidden(X1,sK4)
    | r1_xboole_0(X0,sK3) ),
    inference(resolution,[status(thm)],[c_51586,c_20674])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_52434,plain,
    ( ~ r2_hidden(sK5,sK4)
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) ),
    inference(resolution,[status(thm)],[c_51605,c_20])).

cnf(c_751,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_753,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_770,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1598,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_770])).

cnf(c_755,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_756,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1465,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_755,c_756])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_752,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_769,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5415,plain,
    ( r2_hidden(sK5,X0) != iProver_top
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_752,c_769])).

cnf(c_10477,plain,
    ( k4_xboole_0(k1_enumset1(sK5,sK5,sK5),X0) = k1_enumset1(sK5,sK5,sK5)
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_5415])).

cnf(c_11526,plain,
    ( k4_xboole_0(k1_enumset1(sK5,sK5,sK5),sK3) = k1_enumset1(sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_1598,c_10477])).

cnf(c_764,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11897,plain,
    ( r1_tarski(X0,k1_enumset1(sK5,sK5,sK5)) != iProver_top
    | r1_xboole_0(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11526,c_764])).

cnf(c_13112,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_751,c_11897])).

cnf(c_13113,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13112])).

cnf(c_54344,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_52434,c_13113])).

cnf(c_269,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3491,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_269,c_266])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4566,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(resolution,[status(thm)],[c_3491,c_0])).

cnf(c_54364,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)),sK3) ),
    inference(resolution,[status(thm)],[c_54344,c_4566])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2291,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7509,plain,
    ( ~ r2_hidden(sK1(X0,X1),X2)
    | ~ r1_xboole_0(X2,X0)
    | r1_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_2291,c_6])).

cnf(c_15558,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(resolution,[status(thm)],[c_7509,c_6])).

cnf(c_55401,plain,
    ( r1_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_54364,c_15558])).

cnf(c_1040,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_933,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1,c_18])).

cnf(c_902,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55401,c_1040,c_933,c_902,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:23:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.96/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.96/1.98  
% 11.96/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.96/1.98  
% 11.96/1.98  ------  iProver source info
% 11.96/1.98  
% 11.96/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.96/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.96/1.98  git: non_committed_changes: false
% 11.96/1.98  git: last_make_outside_of_git: false
% 11.96/1.98  
% 11.96/1.98  ------ 
% 11.96/1.98  ------ Parsing...
% 11.96/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.96/1.98  
% 11.96/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.96/1.98  
% 11.96/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.96/1.98  
% 11.96/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.96/1.98  ------ Proving...
% 11.96/1.98  ------ Problem Properties 
% 11.96/1.98  
% 11.96/1.98  
% 11.96/1.98  clauses                                 21
% 11.96/1.98  conjectures                             4
% 11.96/1.98  EPR                                     4
% 11.96/1.98  Horn                                    17
% 11.96/1.98  unary                                   6
% 11.96/1.98  binary                                  13
% 11.96/1.98  lits                                    38
% 11.96/1.98  lits eq                                 3
% 11.96/1.98  fd_pure                                 0
% 11.96/1.98  fd_pseudo                               0
% 11.96/1.98  fd_cond                                 0
% 11.96/1.98  fd_pseudo_cond                          0
% 11.96/1.98  AC symbols                              0
% 11.96/1.98  
% 11.96/1.98  ------ Input Options Time Limit: Unbounded
% 11.96/1.98  
% 11.96/1.98  
% 11.96/1.98  ------ 
% 11.96/1.98  Current options:
% 11.96/1.98  ------ 
% 11.96/1.98  
% 11.96/1.98  
% 11.96/1.98  
% 11.96/1.98  
% 11.96/1.98  ------ Proving...
% 11.96/1.98  
% 11.96/1.98  
% 11.96/1.98  % SZS status Theorem for theBenchmark.p
% 11.96/1.98  
% 11.96/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.96/1.98  
% 11.96/1.98  fof(f7,axiom,(
% 11.96/1.98    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f22,plain,(
% 11.96/1.98    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 11.96/1.98    inference(ennf_transformation,[],[f7])).
% 11.96/1.98  
% 11.96/1.98  fof(f44,plain,(
% 11.96/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 11.96/1.98    inference(cnf_transformation,[],[f22])).
% 11.96/1.98  
% 11.96/1.98  fof(f3,axiom,(
% 11.96/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f16,plain,(
% 11.96/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.96/1.98    inference(rectify,[],[f3])).
% 11.96/1.98  
% 11.96/1.98  fof(f19,plain,(
% 11.96/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.96/1.98    inference(ennf_transformation,[],[f16])).
% 11.96/1.98  
% 11.96/1.98  fof(f27,plain,(
% 11.96/1.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.96/1.98    introduced(choice_axiom,[])).
% 11.96/1.98  
% 11.96/1.98  fof(f28,plain,(
% 11.96/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.96/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f27])).
% 11.96/1.98  
% 11.96/1.98  fof(f38,plain,(
% 11.96/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.96/1.98    inference(cnf_transformation,[],[f28])).
% 11.96/1.98  
% 11.96/1.98  fof(f13,axiom,(
% 11.96/1.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f24,plain,(
% 11.96/1.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 11.96/1.98    inference(ennf_transformation,[],[f13])).
% 11.96/1.98  
% 11.96/1.98  fof(f53,plain,(
% 11.96/1.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 11.96/1.98    inference(cnf_transformation,[],[f24])).
% 11.96/1.98  
% 11.96/1.98  fof(f11,axiom,(
% 11.96/1.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f51,plain,(
% 11.96/1.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.96/1.98    inference(cnf_transformation,[],[f11])).
% 11.96/1.98  
% 11.96/1.98  fof(f12,axiom,(
% 11.96/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f52,plain,(
% 11.96/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.96/1.98    inference(cnf_transformation,[],[f12])).
% 11.96/1.98  
% 11.96/1.98  fof(f58,plain,(
% 11.96/1.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 11.96/1.98    inference(definition_unfolding,[],[f51,f52])).
% 11.96/1.98  
% 11.96/1.98  fof(f63,plain,(
% 11.96/1.98    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 11.96/1.98    inference(definition_unfolding,[],[f53,f58])).
% 11.96/1.98  
% 11.96/1.98  fof(f46,plain,(
% 11.96/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 11.96/1.98    inference(cnf_transformation,[],[f22])).
% 11.96/1.98  
% 11.96/1.98  fof(f14,conjecture,(
% 11.96/1.98    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f15,negated_conjecture,(
% 11.96/1.98    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 11.96/1.98    inference(negated_conjecture,[],[f14])).
% 11.96/1.98  
% 11.96/1.98  fof(f25,plain,(
% 11.96/1.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 11.96/1.98    inference(ennf_transformation,[],[f15])).
% 11.96/1.98  
% 11.96/1.98  fof(f26,plain,(
% 11.96/1.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 11.96/1.98    inference(flattening,[],[f25])).
% 11.96/1.98  
% 11.96/1.98  fof(f32,plain,(
% 11.96/1.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 11.96/1.98    introduced(choice_axiom,[])).
% 11.96/1.98  
% 11.96/1.98  fof(f33,plain,(
% 11.96/1.98    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 11.96/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f32])).
% 11.96/1.98  
% 11.96/1.98  fof(f56,plain,(
% 11.96/1.98    r1_xboole_0(sK4,sK3)),
% 11.96/1.98    inference(cnf_transformation,[],[f33])).
% 11.96/1.98  
% 11.96/1.98  fof(f10,axiom,(
% 11.96/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f31,plain,(
% 11.96/1.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 11.96/1.98    inference(nnf_transformation,[],[f10])).
% 11.96/1.98  
% 11.96/1.98  fof(f49,plain,(
% 11.96/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.96/1.98    inference(cnf_transformation,[],[f31])).
% 11.96/1.98  
% 11.96/1.98  fof(f5,axiom,(
% 11.96/1.98    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f21,plain,(
% 11.96/1.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.96/1.98    inference(ennf_transformation,[],[f5])).
% 11.96/1.98  
% 11.96/1.98  fof(f42,plain,(
% 11.96/1.98    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 11.96/1.98    inference(cnf_transformation,[],[f21])).
% 11.96/1.98  
% 11.96/1.98  fof(f54,plain,(
% 11.96/1.98    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 11.96/1.98    inference(cnf_transformation,[],[f33])).
% 11.96/1.98  
% 11.96/1.98  fof(f6,axiom,(
% 11.96/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f43,plain,(
% 11.96/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.96/1.98    inference(cnf_transformation,[],[f6])).
% 11.96/1.98  
% 11.96/1.98  fof(f64,plain,(
% 11.96/1.98    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5))),
% 11.96/1.98    inference(definition_unfolding,[],[f54,f43,f58])).
% 11.96/1.98  
% 11.96/1.98  fof(f2,axiom,(
% 11.96/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f18,plain,(
% 11.96/1.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.96/1.98    inference(ennf_transformation,[],[f2])).
% 11.96/1.98  
% 11.96/1.98  fof(f35,plain,(
% 11.96/1.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.96/1.98    inference(cnf_transformation,[],[f18])).
% 11.96/1.98  
% 11.96/1.98  fof(f55,plain,(
% 11.96/1.98    r2_hidden(sK5,sK4)),
% 11.96/1.98    inference(cnf_transformation,[],[f33])).
% 11.96/1.98  
% 11.96/1.98  fof(f1,axiom,(
% 11.96/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f34,plain,(
% 11.96/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.96/1.98    inference(cnf_transformation,[],[f1])).
% 11.96/1.98  
% 11.96/1.98  fof(f59,plain,(
% 11.96/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.96/1.98    inference(definition_unfolding,[],[f34,f43,f43])).
% 11.96/1.98  
% 11.96/1.98  fof(f8,axiom,(
% 11.96/1.98    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f23,plain,(
% 11.96/1.98    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 11.96/1.98    inference(ennf_transformation,[],[f8])).
% 11.96/1.98  
% 11.96/1.98  fof(f47,plain,(
% 11.96/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 11.96/1.98    inference(cnf_transformation,[],[f23])).
% 11.96/1.98  
% 11.96/1.98  fof(f62,plain,(
% 11.96/1.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 11.96/1.98    inference(definition_unfolding,[],[f47,f43])).
% 11.96/1.98  
% 11.96/1.98  fof(f4,axiom,(
% 11.96/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.96/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.96/1.98  
% 11.96/1.98  fof(f17,plain,(
% 11.96/1.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.96/1.98    inference(rectify,[],[f4])).
% 11.96/1.98  
% 11.96/1.98  fof(f20,plain,(
% 11.96/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.96/1.98    inference(ennf_transformation,[],[f17])).
% 11.96/1.98  
% 11.96/1.98  fof(f29,plain,(
% 11.96/1.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 11.96/1.98    introduced(choice_axiom,[])).
% 11.96/1.98  
% 11.96/1.98  fof(f30,plain,(
% 11.96/1.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.96/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f29])).
% 11.96/1.98  
% 11.96/1.98  fof(f39,plain,(
% 11.96/1.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 11.96/1.98    inference(cnf_transformation,[],[f30])).
% 11.96/1.98  
% 11.96/1.98  fof(f61,plain,(
% 11.96/1.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 11.96/1.98    inference(definition_unfolding,[],[f39,f43])).
% 11.96/1.98  
% 11.96/1.98  fof(f57,plain,(
% 11.96/1.98    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 11.96/1.98    inference(cnf_transformation,[],[f33])).
% 11.96/1.98  
% 11.96/1.98  cnf(c_11,plain,
% 11.96/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.96/1.98      | ~ r1_xboole_0(X0,X2)
% 11.96/1.98      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.96/1.98      inference(cnf_transformation,[],[f44]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_2,plain,
% 11.96/1.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 11.96/1.98      inference(cnf_transformation,[],[f38]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_2415,plain,
% 11.96/1.98      ( ~ r2_hidden(X0,X1)
% 11.96/1.98      | ~ r2_hidden(X0,k2_xboole_0(X2,X3))
% 11.96/1.98      | ~ r1_xboole_0(X1,X2)
% 11.96/1.98      | ~ r1_xboole_0(X1,X3) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_11,c_2]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_16,plain,
% 11.96/1.98      ( r2_hidden(X0,X1) | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
% 11.96/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_9,plain,
% 11.96/1.98      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.96/1.98      inference(cnf_transformation,[],[f46]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_1501,plain,
% 11.96/1.98      ( r2_hidden(X0,k2_xboole_0(X1,X2))
% 11.96/1.98      | r1_xboole_0(k1_enumset1(X0,X0,X0),X2) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_16,c_9]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_10384,plain,
% 11.96/1.98      ( ~ r2_hidden(X0,X1)
% 11.96/1.98      | ~ r1_xboole_0(X1,X2)
% 11.96/1.98      | ~ r1_xboole_0(X1,X3)
% 11.96/1.98      | r1_xboole_0(k1_enumset1(X0,X0,X0),X3) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_2415,c_1501]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_18,negated_conjecture,
% 11.96/1.98      ( r1_xboole_0(sK4,sK3) ),
% 11.96/1.98      inference(cnf_transformation,[],[f56]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_50994,plain,
% 11.96/1.98      ( ~ r2_hidden(X0,sK4)
% 11.96/1.98      | r1_xboole_0(k1_enumset1(X0,X0,X0),sK3)
% 11.96/1.98      | ~ r1_xboole_0(sK4,X1) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_10384,c_18]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_1675,plain,
% 11.96/1.98      ( r2_hidden(X0,sK3) | r1_xboole_0(k1_enumset1(X0,X0,X0),sK3) ),
% 11.96/1.98      inference(instantiation,[status(thm)],[c_16]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_2303,plain,
% 11.96/1.98      ( ~ r2_hidden(X0,sK3) | ~ r2_hidden(X0,sK4) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_2,c_18]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_51585,plain,
% 11.96/1.98      ( r1_xboole_0(k1_enumset1(X0,X0,X0),sK3) | ~ r2_hidden(X0,sK4) ),
% 11.96/1.98      inference(global_propositional_subsumption,
% 11.96/1.98                [status(thm)],
% 11.96/1.98                [c_50994,c_1675,c_2303]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_51586,plain,
% 11.96/1.98      ( ~ r2_hidden(X0,sK4) | r1_xboole_0(k1_enumset1(X0,X0,X0),sK3) ),
% 11.96/1.98      inference(renaming,[status(thm)],[c_51585]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_271,plain,
% 11.96/1.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.96/1.98      theory(equality) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_15,plain,
% 11.96/1.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 11.96/1.98      inference(cnf_transformation,[],[f49]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_3666,plain,
% 11.96/1.98      ( ~ r1_tarski(X0,X1)
% 11.96/1.98      | r1_tarski(X2,k4_xboole_0(X1,X3))
% 11.96/1.98      | ~ r1_xboole_0(X1,X3)
% 11.96/1.98      | X2 != X0 ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_271,c_15]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_266,plain,( X0 = X0 ),theory(equality) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_10674,plain,
% 11.96/1.98      ( ~ r1_tarski(X0,X1)
% 11.96/1.98      | r1_tarski(X0,k4_xboole_0(X1,X2))
% 11.96/1.98      | ~ r1_xboole_0(X1,X2) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_3666,c_266]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_7,plain,
% 11.96/1.98      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 11.96/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_20674,plain,
% 11.96/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_10674,c_7]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_51605,plain,
% 11.96/1.98      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
% 11.96/1.98      | ~ r2_hidden(X1,sK4)
% 11.96/1.98      | r1_xboole_0(X0,sK3) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_51586,c_20674]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_20,negated_conjecture,
% 11.96/1.98      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) ),
% 11.96/1.98      inference(cnf_transformation,[],[f64]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_52434,plain,
% 11.96/1.98      ( ~ r2_hidden(sK5,sK4)
% 11.96/1.98      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_51605,c_20]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_751,plain,
% 11.96/1.98      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) = iProver_top ),
% 11.96/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_753,plain,
% 11.96/1.98      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 11.96/1.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_1,plain,
% 11.96/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.96/1.98      inference(cnf_transformation,[],[f35]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_770,plain,
% 11.96/1.98      ( r1_xboole_0(X0,X1) != iProver_top
% 11.96/1.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 11.96/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_1598,plain,
% 11.96/1.98      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 11.96/1.98      inference(superposition,[status(thm)],[c_753,c_770]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_755,plain,
% 11.96/1.98      ( r2_hidden(X0,X1) = iProver_top
% 11.96/1.98      | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
% 11.96/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_756,plain,
% 11.96/1.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 11.96/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_1465,plain,
% 11.96/1.98      ( k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
% 11.96/1.98      | r2_hidden(X0,X1) = iProver_top ),
% 11.96/1.98      inference(superposition,[status(thm)],[c_755,c_756]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_19,negated_conjecture,
% 11.96/1.98      ( r2_hidden(sK5,sK4) ),
% 11.96/1.98      inference(cnf_transformation,[],[f55]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_752,plain,
% 11.96/1.98      ( r2_hidden(sK5,sK4) = iProver_top ),
% 11.96/1.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_769,plain,
% 11.96/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.96/1.98      | r2_hidden(X0,X2) != iProver_top
% 11.96/1.98      | r1_xboole_0(X2,X1) != iProver_top ),
% 11.96/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_5415,plain,
% 11.96/1.98      ( r2_hidden(sK5,X0) != iProver_top
% 11.96/1.98      | r1_xboole_0(X0,sK4) != iProver_top ),
% 11.96/1.98      inference(superposition,[status(thm)],[c_752,c_769]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_10477,plain,
% 11.96/1.98      ( k4_xboole_0(k1_enumset1(sK5,sK5,sK5),X0) = k1_enumset1(sK5,sK5,sK5)
% 11.96/1.98      | r1_xboole_0(X0,sK4) != iProver_top ),
% 11.96/1.98      inference(superposition,[status(thm)],[c_1465,c_5415]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_11526,plain,
% 11.96/1.98      ( k4_xboole_0(k1_enumset1(sK5,sK5,sK5),sK3) = k1_enumset1(sK5,sK5,sK5) ),
% 11.96/1.98      inference(superposition,[status(thm)],[c_1598,c_10477]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_764,plain,
% 11.96/1.98      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 11.96/1.98      | r1_xboole_0(X0,X2) = iProver_top ),
% 11.96/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_11897,plain,
% 11.96/1.98      ( r1_tarski(X0,k1_enumset1(sK5,sK5,sK5)) != iProver_top
% 11.96/1.98      | r1_xboole_0(X0,sK3) = iProver_top ),
% 11.96/1.98      inference(superposition,[status(thm)],[c_11526,c_764]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_13112,plain,
% 11.96/1.98      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = iProver_top ),
% 11.96/1.98      inference(superposition,[status(thm)],[c_751,c_11897]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_13113,plain,
% 11.96/1.98      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) ),
% 11.96/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_13112]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_54344,plain,
% 11.96/1.98      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) ),
% 11.96/1.98      inference(global_propositional_subsumption,
% 11.96/1.98                [status(thm)],
% 11.96/1.98                [c_52434,c_13113]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_269,plain,
% 11.96/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.96/1.98      theory(equality) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_3491,plain,
% 11.96/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_269,c_266]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_0,plain,
% 11.96/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.96/1.98      inference(cnf_transformation,[],[f59]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_4566,plain,
% 11.96/1.98      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
% 11.96/1.98      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_3491,c_0]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_54364,plain,
% 11.96/1.98      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)),sK3) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_54344,c_4566]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_12,plain,
% 11.96/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.96/1.98      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 11.96/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_2291,plain,
% 11.96/1.98      ( ~ r2_hidden(X0,X1)
% 11.96/1.98      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
% 11.96/1.98      | ~ r1_xboole_0(X1,X2) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_6,plain,
% 11.96/1.98      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 11.96/1.98      | r1_xboole_0(X0,X1) ),
% 11.96/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_7509,plain,
% 11.96/1.98      ( ~ r2_hidden(sK1(X0,X1),X2)
% 11.96/1.98      | ~ r1_xboole_0(X2,X0)
% 11.96/1.98      | r1_xboole_0(X0,X1) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_2291,c_6]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_15558,plain,
% 11.96/1.98      ( r1_xboole_0(X0,X1)
% 11.96/1.98      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_7509,c_6]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_55401,plain,
% 11.96/1.98      ( r1_xboole_0(sK3,sK2) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_54364,c_15558]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_1040,plain,
% 11.96/1.98      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 11.96/1.98      | ~ r1_xboole_0(sK3,sK4)
% 11.96/1.98      | ~ r1_xboole_0(sK3,sK2) ),
% 11.96/1.98      inference(instantiation,[status(thm)],[c_11]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_933,plain,
% 11.96/1.98      ( r1_xboole_0(sK3,sK4) ),
% 11.96/1.98      inference(resolution,[status(thm)],[c_1,c_18]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_902,plain,
% 11.96/1.98      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 11.96/1.98      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 11.96/1.98      inference(instantiation,[status(thm)],[c_1]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(c_17,negated_conjecture,
% 11.96/1.98      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 11.96/1.98      inference(cnf_transformation,[],[f57]) ).
% 11.96/1.98  
% 11.96/1.98  cnf(contradiction,plain,
% 11.96/1.98      ( $false ),
% 11.96/1.98      inference(minisat,[status(thm)],[c_55401,c_1040,c_933,c_902,c_17]) ).
% 11.96/1.98  
% 11.96/1.98  
% 11.96/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.96/1.98  
% 11.96/1.98  ------                               Statistics
% 11.96/1.98  
% 11.96/1.98  ------ Selected
% 11.96/1.98  
% 11.96/1.98  total_time:                             1.485
% 11.96/1.98  
%------------------------------------------------------------------------------
