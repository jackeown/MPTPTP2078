%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:39 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 171 expanded)
%              Number of clauses        :   41 (  52 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  272 ( 524 expanded)
%              Number of equality atoms :   74 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

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
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f25])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)
      & r1_xboole_0(sK5,sK4)
      & r2_hidden(sK6,sK5)
      & r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)
    & r1_xboole_0(sK5,sK4)
    & r2_hidden(sK6,sK5)
    & r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f33])).

fof(f54,plain,(
    r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f64,plain,(
    r1_tarski(k3_xboole_0(sK3,sK4),k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f67,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    r1_xboole_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2628,plain,
    ( ~ r1_xboole_0(sK5,X0)
    | r1_xboole_0(sK5,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5448,plain,
    ( r1_xboole_0(sK5,k3_xboole_0(sK4,X0))
    | ~ r1_xboole_0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_2628])).

cnf(c_21569,plain,
    ( r1_xboole_0(sK5,k3_xboole_0(sK4,sK3))
    | ~ r1_xboole_0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_5448])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1536,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK5)
    | X0 != X2
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_3532,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | X1 != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_8443,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK1(sK4,sK3),sK5)
    | sK1(sK4,sK3) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3532])).

cnf(c_8447,plain,
    ( r2_hidden(sK1(sK4,sK3),sK5)
    | ~ r2_hidden(sK6,sK5)
    | sK1(sK4,sK3) != sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_8443])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1911,plain,
    ( ~ r1_xboole_0(X0,k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK1(sK4,sK3),X0)
    | ~ r2_hidden(sK1(sK4,sK3),k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8442,plain,
    ( ~ r1_xboole_0(sK5,k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK1(sK4,sK3),k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK1(sK4,sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_696,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2438,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_696])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK3,sK4),k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_213,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k2_enumset1(sK6,sK6,sK6,sK6) != X2
    | k3_xboole_0(sK3,sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_214,plain,
    ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6))
    | ~ r2_hidden(X0,k3_xboole_0(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_684,plain,
    ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(X0,k3_xboole_0(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_688,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1391,plain,
    ( sK6 = X0
    | r2_hidden(X0,k3_xboole_0(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_688])).

cnf(c_3403,plain,
    ( sK1(sK4,sK3) = sK6
    | r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2438,c_1391])).

cnf(c_1162,plain,
    ( r1_xboole_0(sK4,sK3)
    | r2_hidden(sK1(sK4,sK3),k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_353,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1112,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_933,plain,
    ( r1_xboole_0(sK4,k2_xboole_0(sK3,sK5))
    | ~ r1_xboole_0(sK4,sK5)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_934,plain,
    ( r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = iProver_top
    | r1_xboole_0(sK4,sK5) != iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_856,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_2,c_17])).

cnf(c_857,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_826,plain,
    ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)
    | ~ r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_827,plain,
    ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) = iProver_top
    | r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_826])).

cnf(c_16,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,plain,
    ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21569,c_8447,c_8442,c_3403,c_1162,c_1112,c_934,c_933,c_857,c_856,c_827,c_826,c_23,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:14:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.34/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/1.50  
% 7.34/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.34/1.50  
% 7.34/1.50  ------  iProver source info
% 7.34/1.50  
% 7.34/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.34/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.34/1.50  git: non_committed_changes: false
% 7.34/1.50  git: last_make_outside_of_git: false
% 7.34/1.50  
% 7.34/1.50  ------ 
% 7.34/1.50  ------ Parsing...
% 7.34/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.34/1.50  
% 7.34/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.34/1.50  
% 7.34/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.34/1.50  
% 7.34/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.34/1.50  ------ Proving...
% 7.34/1.50  ------ Problem Properties 
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  clauses                                 19
% 7.34/1.50  conjectures                             3
% 7.34/1.50  EPR                                     4
% 7.34/1.50  Horn                                    15
% 7.34/1.50  unary                                   5
% 7.34/1.50  binary                                  10
% 7.34/1.50  lits                                    37
% 7.34/1.50  lits eq                                 6
% 7.34/1.50  fd_pure                                 0
% 7.34/1.50  fd_pseudo                               0
% 7.34/1.50  fd_cond                                 0
% 7.34/1.50  fd_pseudo_cond                          2
% 7.34/1.50  AC symbols                              0
% 7.34/1.50  
% 7.34/1.50  ------ Input Options Time Limit: Unbounded
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  ------ 
% 7.34/1.50  Current options:
% 7.34/1.50  ------ 
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  ------ Proving...
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  % SZS status Theorem for theBenchmark.p
% 7.34/1.50  
% 7.34/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.34/1.50  
% 7.34/1.50  fof(f7,axiom,(
% 7.34/1.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f22,plain,(
% 7.34/1.50    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 7.34/1.50    inference(ennf_transformation,[],[f7])).
% 7.34/1.50  
% 7.34/1.50  fof(f46,plain,(
% 7.34/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 7.34/1.50    inference(cnf_transformation,[],[f22])).
% 7.34/1.50  
% 7.34/1.50  fof(f4,axiom,(
% 7.34/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f14,plain,(
% 7.34/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.34/1.50    inference(rectify,[],[f4])).
% 7.34/1.50  
% 7.34/1.50  fof(f19,plain,(
% 7.34/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.34/1.50    inference(ennf_transformation,[],[f14])).
% 7.34/1.50  
% 7.34/1.50  fof(f25,plain,(
% 7.34/1.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.34/1.50    introduced(choice_axiom,[])).
% 7.34/1.50  
% 7.34/1.50  fof(f26,plain,(
% 7.34/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.34/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f25])).
% 7.34/1.50  
% 7.34/1.50  fof(f40,plain,(
% 7.34/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f26])).
% 7.34/1.50  
% 7.34/1.50  fof(f1,axiom,(
% 7.34/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f35,plain,(
% 7.34/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f1])).
% 7.34/1.50  
% 7.34/1.50  fof(f5,axiom,(
% 7.34/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f15,plain,(
% 7.34/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.34/1.50    inference(rectify,[],[f5])).
% 7.34/1.50  
% 7.34/1.50  fof(f20,plain,(
% 7.34/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.34/1.50    inference(ennf_transformation,[],[f15])).
% 7.34/1.50  
% 7.34/1.50  fof(f27,plain,(
% 7.34/1.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.34/1.50    introduced(choice_axiom,[])).
% 7.34/1.50  
% 7.34/1.50  fof(f28,plain,(
% 7.34/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.34/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f27])).
% 7.34/1.50  
% 7.34/1.50  fof(f41,plain,(
% 7.34/1.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f28])).
% 7.34/1.50  
% 7.34/1.50  fof(f2,axiom,(
% 7.34/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f16,plain,(
% 7.34/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.34/1.50    inference(unused_predicate_definition_removal,[],[f2])).
% 7.34/1.50  
% 7.34/1.50  fof(f17,plain,(
% 7.34/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 7.34/1.50    inference(ennf_transformation,[],[f16])).
% 7.34/1.50  
% 7.34/1.50  fof(f36,plain,(
% 7.34/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f17])).
% 7.34/1.50  
% 7.34/1.50  fof(f12,conjecture,(
% 7.34/1.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f13,negated_conjecture,(
% 7.34/1.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.34/1.50    inference(negated_conjecture,[],[f12])).
% 7.34/1.50  
% 7.34/1.50  fof(f23,plain,(
% 7.34/1.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.34/1.50    inference(ennf_transformation,[],[f13])).
% 7.34/1.50  
% 7.34/1.50  fof(f24,plain,(
% 7.34/1.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.34/1.50    inference(flattening,[],[f23])).
% 7.34/1.50  
% 7.34/1.50  fof(f33,plain,(
% 7.34/1.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) & r1_xboole_0(sK5,sK4) & r2_hidden(sK6,sK5) & r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6)))),
% 7.34/1.50    introduced(choice_axiom,[])).
% 7.34/1.50  
% 7.34/1.50  fof(f34,plain,(
% 7.34/1.50    ~r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) & r1_xboole_0(sK5,sK4) & r2_hidden(sK6,sK5) & r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6))),
% 7.34/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f33])).
% 7.34/1.50  
% 7.34/1.50  fof(f54,plain,(
% 7.34/1.50    r1_tarski(k3_xboole_0(sK3,sK4),k1_tarski(sK6))),
% 7.34/1.50    inference(cnf_transformation,[],[f34])).
% 7.34/1.50  
% 7.34/1.50  fof(f9,axiom,(
% 7.34/1.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f51,plain,(
% 7.34/1.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f9])).
% 7.34/1.50  
% 7.34/1.50  fof(f10,axiom,(
% 7.34/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f52,plain,(
% 7.34/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f10])).
% 7.34/1.50  
% 7.34/1.50  fof(f11,axiom,(
% 7.34/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f53,plain,(
% 7.34/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f11])).
% 7.34/1.50  
% 7.34/1.50  fof(f58,plain,(
% 7.34/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.34/1.50    inference(definition_unfolding,[],[f52,f53])).
% 7.34/1.50  
% 7.34/1.50  fof(f59,plain,(
% 7.34/1.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.34/1.50    inference(definition_unfolding,[],[f51,f58])).
% 7.34/1.50  
% 7.34/1.50  fof(f64,plain,(
% 7.34/1.50    r1_tarski(k3_xboole_0(sK3,sK4),k2_enumset1(sK6,sK6,sK6,sK6))),
% 7.34/1.50    inference(definition_unfolding,[],[f54,f59])).
% 7.34/1.50  
% 7.34/1.50  fof(f8,axiom,(
% 7.34/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f29,plain,(
% 7.34/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.34/1.50    inference(nnf_transformation,[],[f8])).
% 7.34/1.50  
% 7.34/1.50  fof(f30,plain,(
% 7.34/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.34/1.50    inference(rectify,[],[f29])).
% 7.34/1.50  
% 7.34/1.50  fof(f31,plain,(
% 7.34/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.34/1.50    introduced(choice_axiom,[])).
% 7.34/1.50  
% 7.34/1.50  fof(f32,plain,(
% 7.34/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.34/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 7.34/1.50  
% 7.34/1.50  fof(f47,plain,(
% 7.34/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.34/1.50    inference(cnf_transformation,[],[f32])).
% 7.34/1.50  
% 7.34/1.50  fof(f63,plain,(
% 7.34/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.34/1.50    inference(definition_unfolding,[],[f47,f59])).
% 7.34/1.50  
% 7.34/1.50  fof(f67,plain,(
% 7.34/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.34/1.50    inference(equality_resolution,[],[f63])).
% 7.34/1.50  
% 7.34/1.50  fof(f6,axiom,(
% 7.34/1.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f21,plain,(
% 7.34/1.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.34/1.50    inference(ennf_transformation,[],[f6])).
% 7.34/1.50  
% 7.34/1.50  fof(f43,plain,(
% 7.34/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.34/1.50    inference(cnf_transformation,[],[f21])).
% 7.34/1.50  
% 7.34/1.50  fof(f3,axiom,(
% 7.34/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f18,plain,(
% 7.34/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.34/1.50    inference(ennf_transformation,[],[f3])).
% 7.34/1.50  
% 7.34/1.50  fof(f37,plain,(
% 7.34/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f18])).
% 7.34/1.50  
% 7.34/1.50  fof(f56,plain,(
% 7.34/1.50    r1_xboole_0(sK5,sK4)),
% 7.34/1.50    inference(cnf_transformation,[],[f34])).
% 7.34/1.50  
% 7.34/1.50  fof(f57,plain,(
% 7.34/1.50    ~r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)),
% 7.34/1.50    inference(cnf_transformation,[],[f34])).
% 7.34/1.50  
% 7.34/1.50  fof(f55,plain,(
% 7.34/1.50    r2_hidden(sK6,sK5)),
% 7.34/1.50    inference(cnf_transformation,[],[f34])).
% 7.34/1.50  
% 7.34/1.50  cnf(c_11,plain,
% 7.34/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.34/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.34/1.50  
% 7.34/1.50  cnf(c_2628,plain,
% 7.34/1.50      ( ~ r1_xboole_0(sK5,X0) | r1_xboole_0(sK5,k3_xboole_0(X0,X1)) ),
% 7.34/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_5448,plain,
% 7.34/1.51      ( r1_xboole_0(sK5,k3_xboole_0(sK4,X0)) | ~ r1_xboole_0(sK5,sK4) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_2628]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_21569,plain,
% 7.34/1.51      ( r1_xboole_0(sK5,k3_xboole_0(sK4,sK3)) | ~ r1_xboole_0(sK5,sK4) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_5448]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_356,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.34/1.51      theory(equality) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1536,plain,
% 7.34/1.51      ( r2_hidden(X0,X1) | ~ r2_hidden(X2,sK5) | X0 != X2 | X1 != sK5 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_356]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3532,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,sK5) | r2_hidden(X1,sK5) | X1 != X0 | sK5 != sK5 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_1536]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_8443,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,sK5)
% 7.34/1.51      | r2_hidden(sK1(sK4,sK3),sK5)
% 7.34/1.51      | sK1(sK4,sK3) != X0
% 7.34/1.51      | sK5 != sK5 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_3532]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_8447,plain,
% 7.34/1.51      ( r2_hidden(sK1(sK4,sK3),sK5)
% 7.34/1.51      | ~ r2_hidden(sK6,sK5)
% 7.34/1.51      | sK1(sK4,sK3) != sK6
% 7.34/1.51      | sK5 != sK5 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_8443]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3,plain,
% 7.34/1.51      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 7.34/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1911,plain,
% 7.34/1.51      ( ~ r1_xboole_0(X0,k3_xboole_0(sK4,sK3))
% 7.34/1.51      | ~ r2_hidden(sK1(sK4,sK3),X0)
% 7.34/1.51      | ~ r2_hidden(sK1(sK4,sK3),k3_xboole_0(sK4,sK3)) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_8442,plain,
% 7.34/1.51      ( ~ r1_xboole_0(sK5,k3_xboole_0(sK4,sK3))
% 7.34/1.51      | ~ r2_hidden(sK1(sK4,sK3),k3_xboole_0(sK4,sK3))
% 7.34/1.51      | ~ r2_hidden(sK1(sK4,sK3),sK5) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_1911]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_0,plain,
% 7.34/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.34/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_7,plain,
% 7.34/1.51      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 7.34/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_696,plain,
% 7.34/1.51      ( r1_xboole_0(X0,X1) = iProver_top
% 7.34/1.51      | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_2438,plain,
% 7.34/1.51      ( r1_xboole_0(X0,X1) = iProver_top
% 7.34/1.51      | r2_hidden(sK1(X0,X1),k3_xboole_0(X1,X0)) = iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_0,c_696]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1,plain,
% 7.34/1.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.34/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_19,negated_conjecture,
% 7.34/1.51      ( r1_tarski(k3_xboole_0(sK3,sK4),k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 7.34/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_213,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,X1)
% 7.34/1.51      | r2_hidden(X0,X2)
% 7.34/1.51      | k2_enumset1(sK6,sK6,sK6,sK6) != X2
% 7.34/1.51      | k3_xboole_0(sK3,sK4) != X1 ),
% 7.34/1.51      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_214,plain,
% 7.34/1.51      ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6))
% 7.34/1.51      | ~ r2_hidden(X0,k3_xboole_0(sK3,sK4)) ),
% 7.34/1.51      inference(unflattening,[status(thm)],[c_213]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_684,plain,
% 7.34/1.51      ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
% 7.34/1.51      | r2_hidden(X0,k3_xboole_0(sK3,sK4)) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_15,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.34/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_688,plain,
% 7.34/1.51      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1391,plain,
% 7.34/1.51      ( sK6 = X0 | r2_hidden(X0,k3_xboole_0(sK3,sK4)) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_684,c_688]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3403,plain,
% 7.34/1.51      ( sK1(sK4,sK3) = sK6 | r1_xboole_0(sK4,sK3) = iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_2438,c_1391]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1162,plain,
% 7.34/1.51      ( r1_xboole_0(sK4,sK3)
% 7.34/1.51      | r2_hidden(sK1(sK4,sK3),k3_xboole_0(sK4,sK3)) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_353,plain,( X0 = X0 ),theory(equality) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1112,plain,
% 7.34/1.51      ( sK5 = sK5 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_353]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_10,plain,
% 7.34/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.34/1.51      | ~ r1_xboole_0(X0,X2)
% 7.34/1.51      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.34/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_933,plain,
% 7.34/1.51      ( r1_xboole_0(sK4,k2_xboole_0(sK3,sK5))
% 7.34/1.51      | ~ r1_xboole_0(sK4,sK5)
% 7.34/1.51      | ~ r1_xboole_0(sK4,sK3) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_934,plain,
% 7.34/1.51      ( r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = iProver_top
% 7.34/1.51      | r1_xboole_0(sK4,sK5) != iProver_top
% 7.34/1.51      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_2,plain,
% 7.34/1.51      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.34/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_17,negated_conjecture,
% 7.34/1.51      ( r1_xboole_0(sK5,sK4) ),
% 7.34/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_856,plain,
% 7.34/1.51      ( r1_xboole_0(sK4,sK5) ),
% 7.34/1.51      inference(resolution,[status(thm)],[c_2,c_17]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_857,plain,
% 7.34/1.51      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_826,plain,
% 7.34/1.51      ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4)
% 7.34/1.51      | ~ r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_827,plain,
% 7.34/1.51      ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) = iProver_top
% 7.34/1.51      | r1_xboole_0(sK4,k2_xboole_0(sK3,sK5)) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_826]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_16,negated_conjecture,
% 7.34/1.51      ( ~ r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) ),
% 7.34/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_23,plain,
% 7.34/1.51      ( r1_xboole_0(k2_xboole_0(sK3,sK5),sK4) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_18,negated_conjecture,
% 7.34/1.51      ( r2_hidden(sK6,sK5) ),
% 7.34/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(contradiction,plain,
% 7.34/1.51      ( $false ),
% 7.34/1.51      inference(minisat,
% 7.34/1.51                [status(thm)],
% 7.34/1.51                [c_21569,c_8447,c_8442,c_3403,c_1162,c_1112,c_934,c_933,
% 7.34/1.51                 c_857,c_856,c_827,c_826,c_23,c_16,c_17,c_18]) ).
% 7.34/1.51  
% 7.34/1.51  
% 7.34/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.34/1.51  
% 7.34/1.51  ------                               Statistics
% 7.34/1.51  
% 7.34/1.51  ------ Selected
% 7.34/1.51  
% 7.34/1.51  total_time:                             0.615
% 7.34/1.51  
%------------------------------------------------------------------------------
