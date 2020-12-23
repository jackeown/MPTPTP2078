%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:42 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 144 expanded)
%              Number of clauses        :   43 (  46 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  219 ( 349 expanded)
%              Number of equality atoms :   57 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f28])).

fof(f45,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f55,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f47,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1051,plain,
    ( ~ r1_xboole_0(sK2,X0)
    | k3_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_xboole_0(sK2,X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3087,plain,
    ( ~ r1_xboole_0(sK2,X0)
    | k3_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,sK3))) = k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_8755,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | k3_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) = k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3087])).

cnf(c_325,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_765,plain,
    ( k3_xboole_0(X0,X1) != X2
    | k3_xboole_0(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_1638,plain,
    ( k3_xboole_0(X0,X1) != k3_xboole_0(sK2,sK3)
    | k3_xboole_0(X0,X1) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_3086,plain,
    ( k3_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,sK3))) != k3_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,sK3))) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_5179,plain,
    ( k3_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) != k3_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3086])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1321,plain,
    ( r1_xboole_0(sK2,X0)
    | k3_xboole_0(sK2,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2606,plain,
    ( r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)))
    | k3_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_860,plain,
    ( ~ r1_xboole_0(X0,sK2)
    | r1_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1652,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_826,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_990,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_1507,plain,
    ( k3_xboole_0(sK2,sK3) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_1053,plain,
    ( r1_xboole_0(X0,sK2)
    | ~ r1_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1310,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2)
    | ~ r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_884,plain,
    ( r1_xboole_0(X0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(X0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1139,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK2)
    | r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_324,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_991,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_187,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | k2_enumset1(sK4,sK4,sK4,sK4) != X0
    | k3_xboole_0(sK1,sK2) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_188,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)
    | r1_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(unflattening,[status(thm)],[c_187])).

cnf(c_897,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2)
    | r1_xboole_0(k3_xboole_0(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_787,plain,
    ( r2_hidden(X0,sK2)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_789,plain,
    ( r2_hidden(sK4,sK2)
    | r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_771,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_745,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_747,plain,
    ( ~ r2_hidden(sK4,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_738,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8755,c_5179,c_2606,c_1652,c_1507,c_1310,c_1139,c_991,c_897,c_789,c_771,c_747,c_738,c_11,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.28/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.00  
% 3.28/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.28/1.00  
% 3.28/1.00  ------  iProver source info
% 3.28/1.00  
% 3.28/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.28/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.28/1.00  git: non_committed_changes: false
% 3.28/1.00  git: last_make_outside_of_git: false
% 3.28/1.00  
% 3.28/1.00  ------ 
% 3.28/1.00  
% 3.28/1.00  ------ Input Options
% 3.28/1.00  
% 3.28/1.00  --out_options                           all
% 3.28/1.00  --tptp_safe_out                         true
% 3.28/1.00  --problem_path                          ""
% 3.28/1.00  --include_path                          ""
% 3.28/1.00  --clausifier                            res/vclausify_rel
% 3.28/1.00  --clausifier_options                    --mode clausify
% 3.28/1.00  --stdin                                 false
% 3.28/1.00  --stats_out                             all
% 3.28/1.00  
% 3.28/1.00  ------ General Options
% 3.28/1.00  
% 3.28/1.00  --fof                                   false
% 3.28/1.00  --time_out_real                         305.
% 3.28/1.00  --time_out_virtual                      -1.
% 3.28/1.00  --symbol_type_check                     false
% 3.28/1.00  --clausify_out                          false
% 3.28/1.00  --sig_cnt_out                           false
% 3.28/1.00  --trig_cnt_out                          false
% 3.28/1.00  --trig_cnt_out_tolerance                1.
% 3.28/1.00  --trig_cnt_out_sk_spl                   false
% 3.28/1.00  --abstr_cl_out                          false
% 3.28/1.00  
% 3.28/1.00  ------ Global Options
% 3.28/1.00  
% 3.28/1.00  --schedule                              default
% 3.28/1.00  --add_important_lit                     false
% 3.28/1.00  --prop_solver_per_cl                    1000
% 3.28/1.00  --min_unsat_core                        false
% 3.28/1.00  --soft_assumptions                      false
% 3.28/1.00  --soft_lemma_size                       3
% 3.28/1.00  --prop_impl_unit_size                   0
% 3.28/1.00  --prop_impl_unit                        []
% 3.28/1.00  --share_sel_clauses                     true
% 3.28/1.00  --reset_solvers                         false
% 3.28/1.00  --bc_imp_inh                            [conj_cone]
% 3.28/1.00  --conj_cone_tolerance                   3.
% 3.28/1.00  --extra_neg_conj                        none
% 3.28/1.00  --large_theory_mode                     true
% 3.28/1.00  --prolific_symb_bound                   200
% 3.28/1.00  --lt_threshold                          2000
% 3.28/1.00  --clause_weak_htbl                      true
% 3.28/1.00  --gc_record_bc_elim                     false
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing Options
% 3.28/1.00  
% 3.28/1.00  --preprocessing_flag                    true
% 3.28/1.00  --time_out_prep_mult                    0.1
% 3.28/1.00  --splitting_mode                        input
% 3.28/1.00  --splitting_grd                         true
% 3.28/1.00  --splitting_cvd                         false
% 3.28/1.00  --splitting_cvd_svl                     false
% 3.28/1.00  --splitting_nvd                         32
% 3.28/1.00  --sub_typing                            true
% 3.28/1.00  --prep_gs_sim                           true
% 3.28/1.00  --prep_unflatten                        true
% 3.28/1.00  --prep_res_sim                          true
% 3.28/1.00  --prep_upred                            true
% 3.28/1.00  --prep_sem_filter                       exhaustive
% 3.28/1.00  --prep_sem_filter_out                   false
% 3.28/1.00  --pred_elim                             true
% 3.28/1.00  --res_sim_input                         true
% 3.28/1.00  --eq_ax_congr_red                       true
% 3.28/1.00  --pure_diseq_elim                       true
% 3.28/1.00  --brand_transform                       false
% 3.28/1.00  --non_eq_to_eq                          false
% 3.28/1.00  --prep_def_merge                        true
% 3.28/1.00  --prep_def_merge_prop_impl              false
% 3.28/1.00  --prep_def_merge_mbd                    true
% 3.28/1.00  --prep_def_merge_tr_red                 false
% 3.28/1.00  --prep_def_merge_tr_cl                  false
% 3.28/1.00  --smt_preprocessing                     true
% 3.28/1.00  --smt_ac_axioms                         fast
% 3.28/1.00  --preprocessed_out                      false
% 3.28/1.00  --preprocessed_stats                    false
% 3.28/1.00  
% 3.28/1.00  ------ Abstraction refinement Options
% 3.28/1.00  
% 3.28/1.00  --abstr_ref                             []
% 3.28/1.00  --abstr_ref_prep                        false
% 3.28/1.00  --abstr_ref_until_sat                   false
% 3.28/1.00  --abstr_ref_sig_restrict                funpre
% 3.28/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/1.00  --abstr_ref_under                       []
% 3.28/1.00  
% 3.28/1.00  ------ SAT Options
% 3.28/1.00  
% 3.28/1.00  --sat_mode                              false
% 3.28/1.00  --sat_fm_restart_options                ""
% 3.28/1.00  --sat_gr_def                            false
% 3.28/1.00  --sat_epr_types                         true
% 3.28/1.00  --sat_non_cyclic_types                  false
% 3.28/1.00  --sat_finite_models                     false
% 3.28/1.00  --sat_fm_lemmas                         false
% 3.28/1.00  --sat_fm_prep                           false
% 3.28/1.00  --sat_fm_uc_incr                        true
% 3.28/1.00  --sat_out_model                         small
% 3.28/1.00  --sat_out_clauses                       false
% 3.28/1.00  
% 3.28/1.00  ------ QBF Options
% 3.28/1.00  
% 3.28/1.00  --qbf_mode                              false
% 3.28/1.00  --qbf_elim_univ                         false
% 3.28/1.00  --qbf_dom_inst                          none
% 3.28/1.00  --qbf_dom_pre_inst                      false
% 3.28/1.00  --qbf_sk_in                             false
% 3.28/1.00  --qbf_pred_elim                         true
% 3.28/1.00  --qbf_split                             512
% 3.28/1.00  
% 3.28/1.00  ------ BMC1 Options
% 3.28/1.00  
% 3.28/1.00  --bmc1_incremental                      false
% 3.28/1.00  --bmc1_axioms                           reachable_all
% 3.28/1.00  --bmc1_min_bound                        0
% 3.28/1.00  --bmc1_max_bound                        -1
% 3.28/1.00  --bmc1_max_bound_default                -1
% 3.28/1.00  --bmc1_symbol_reachability              true
% 3.28/1.00  --bmc1_property_lemmas                  false
% 3.28/1.00  --bmc1_k_induction                      false
% 3.28/1.00  --bmc1_non_equiv_states                 false
% 3.28/1.00  --bmc1_deadlock                         false
% 3.28/1.00  --bmc1_ucm                              false
% 3.28/1.00  --bmc1_add_unsat_core                   none
% 3.28/1.00  --bmc1_unsat_core_children              false
% 3.28/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/1.00  --bmc1_out_stat                         full
% 3.28/1.00  --bmc1_ground_init                      false
% 3.28/1.00  --bmc1_pre_inst_next_state              false
% 3.28/1.00  --bmc1_pre_inst_state                   false
% 3.28/1.00  --bmc1_pre_inst_reach_state             false
% 3.28/1.00  --bmc1_out_unsat_core                   false
% 3.28/1.00  --bmc1_aig_witness_out                  false
% 3.28/1.00  --bmc1_verbose                          false
% 3.28/1.00  --bmc1_dump_clauses_tptp                false
% 3.28/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.28/1.00  --bmc1_dump_file                        -
% 3.28/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.28/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.28/1.00  --bmc1_ucm_extend_mode                  1
% 3.28/1.00  --bmc1_ucm_init_mode                    2
% 3.28/1.00  --bmc1_ucm_cone_mode                    none
% 3.28/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.28/1.00  --bmc1_ucm_relax_model                  4
% 3.28/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.28/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/1.00  --bmc1_ucm_layered_model                none
% 3.28/1.00  --bmc1_ucm_max_lemma_size               10
% 3.28/1.00  
% 3.28/1.00  ------ AIG Options
% 3.28/1.00  
% 3.28/1.00  --aig_mode                              false
% 3.28/1.00  
% 3.28/1.00  ------ Instantiation Options
% 3.28/1.00  
% 3.28/1.00  --instantiation_flag                    true
% 3.28/1.00  --inst_sos_flag                         false
% 3.28/1.00  --inst_sos_phase                        true
% 3.28/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/1.00  --inst_lit_sel_side                     num_symb
% 3.28/1.00  --inst_solver_per_active                1400
% 3.28/1.00  --inst_solver_calls_frac                1.
% 3.28/1.00  --inst_passive_queue_type               priority_queues
% 3.28/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/1.00  --inst_passive_queues_freq              [25;2]
% 3.28/1.00  --inst_dismatching                      true
% 3.28/1.00  --inst_eager_unprocessed_to_passive     true
% 3.28/1.00  --inst_prop_sim_given                   true
% 3.28/1.00  --inst_prop_sim_new                     false
% 3.28/1.00  --inst_subs_new                         false
% 3.28/1.00  --inst_eq_res_simp                      false
% 3.28/1.00  --inst_subs_given                       false
% 3.28/1.00  --inst_orphan_elimination               true
% 3.28/1.00  --inst_learning_loop_flag               true
% 3.28/1.00  --inst_learning_start                   3000
% 3.28/1.00  --inst_learning_factor                  2
% 3.28/1.00  --inst_start_prop_sim_after_learn       3
% 3.28/1.00  --inst_sel_renew                        solver
% 3.28/1.00  --inst_lit_activity_flag                true
% 3.28/1.00  --inst_restr_to_given                   false
% 3.28/1.00  --inst_activity_threshold               500
% 3.28/1.00  --inst_out_proof                        true
% 3.28/1.00  
% 3.28/1.00  ------ Resolution Options
% 3.28/1.00  
% 3.28/1.00  --resolution_flag                       true
% 3.28/1.00  --res_lit_sel                           adaptive
% 3.28/1.00  --res_lit_sel_side                      none
% 3.28/1.00  --res_ordering                          kbo
% 3.28/1.00  --res_to_prop_solver                    active
% 3.28/1.00  --res_prop_simpl_new                    false
% 3.28/1.00  --res_prop_simpl_given                  true
% 3.28/1.00  --res_passive_queue_type                priority_queues
% 3.28/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/1.00  --res_passive_queues_freq               [15;5]
% 3.28/1.00  --res_forward_subs                      full
% 3.28/1.00  --res_backward_subs                     full
% 3.28/1.00  --res_forward_subs_resolution           true
% 3.28/1.00  --res_backward_subs_resolution          true
% 3.28/1.00  --res_orphan_elimination                true
% 3.28/1.00  --res_time_limit                        2.
% 3.28/1.00  --res_out_proof                         true
% 3.28/1.00  
% 3.28/1.00  ------ Superposition Options
% 3.28/1.00  
% 3.28/1.00  --superposition_flag                    true
% 3.28/1.00  --sup_passive_queue_type                priority_queues
% 3.28/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.28/1.00  --demod_completeness_check              fast
% 3.28/1.00  --demod_use_ground                      true
% 3.28/1.00  --sup_to_prop_solver                    passive
% 3.28/1.00  --sup_prop_simpl_new                    true
% 3.28/1.00  --sup_prop_simpl_given                  true
% 3.28/1.00  --sup_fun_splitting                     false
% 3.28/1.00  --sup_smt_interval                      50000
% 3.28/1.00  
% 3.28/1.00  ------ Superposition Simplification Setup
% 3.28/1.00  
% 3.28/1.00  --sup_indices_passive                   []
% 3.28/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_full_bw                           [BwDemod]
% 3.28/1.00  --sup_immed_triv                        [TrivRules]
% 3.28/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_immed_bw_main                     []
% 3.28/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.00  
% 3.28/1.00  ------ Combination Options
% 3.28/1.00  
% 3.28/1.00  --comb_res_mult                         3
% 3.28/1.00  --comb_sup_mult                         2
% 3.28/1.00  --comb_inst_mult                        10
% 3.28/1.00  
% 3.28/1.00  ------ Debug Options
% 3.28/1.00  
% 3.28/1.00  --dbg_backtrace                         false
% 3.28/1.00  --dbg_dump_prop_clauses                 false
% 3.28/1.00  --dbg_dump_prop_clauses_file            -
% 3.28/1.00  --dbg_out_stat                          false
% 3.28/1.00  ------ Parsing...
% 3.28/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.28/1.00  ------ Proving...
% 3.28/1.00  ------ Problem Properties 
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  clauses                                 14
% 3.28/1.00  conjectures                             3
% 3.28/1.00  EPR                                     4
% 3.28/1.00  Horn                                    11
% 3.28/1.00  unary                                   4
% 3.28/1.00  binary                                  9
% 3.28/1.00  lits                                    25
% 3.28/1.00  lits eq                                 4
% 3.28/1.00  fd_pure                                 0
% 3.28/1.00  fd_pseudo                               0
% 3.28/1.00  fd_cond                                 0
% 3.28/1.00  fd_pseudo_cond                          0
% 3.28/1.00  AC symbols                              0
% 3.28/1.00  
% 3.28/1.00  ------ Schedule dynamic 5 is on 
% 3.28/1.00  
% 3.28/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  ------ 
% 3.28/1.00  Current options:
% 3.28/1.00  ------ 
% 3.28/1.00  
% 3.28/1.00  ------ Input Options
% 3.28/1.00  
% 3.28/1.00  --out_options                           all
% 3.28/1.00  --tptp_safe_out                         true
% 3.28/1.00  --problem_path                          ""
% 3.28/1.00  --include_path                          ""
% 3.28/1.00  --clausifier                            res/vclausify_rel
% 3.28/1.00  --clausifier_options                    --mode clausify
% 3.28/1.00  --stdin                                 false
% 3.28/1.00  --stats_out                             all
% 3.28/1.00  
% 3.28/1.00  ------ General Options
% 3.28/1.00  
% 3.28/1.00  --fof                                   false
% 3.28/1.00  --time_out_real                         305.
% 3.28/1.00  --time_out_virtual                      -1.
% 3.28/1.00  --symbol_type_check                     false
% 3.28/1.00  --clausify_out                          false
% 3.28/1.00  --sig_cnt_out                           false
% 3.28/1.00  --trig_cnt_out                          false
% 3.28/1.00  --trig_cnt_out_tolerance                1.
% 3.28/1.00  --trig_cnt_out_sk_spl                   false
% 3.28/1.00  --abstr_cl_out                          false
% 3.28/1.00  
% 3.28/1.00  ------ Global Options
% 3.28/1.00  
% 3.28/1.00  --schedule                              default
% 3.28/1.00  --add_important_lit                     false
% 3.28/1.00  --prop_solver_per_cl                    1000
% 3.28/1.00  --min_unsat_core                        false
% 3.28/1.00  --soft_assumptions                      false
% 3.28/1.00  --soft_lemma_size                       3
% 3.28/1.00  --prop_impl_unit_size                   0
% 3.28/1.00  --prop_impl_unit                        []
% 3.28/1.00  --share_sel_clauses                     true
% 3.28/1.00  --reset_solvers                         false
% 3.28/1.00  --bc_imp_inh                            [conj_cone]
% 3.28/1.00  --conj_cone_tolerance                   3.
% 3.28/1.00  --extra_neg_conj                        none
% 3.28/1.00  --large_theory_mode                     true
% 3.28/1.00  --prolific_symb_bound                   200
% 3.28/1.00  --lt_threshold                          2000
% 3.28/1.00  --clause_weak_htbl                      true
% 3.28/1.00  --gc_record_bc_elim                     false
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing Options
% 3.28/1.00  
% 3.28/1.00  --preprocessing_flag                    true
% 3.28/1.00  --time_out_prep_mult                    0.1
% 3.28/1.00  --splitting_mode                        input
% 3.28/1.00  --splitting_grd                         true
% 3.28/1.00  --splitting_cvd                         false
% 3.28/1.00  --splitting_cvd_svl                     false
% 3.28/1.00  --splitting_nvd                         32
% 3.28/1.00  --sub_typing                            true
% 3.28/1.00  --prep_gs_sim                           true
% 3.28/1.00  --prep_unflatten                        true
% 3.28/1.00  --prep_res_sim                          true
% 3.28/1.00  --prep_upred                            true
% 3.28/1.00  --prep_sem_filter                       exhaustive
% 3.28/1.00  --prep_sem_filter_out                   false
% 3.28/1.00  --pred_elim                             true
% 3.28/1.00  --res_sim_input                         true
% 3.28/1.00  --eq_ax_congr_red                       true
% 3.28/1.00  --pure_diseq_elim                       true
% 3.28/1.00  --brand_transform                       false
% 3.28/1.00  --non_eq_to_eq                          false
% 3.28/1.00  --prep_def_merge                        true
% 3.28/1.00  --prep_def_merge_prop_impl              false
% 3.28/1.00  --prep_def_merge_mbd                    true
% 3.28/1.00  --prep_def_merge_tr_red                 false
% 3.28/1.00  --prep_def_merge_tr_cl                  false
% 3.28/1.00  --smt_preprocessing                     true
% 3.28/1.00  --smt_ac_axioms                         fast
% 3.28/1.00  --preprocessed_out                      false
% 3.28/1.00  --preprocessed_stats                    false
% 3.28/1.00  
% 3.28/1.00  ------ Abstraction refinement Options
% 3.28/1.00  
% 3.28/1.00  --abstr_ref                             []
% 3.28/1.00  --abstr_ref_prep                        false
% 3.28/1.00  --abstr_ref_until_sat                   false
% 3.28/1.00  --abstr_ref_sig_restrict                funpre
% 3.28/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.28/1.00  --abstr_ref_under                       []
% 3.28/1.00  
% 3.28/1.00  ------ SAT Options
% 3.28/1.00  
% 3.28/1.00  --sat_mode                              false
% 3.28/1.00  --sat_fm_restart_options                ""
% 3.28/1.00  --sat_gr_def                            false
% 3.28/1.00  --sat_epr_types                         true
% 3.28/1.00  --sat_non_cyclic_types                  false
% 3.28/1.00  --sat_finite_models                     false
% 3.28/1.00  --sat_fm_lemmas                         false
% 3.28/1.00  --sat_fm_prep                           false
% 3.28/1.00  --sat_fm_uc_incr                        true
% 3.28/1.00  --sat_out_model                         small
% 3.28/1.00  --sat_out_clauses                       false
% 3.28/1.00  
% 3.28/1.00  ------ QBF Options
% 3.28/1.00  
% 3.28/1.00  --qbf_mode                              false
% 3.28/1.00  --qbf_elim_univ                         false
% 3.28/1.00  --qbf_dom_inst                          none
% 3.28/1.00  --qbf_dom_pre_inst                      false
% 3.28/1.00  --qbf_sk_in                             false
% 3.28/1.00  --qbf_pred_elim                         true
% 3.28/1.00  --qbf_split                             512
% 3.28/1.00  
% 3.28/1.00  ------ BMC1 Options
% 3.28/1.00  
% 3.28/1.00  --bmc1_incremental                      false
% 3.28/1.00  --bmc1_axioms                           reachable_all
% 3.28/1.00  --bmc1_min_bound                        0
% 3.28/1.00  --bmc1_max_bound                        -1
% 3.28/1.00  --bmc1_max_bound_default                -1
% 3.28/1.00  --bmc1_symbol_reachability              true
% 3.28/1.00  --bmc1_property_lemmas                  false
% 3.28/1.00  --bmc1_k_induction                      false
% 3.28/1.00  --bmc1_non_equiv_states                 false
% 3.28/1.00  --bmc1_deadlock                         false
% 3.28/1.00  --bmc1_ucm                              false
% 3.28/1.00  --bmc1_add_unsat_core                   none
% 3.28/1.00  --bmc1_unsat_core_children              false
% 3.28/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.28/1.00  --bmc1_out_stat                         full
% 3.28/1.00  --bmc1_ground_init                      false
% 3.28/1.00  --bmc1_pre_inst_next_state              false
% 3.28/1.00  --bmc1_pre_inst_state                   false
% 3.28/1.00  --bmc1_pre_inst_reach_state             false
% 3.28/1.00  --bmc1_out_unsat_core                   false
% 3.28/1.00  --bmc1_aig_witness_out                  false
% 3.28/1.00  --bmc1_verbose                          false
% 3.28/1.00  --bmc1_dump_clauses_tptp                false
% 3.28/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.28/1.00  --bmc1_dump_file                        -
% 3.28/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.28/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.28/1.00  --bmc1_ucm_extend_mode                  1
% 3.28/1.00  --bmc1_ucm_init_mode                    2
% 3.28/1.00  --bmc1_ucm_cone_mode                    none
% 3.28/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.28/1.00  --bmc1_ucm_relax_model                  4
% 3.28/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.28/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.28/1.00  --bmc1_ucm_layered_model                none
% 3.28/1.00  --bmc1_ucm_max_lemma_size               10
% 3.28/1.00  
% 3.28/1.00  ------ AIG Options
% 3.28/1.00  
% 3.28/1.00  --aig_mode                              false
% 3.28/1.00  
% 3.28/1.00  ------ Instantiation Options
% 3.28/1.00  
% 3.28/1.00  --instantiation_flag                    true
% 3.28/1.00  --inst_sos_flag                         false
% 3.28/1.00  --inst_sos_phase                        true
% 3.28/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.28/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.28/1.00  --inst_lit_sel_side                     none
% 3.28/1.00  --inst_solver_per_active                1400
% 3.28/1.00  --inst_solver_calls_frac                1.
% 3.28/1.00  --inst_passive_queue_type               priority_queues
% 3.28/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.28/1.00  --inst_passive_queues_freq              [25;2]
% 3.28/1.00  --inst_dismatching                      true
% 3.28/1.00  --inst_eager_unprocessed_to_passive     true
% 3.28/1.00  --inst_prop_sim_given                   true
% 3.28/1.00  --inst_prop_sim_new                     false
% 3.28/1.00  --inst_subs_new                         false
% 3.28/1.00  --inst_eq_res_simp                      false
% 3.28/1.00  --inst_subs_given                       false
% 3.28/1.00  --inst_orphan_elimination               true
% 3.28/1.00  --inst_learning_loop_flag               true
% 3.28/1.00  --inst_learning_start                   3000
% 3.28/1.00  --inst_learning_factor                  2
% 3.28/1.00  --inst_start_prop_sim_after_learn       3
% 3.28/1.00  --inst_sel_renew                        solver
% 3.28/1.00  --inst_lit_activity_flag                true
% 3.28/1.00  --inst_restr_to_given                   false
% 3.28/1.00  --inst_activity_threshold               500
% 3.28/1.00  --inst_out_proof                        true
% 3.28/1.00  
% 3.28/1.00  ------ Resolution Options
% 3.28/1.00  
% 3.28/1.00  --resolution_flag                       false
% 3.28/1.00  --res_lit_sel                           adaptive
% 3.28/1.00  --res_lit_sel_side                      none
% 3.28/1.00  --res_ordering                          kbo
% 3.28/1.00  --res_to_prop_solver                    active
% 3.28/1.00  --res_prop_simpl_new                    false
% 3.28/1.00  --res_prop_simpl_given                  true
% 3.28/1.00  --res_passive_queue_type                priority_queues
% 3.28/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.28/1.00  --res_passive_queues_freq               [15;5]
% 3.28/1.00  --res_forward_subs                      full
% 3.28/1.00  --res_backward_subs                     full
% 3.28/1.00  --res_forward_subs_resolution           true
% 3.28/1.00  --res_backward_subs_resolution          true
% 3.28/1.00  --res_orphan_elimination                true
% 3.28/1.00  --res_time_limit                        2.
% 3.28/1.00  --res_out_proof                         true
% 3.28/1.00  
% 3.28/1.00  ------ Superposition Options
% 3.28/1.00  
% 3.28/1.00  --superposition_flag                    true
% 3.28/1.00  --sup_passive_queue_type                priority_queues
% 3.28/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.28/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.28/1.00  --demod_completeness_check              fast
% 3.28/1.00  --demod_use_ground                      true
% 3.28/1.00  --sup_to_prop_solver                    passive
% 3.28/1.00  --sup_prop_simpl_new                    true
% 3.28/1.00  --sup_prop_simpl_given                  true
% 3.28/1.00  --sup_fun_splitting                     false
% 3.28/1.00  --sup_smt_interval                      50000
% 3.28/1.00  
% 3.28/1.00  ------ Superposition Simplification Setup
% 3.28/1.00  
% 3.28/1.00  --sup_indices_passive                   []
% 3.28/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.28/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.28/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_full_bw                           [BwDemod]
% 3.28/1.00  --sup_immed_triv                        [TrivRules]
% 3.28/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.28/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_immed_bw_main                     []
% 3.28/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.28/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.28/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.28/1.00  
% 3.28/1.00  ------ Combination Options
% 3.28/1.00  
% 3.28/1.00  --comb_res_mult                         3
% 3.28/1.00  --comb_sup_mult                         2
% 3.28/1.00  --comb_inst_mult                        10
% 3.28/1.00  
% 3.28/1.00  ------ Debug Options
% 3.28/1.00  
% 3.28/1.00  --dbg_backtrace                         false
% 3.28/1.00  --dbg_dump_prop_clauses                 false
% 3.28/1.00  --dbg_dump_prop_clauses_file            -
% 3.28/1.00  --dbg_out_stat                          false
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  ------ Proving...
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  % SZS status Theorem for theBenchmark.p
% 3.28/1.00  
% 3.28/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.28/1.00  
% 3.28/1.00  fof(f7,axiom,(
% 3.28/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f21,plain,(
% 3.28/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 3.28/1.00    inference(ennf_transformation,[],[f7])).
% 3.28/1.00  
% 3.28/1.00  fof(f39,plain,(
% 3.28/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f21])).
% 3.28/1.00  
% 3.28/1.00  fof(f12,axiom,(
% 3.28/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f44,plain,(
% 3.28/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.28/1.00    inference(cnf_transformation,[],[f12])).
% 3.28/1.00  
% 3.28/1.00  fof(f9,axiom,(
% 3.28/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f41,plain,(
% 3.28/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f9])).
% 3.28/1.00  
% 3.28/1.00  fof(f10,axiom,(
% 3.28/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f42,plain,(
% 3.28/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f10])).
% 3.28/1.00  
% 3.28/1.00  fof(f49,plain,(
% 3.28/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.28/1.00    inference(definition_unfolding,[],[f41,f42])).
% 3.28/1.00  
% 3.28/1.00  fof(f50,plain,(
% 3.28/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.28/1.00    inference(definition_unfolding,[],[f44,f49])).
% 3.28/1.00  
% 3.28/1.00  fof(f52,plain,(
% 3.28/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 3.28/1.00    inference(definition_unfolding,[],[f39,f50])).
% 3.28/1.00  
% 3.28/1.00  fof(f2,axiom,(
% 3.28/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f25,plain,(
% 3.28/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.28/1.00    inference(nnf_transformation,[],[f2])).
% 3.28/1.00  
% 3.28/1.00  fof(f32,plain,(
% 3.28/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.28/1.00    inference(cnf_transformation,[],[f25])).
% 3.28/1.00  
% 3.28/1.00  fof(f3,axiom,(
% 3.28/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f16,plain,(
% 3.28/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.28/1.00    inference(ennf_transformation,[],[f3])).
% 3.28/1.00  
% 3.28/1.00  fof(f33,plain,(
% 3.28/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f16])).
% 3.28/1.00  
% 3.28/1.00  fof(f6,axiom,(
% 3.28/1.00    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f20,plain,(
% 3.28/1.00    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 3.28/1.00    inference(ennf_transformation,[],[f6])).
% 3.28/1.00  
% 3.28/1.00  fof(f38,plain,(
% 3.28/1.00    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f20])).
% 3.28/1.00  
% 3.28/1.00  fof(f5,axiom,(
% 3.28/1.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f18,plain,(
% 3.28/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.28/1.00    inference(ennf_transformation,[],[f5])).
% 3.28/1.00  
% 3.28/1.00  fof(f19,plain,(
% 3.28/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 3.28/1.00    inference(flattening,[],[f18])).
% 3.28/1.00  
% 3.28/1.00  fof(f37,plain,(
% 3.28/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f19])).
% 3.28/1.00  
% 3.28/1.00  fof(f13,conjecture,(
% 3.28/1.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f14,negated_conjecture,(
% 3.28/1.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.28/1.00    inference(negated_conjecture,[],[f13])).
% 3.28/1.00  
% 3.28/1.00  fof(f23,plain,(
% 3.28/1.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 3.28/1.00    inference(ennf_transformation,[],[f14])).
% 3.28/1.00  
% 3.28/1.00  fof(f24,plain,(
% 3.28/1.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 3.28/1.00    inference(flattening,[],[f23])).
% 3.28/1.00  
% 3.28/1.00  fof(f28,plain,(
% 3.28/1.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 3.28/1.00    introduced(choice_axiom,[])).
% 3.28/1.00  
% 3.28/1.00  fof(f29,plain,(
% 3.28/1.00    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 3.28/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f28])).
% 3.28/1.00  
% 3.28/1.00  fof(f45,plain,(
% 3.28/1.00    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 3.28/1.00    inference(cnf_transformation,[],[f29])).
% 3.28/1.00  
% 3.28/1.00  fof(f8,axiom,(
% 3.28/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f40,plain,(
% 3.28/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f8])).
% 3.28/1.00  
% 3.28/1.00  fof(f51,plain,(
% 3.28/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.28/1.00    inference(definition_unfolding,[],[f40,f49])).
% 3.28/1.00  
% 3.28/1.00  fof(f55,plain,(
% 3.28/1.00    r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4))),
% 3.28/1.00    inference(definition_unfolding,[],[f45,f51])).
% 3.28/1.00  
% 3.28/1.00  fof(f11,axiom,(
% 3.28/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f22,plain,(
% 3.28/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.28/1.00    inference(ennf_transformation,[],[f11])).
% 3.28/1.00  
% 3.28/1.00  fof(f43,plain,(
% 3.28/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f22])).
% 3.28/1.00  
% 3.28/1.00  fof(f53,plain,(
% 3.28/1.00    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.28/1.00    inference(definition_unfolding,[],[f43,f51])).
% 3.28/1.00  
% 3.28/1.00  fof(f31,plain,(
% 3.28/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f25])).
% 3.28/1.00  
% 3.28/1.00  fof(f4,axiom,(
% 3.28/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.28/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/1.00  
% 3.28/1.00  fof(f15,plain,(
% 3.28/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.28/1.00    inference(rectify,[],[f4])).
% 3.28/1.00  
% 3.28/1.00  fof(f17,plain,(
% 3.28/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.28/1.00    inference(ennf_transformation,[],[f15])).
% 3.28/1.00  
% 3.28/1.00  fof(f26,plain,(
% 3.28/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.28/1.00    introduced(choice_axiom,[])).
% 3.28/1.00  
% 3.28/1.00  fof(f27,plain,(
% 3.28/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.28/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).
% 3.28/1.00  
% 3.28/1.00  fof(f36,plain,(
% 3.28/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.28/1.00    inference(cnf_transformation,[],[f27])).
% 3.28/1.00  
% 3.28/1.00  fof(f48,plain,(
% 3.28/1.00    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 3.28/1.00    inference(cnf_transformation,[],[f29])).
% 3.28/1.00  
% 3.28/1.00  fof(f54,plain,(
% 3.28/1.00    ~r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2)),
% 3.28/1.00    inference(definition_unfolding,[],[f48,f50])).
% 3.28/1.00  
% 3.28/1.00  fof(f47,plain,(
% 3.28/1.00    r1_xboole_0(sK3,sK2)),
% 3.28/1.00    inference(cnf_transformation,[],[f29])).
% 3.28/1.00  
% 3.28/1.00  fof(f46,plain,(
% 3.28/1.00    r2_hidden(sK4,sK3)),
% 3.28/1.00    inference(cnf_transformation,[],[f29])).
% 3.28/1.00  
% 3.28/1.00  cnf(c_9,plain,
% 3.28/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.28/1.00      | k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
% 3.28/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1051,plain,
% 3.28/1.00      ( ~ r1_xboole_0(sK2,X0)
% 3.28/1.00      | k3_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_xboole_0(sK2,X1) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3087,plain,
% 3.28/1.00      ( ~ r1_xboole_0(sK2,X0)
% 3.28/1.00      | k3_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,sK3))) = k3_xboole_0(sK2,sK3) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_1051]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8755,plain,
% 3.28/1.00      ( ~ r1_xboole_0(sK2,sK1)
% 3.28/1.00      | k3_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) = k3_xboole_0(sK2,sK3) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_3087]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_325,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_765,plain,
% 3.28/1.00      ( k3_xboole_0(X0,X1) != X2
% 3.28/1.00      | k3_xboole_0(X0,X1) = k1_xboole_0
% 3.28/1.00      | k1_xboole_0 != X2 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_325]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1638,plain,
% 3.28/1.00      ( k3_xboole_0(X0,X1) != k3_xboole_0(sK2,sK3)
% 3.28/1.00      | k3_xboole_0(X0,X1) = k1_xboole_0
% 3.28/1.00      | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_765]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3086,plain,
% 3.28/1.00      ( k3_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,sK3))) != k3_xboole_0(sK2,sK3)
% 3.28/1.00      | k3_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,sK3))) = k1_xboole_0
% 3.28/1.00      | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_1638]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_5179,plain,
% 3.28/1.00      ( k3_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) != k3_xboole_0(sK2,sK3)
% 3.28/1.00      | k3_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) = k1_xboole_0
% 3.28/1.00      | k1_xboole_0 != k3_xboole_0(sK2,sK3) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_3086]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1,plain,
% 3.28/1.00      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.28/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1321,plain,
% 3.28/1.00      ( r1_xboole_0(sK2,X0) | k3_xboole_0(sK2,X0) != k1_xboole_0 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_2606,plain,
% 3.28/1.00      ( r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)))
% 3.28/1.00      | k3_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) != k1_xboole_0 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_1321]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_3,plain,
% 3.28/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.28/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_860,plain,
% 3.28/1.00      ( ~ r1_xboole_0(X0,sK2) | r1_xboole_0(sK2,X0) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1652,plain,
% 3.28/1.00      ( r1_xboole_0(sK2,sK1) | ~ r1_xboole_0(sK1,sK2) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_860]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_826,plain,
% 3.28/1.00      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_325]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_990,plain,
% 3.28/1.00      ( X0 != k1_xboole_0
% 3.28/1.00      | k1_xboole_0 = X0
% 3.28/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_826]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1507,plain,
% 3.28/1.00      ( k3_xboole_0(sK2,sK3) != k1_xboole_0
% 3.28/1.00      | k1_xboole_0 = k3_xboole_0(sK2,sK3)
% 3.28/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_990]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1053,plain,
% 3.28/1.00      ( r1_xboole_0(X0,sK2) | ~ r1_xboole_0(sK2,X0) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1310,plain,
% 3.28/1.00      ( r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2)
% 3.28/1.00      | ~ r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_1053]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_8,plain,
% 3.28/1.00      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 3.28/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_884,plain,
% 3.28/1.00      ( r1_xboole_0(X0,sK2) | ~ r1_xboole_0(k3_xboole_0(X0,sK2),sK2) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_1139,plain,
% 3.28/1.00      ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK2) | r1_xboole_0(sK1,sK2) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_884]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_324,plain,( X0 = X0 ),theory(equality) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_991,plain,
% 3.28/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_324]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_7,plain,
% 3.28/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 3.28/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_14,negated_conjecture,
% 3.28/1.00      ( r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.28/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_187,plain,
% 3.28/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.28/1.00      | r1_xboole_0(X2,X1)
% 3.28/1.00      | k2_enumset1(sK4,sK4,sK4,sK4) != X0
% 3.28/1.00      | k3_xboole_0(sK1,sK2) != X2 ),
% 3.28/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_188,plain,
% 3.28/1.00      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)
% 3.28/1.00      | r1_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 3.28/1.00      inference(unflattening,[status(thm)],[c_187]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_897,plain,
% 3.28/1.00      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2)
% 3.28/1.00      | r1_xboole_0(k3_xboole_0(sK1,sK2),sK2) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_188]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_10,plain,
% 3.28/1.00      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 3.28/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_787,plain,
% 3.28/1.00      ( r2_hidden(X0,sK2) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK2) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_789,plain,
% 3.28/1.00      ( r2_hidden(sK4,sK2)
% 3.28/1.00      | r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_2,plain,
% 3.28/1.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.28/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_771,plain,
% 3.28/1.00      ( ~ r1_xboole_0(sK2,sK3) | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_4,plain,
% 3.28/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.28/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_745,plain,
% 3.28/1.00      ( ~ r2_hidden(X0,sK2)
% 3.28/1.00      | ~ r2_hidden(X0,sK3)
% 3.28/1.00      | ~ r1_xboole_0(sK3,sK2) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_747,plain,
% 3.28/1.00      ( ~ r2_hidden(sK4,sK2)
% 3.28/1.00      | ~ r2_hidden(sK4,sK3)
% 3.28/1.00      | ~ r1_xboole_0(sK3,sK2) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_745]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_738,plain,
% 3.28/1.00      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 3.28/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_11,negated_conjecture,
% 3.28/1.00      ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2) ),
% 3.28/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_12,negated_conjecture,
% 3.28/1.00      ( r1_xboole_0(sK3,sK2) ),
% 3.28/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(c_13,negated_conjecture,
% 3.28/1.00      ( r2_hidden(sK4,sK3) ),
% 3.28/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.28/1.00  
% 3.28/1.00  cnf(contradiction,plain,
% 3.28/1.00      ( $false ),
% 3.28/1.00      inference(minisat,
% 3.28/1.00                [status(thm)],
% 3.28/1.00                [c_8755,c_5179,c_2606,c_1652,c_1507,c_1310,c_1139,c_991,
% 3.28/1.00                 c_897,c_789,c_771,c_747,c_738,c_11,c_12,c_13]) ).
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.28/1.00  
% 3.28/1.00  ------                               Statistics
% 3.28/1.00  
% 3.28/1.00  ------ General
% 3.28/1.00  
% 3.28/1.00  abstr_ref_over_cycles:                  0
% 3.28/1.00  abstr_ref_under_cycles:                 0
% 3.28/1.00  gc_basic_clause_elim:                   0
% 3.28/1.00  forced_gc_time:                         0
% 3.28/1.00  parsing_time:                           0.017
% 3.28/1.00  unif_index_cands_time:                  0.
% 3.28/1.00  unif_index_add_time:                    0.
% 3.28/1.00  orderings_time:                         0.
% 3.28/1.00  out_proof_time:                         0.007
% 3.28/1.00  total_time:                             0.338
% 3.28/1.00  num_of_symbols:                         43
% 3.28/1.00  num_of_terms:                           6404
% 3.28/1.00  
% 3.28/1.00  ------ Preprocessing
% 3.28/1.00  
% 3.28/1.00  num_of_splits:                          0
% 3.28/1.00  num_of_split_atoms:                     0
% 3.28/1.00  num_of_reused_defs:                     0
% 3.28/1.00  num_eq_ax_congr_red:                    6
% 3.28/1.00  num_of_sem_filtered_clauses:            1
% 3.28/1.00  num_of_subtypes:                        1
% 3.28/1.00  monotx_restored_types:                  0
% 3.28/1.00  sat_num_of_epr_types:                   0
% 3.28/1.00  sat_num_of_non_cyclic_types:            0
% 3.28/1.00  sat_guarded_non_collapsed_types:        0
% 3.28/1.00  num_pure_diseq_elim:                    0
% 3.28/1.00  simp_replaced_by:                       0
% 3.28/1.00  res_preprocessed:                       72
% 3.28/1.00  prep_upred:                             0
% 3.28/1.00  prep_unflattend:                        2
% 3.28/1.00  smt_new_axioms:                         0
% 3.28/1.00  pred_elim_cands:                        2
% 3.28/1.00  pred_elim:                              1
% 3.28/1.00  pred_elim_cl:                           1
% 3.28/1.00  pred_elim_cycles:                       3
% 3.28/1.00  merged_defs:                            8
% 3.28/1.00  merged_defs_ncl:                        0
% 3.28/1.00  bin_hyper_res:                          8
% 3.28/1.00  prep_cycles:                            4
% 3.28/1.00  pred_elim_time:                         0.
% 3.28/1.00  splitting_time:                         0.
% 3.28/1.00  sem_filter_time:                        0.
% 3.28/1.00  monotx_time:                            0.
% 3.28/1.00  subtype_inf_time:                       0.
% 3.28/1.00  
% 3.28/1.00  ------ Problem properties
% 3.28/1.00  
% 3.28/1.00  clauses:                                14
% 3.28/1.00  conjectures:                            3
% 3.28/1.00  epr:                                    4
% 3.28/1.00  horn:                                   11
% 3.28/1.00  ground:                                 3
% 3.28/1.00  unary:                                  4
% 3.28/1.00  binary:                                 9
% 3.28/1.00  lits:                                   25
% 3.28/1.00  lits_eq:                                4
% 3.28/1.00  fd_pure:                                0
% 3.28/1.00  fd_pseudo:                              0
% 3.28/1.00  fd_cond:                                0
% 3.28/1.00  fd_pseudo_cond:                         0
% 3.28/1.00  ac_symbols:                             0
% 3.28/1.00  
% 3.28/1.00  ------ Propositional Solver
% 3.28/1.00  
% 3.28/1.00  prop_solver_calls:                      33
% 3.28/1.00  prop_fast_solver_calls:                 540
% 3.28/1.00  smt_solver_calls:                       0
% 3.28/1.00  smt_fast_solver_calls:                  0
% 3.28/1.00  prop_num_of_clauses:                    3393
% 3.28/1.00  prop_preprocess_simplified:             5544
% 3.28/1.00  prop_fo_subsumed:                       2
% 3.28/1.00  prop_solver_time:                       0.
% 3.28/1.00  smt_solver_time:                        0.
% 3.28/1.00  smt_fast_solver_time:                   0.
% 3.28/1.00  prop_fast_solver_time:                  0.
% 3.28/1.00  prop_unsat_core_time:                   0.
% 3.28/1.00  
% 3.28/1.00  ------ QBF
% 3.28/1.00  
% 3.28/1.00  qbf_q_res:                              0
% 3.28/1.00  qbf_num_tautologies:                    0
% 3.28/1.00  qbf_prep_cycles:                        0
% 3.28/1.00  
% 3.28/1.00  ------ BMC1
% 3.28/1.00  
% 3.28/1.00  bmc1_current_bound:                     -1
% 3.28/1.00  bmc1_last_solved_bound:                 -1
% 3.28/1.00  bmc1_unsat_core_size:                   -1
% 3.28/1.00  bmc1_unsat_core_parents_size:           -1
% 3.28/1.00  bmc1_merge_next_fun:                    0
% 3.28/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.28/1.00  
% 3.28/1.00  ------ Instantiation
% 3.28/1.00  
% 3.28/1.00  inst_num_of_clauses:                    959
% 3.28/1.00  inst_num_in_passive:                    239
% 3.28/1.00  inst_num_in_active:                     496
% 3.28/1.00  inst_num_in_unprocessed:                223
% 3.28/1.00  inst_num_of_loops:                      669
% 3.28/1.00  inst_num_of_learning_restarts:          0
% 3.28/1.00  inst_num_moves_active_passive:          166
% 3.28/1.00  inst_lit_activity:                      0
% 3.28/1.00  inst_lit_activity_moves:                0
% 3.28/1.00  inst_num_tautologies:                   0
% 3.28/1.00  inst_num_prop_implied:                  0
% 3.28/1.00  inst_num_existing_simplified:           0
% 3.28/1.00  inst_num_eq_res_simplified:             0
% 3.28/1.00  inst_num_child_elim:                    0
% 3.28/1.00  inst_num_of_dismatching_blockings:      673
% 3.28/1.00  inst_num_of_non_proper_insts:           1401
% 3.28/1.00  inst_num_of_duplicates:                 0
% 3.28/1.00  inst_inst_num_from_inst_to_res:         0
% 3.28/1.00  inst_dismatching_checking_time:         0.
% 3.28/1.00  
% 3.28/1.00  ------ Resolution
% 3.28/1.00  
% 3.28/1.00  res_num_of_clauses:                     0
% 3.28/1.00  res_num_in_passive:                     0
% 3.28/1.00  res_num_in_active:                      0
% 3.28/1.00  res_num_of_loops:                       76
% 3.28/1.00  res_forward_subset_subsumed:            92
% 3.28/1.00  res_backward_subset_subsumed:           0
% 3.28/1.00  res_forward_subsumed:                   0
% 3.28/1.00  res_backward_subsumed:                  0
% 3.28/1.00  res_forward_subsumption_resolution:     0
% 3.28/1.00  res_backward_subsumption_resolution:    0
% 3.28/1.00  res_clause_to_clause_subsumption:       4257
% 3.28/1.00  res_orphan_elimination:                 0
% 3.28/1.00  res_tautology_del:                      134
% 3.28/1.00  res_num_eq_res_simplified:              0
% 3.28/1.00  res_num_sel_changes:                    0
% 3.28/1.00  res_moves_from_active_to_pass:          0
% 3.28/1.00  
% 3.28/1.00  ------ Superposition
% 3.28/1.00  
% 3.28/1.00  sup_time_total:                         0.
% 3.28/1.00  sup_time_generating:                    0.
% 3.28/1.00  sup_time_sim_full:                      0.
% 3.28/1.00  sup_time_sim_immed:                     0.
% 3.28/1.00  
% 3.28/1.00  sup_num_of_clauses:                     298
% 3.28/1.00  sup_num_in_active:                      126
% 3.28/1.00  sup_num_in_passive:                     172
% 3.28/1.00  sup_num_of_loops:                       132
% 3.28/1.00  sup_fw_superposition:                   314
% 3.28/1.00  sup_bw_superposition:                   165
% 3.28/1.00  sup_immediate_simplified:               13
% 3.28/1.00  sup_given_eliminated:                   0
% 3.28/1.00  comparisons_done:                       0
% 3.28/1.00  comparisons_avoided:                    0
% 3.28/1.00  
% 3.28/1.00  ------ Simplifications
% 3.28/1.00  
% 3.28/1.00  
% 3.28/1.00  sim_fw_subset_subsumed:                 12
% 3.28/1.00  sim_bw_subset_subsumed:                 1
% 3.28/1.00  sim_fw_subsumed:                        0
% 3.28/1.00  sim_bw_subsumed:                        0
% 3.28/1.00  sim_fw_subsumption_res:                 0
% 3.28/1.00  sim_bw_subsumption_res:                 0
% 3.28/1.00  sim_tautology_del:                      0
% 3.28/1.00  sim_eq_tautology_del:                   0
% 3.28/1.00  sim_eq_res_simp:                        0
% 3.28/1.00  sim_fw_demodulated:                     0
% 3.28/1.00  sim_bw_demodulated:                     6
% 3.28/1.00  sim_light_normalised:                   4
% 3.28/1.00  sim_joinable_taut:                      0
% 3.28/1.00  sim_joinable_simp:                      0
% 3.28/1.00  sim_ac_normalised:                      0
% 3.28/1.00  sim_smt_subsumption:                    0
% 3.28/1.00  
%------------------------------------------------------------------------------
