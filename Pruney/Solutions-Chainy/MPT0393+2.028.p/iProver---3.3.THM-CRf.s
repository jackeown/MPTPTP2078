%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:38 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 586 expanded)
%              Number of clauses        :   80 ( 137 expanded)
%              Number of leaves         :   19 ( 151 expanded)
%              Depth                    :   14
%              Number of atoms          :  356 (1185 expanded)
%              Number of equality atoms :  185 ( 693 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f43,f52,f52,f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f62,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f42,f52,f52,f52])).

fof(f61,plain,(
    ! [X1] : k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK2)) != sK2 ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    k1_setfam_1(k1_tarski(sK2)) != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f30])).

fof(f50,plain,(
    k1_setfam_1(k1_tarski(sK2)) != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != sK2 ),
    inference(definition_unfolding,[],[f50,f52])).

cnf(c_306,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_870,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),X2)
    | X2 != X1
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_12391,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),X0)
    | ~ r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))),X1)
    | X0 != X1
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_12395,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)
    | ~ r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))),sK2)
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_12391])).

cnf(c_8380,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK1(k2_enumset1(X3,X3,X3,X3),X2))
    | X2 != X0
    | sK1(k2_enumset1(X3,X3,X3,X3),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_8382,plain,
    ( r1_tarski(sK2,sK1(k2_enumset1(sK2,sK2,sK2,sK2),sK2))
    | ~ r1_tarski(sK2,sK2)
    | sK1(k2_enumset1(sK2,sK2,sK2,sK2),sK2) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_8380])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4955,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))),X1)
    | ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4957,plain,
    ( r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))),sK2)
    | ~ r1_tarski(sK2,sK2)
    | ~ r2_hidden(sK2,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) ),
    inference(instantiation,[status(thm)],[c_4955])).

cnf(c_304,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_756,plain,
    ( X0 != X1
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != X1
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_937,plain,
    ( X0 != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = X0
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_4925,plain,
    ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))))
    | k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_13,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK1(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_625,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_628,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_940,plain,
    ( X0 = X1
    | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_628])).

cnf(c_1224,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_940])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_632,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_631,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1045,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_632,c_631])).

cnf(c_8,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1465,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1045,c_8])).

cnf(c_1895,plain,
    ( sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1224,c_1465])).

cnf(c_624,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X2),X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_811,plain,
    ( r1_tarski(k1_setfam_1(X0),X1) = iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_624])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_633,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2225,plain,
    ( k1_setfam_1(X0) = X1
    | r1_tarski(X1,k1_setfam_1(X0)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_811,c_633])).

cnf(c_3338,plain,
    ( sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X1
    | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_2225])).

cnf(c_3344,plain,
    ( sK1(k2_enumset1(sK2,sK2,sK2,sK2),sK2) = sK2
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
    | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3338])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_634,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1467,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_628])).

cnf(c_1882,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_1467])).

cnf(c_2070,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | sK0(k2_enumset1(X0,X0,X0,X0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1882,c_940])).

cnf(c_3168,plain,
    ( sK0(k2_enumset1(X0,X0,X0,X0),k1_xboole_0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2070,c_1465])).

cnf(c_3175,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_1882])).

cnf(c_3184,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3175])).

cnf(c_309,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_1187,plain,
    ( X0 != k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_setfam_1(X0) = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_2845,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))) != k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1187])).

cnf(c_305,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1030,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_enumset1(X2,X2,X2,X2),k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X2,X2,X2,X2))),k2_enumset1(X2,X2,X2,X2))
    | X1 != k2_enumset1(X2,X2,X2,X2)
    | X0 != sK0(k2_enumset1(X2,X2,X2,X2),k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X2,X2,X2,X2))) ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_2804,plain,
    ( r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
    | X0 != sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_2806,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))) != k2_enumset1(sK2,sK2,sK2,sK2)
    | sK2 != sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_2804])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,sK1(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2777,plain,
    ( ~ r1_tarski(X0,sK1(k2_enumset1(X1,X1,X1,X1),X0))
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2783,plain,
    ( ~ r1_tarski(sK2,sK1(k2_enumset1(sK2,sK2,sK2,sK2),sK2))
    | r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2777])).

cnf(c_2775,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))),k2_enumset1(X1,X1,X1,X1))
    | X0 != sK0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))
    | k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_2779,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k1_xboole_0)
    | sK2 != sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
    | k1_xboole_0 != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2042,plain,
    ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0))
    | ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2044,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_2042])).

cnf(c_1470,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1467])).

cnf(c_1472,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_1469,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1029,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))
    | X1 = sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1036,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
    | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1024,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0))
    | ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1026,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_800,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)
    | ~ r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
    | sK2 = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_303,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_758,plain,
    ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_688,plain,
    ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != X0
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_757,plain,
    ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
    | sK2 != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_706,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))) = k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_697,plain,
    ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_699,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_43,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_35,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_34,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_15,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12395,c_8382,c_4957,c_4925,c_3344,c_3184,c_2845,c_2806,c_2783,c_2779,c_2044,c_1472,c_1469,c_1036,c_1026,c_800,c_758,c_757,c_706,c_699,c_43,c_35,c_34,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.56/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/0.99  
% 3.56/0.99  ------  iProver source info
% 3.56/0.99  
% 3.56/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.56/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/0.99  git: non_committed_changes: false
% 3.56/0.99  git: last_make_outside_of_git: false
% 3.56/0.99  
% 3.56/0.99  ------ 
% 3.56/0.99  ------ Parsing...
% 3.56/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/0.99  ------ Proving...
% 3.56/0.99  ------ Problem Properties 
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  clauses                                 15
% 3.56/0.99  conjectures                             1
% 3.56/0.99  EPR                                     2
% 3.56/0.99  Horn                                    10
% 3.56/0.99  unary                                   4
% 3.56/0.99  binary                                  4
% 3.56/0.99  lits                                    33
% 3.56/0.99  lits eq                                 12
% 3.56/0.99  fd_pure                                 0
% 3.56/0.99  fd_pseudo                               0
% 3.56/0.99  fd_cond                                 2
% 3.56/0.99  fd_pseudo_cond                          5
% 3.56/0.99  AC symbols                              0
% 3.56/0.99  
% 3.56/0.99  ------ Input Options Time Limit: Unbounded
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ 
% 3.56/0.99  Current options:
% 3.56/0.99  ------ 
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ Proving...
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  % SZS status Theorem for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  fof(f10,axiom,(
% 3.56/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f16,plain,(
% 3.56/0.99    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 3.56/0.99    inference(ennf_transformation,[],[f10])).
% 3.56/0.99  
% 3.56/0.99  fof(f17,plain,(
% 3.56/0.99    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 3.56/0.99    inference(flattening,[],[f16])).
% 3.56/0.99  
% 3.56/0.99  fof(f49,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f17])).
% 3.56/0.99  
% 3.56/0.99  fof(f9,axiom,(
% 3.56/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f14,plain,(
% 3.56/0.99    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.56/0.99    inference(ennf_transformation,[],[f9])).
% 3.56/0.99  
% 3.56/0.99  fof(f15,plain,(
% 3.56/0.99    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.56/0.99    inference(flattening,[],[f14])).
% 3.56/0.99  
% 3.56/0.99  fof(f28,plain,(
% 3.56/0.99    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 3.56/0.99    introduced(choice_axiom,[])).
% 3.56/0.99  
% 3.56/0.99  fof(f29,plain,(
% 3.56/0.99    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 3.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f28])).
% 3.56/0.99  
% 3.56/0.99  fof(f47,plain,(
% 3.56/0.99    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK1(X0,X1),X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f29])).
% 3.56/0.99  
% 3.56/0.99  fof(f7,axiom,(
% 3.56/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f25,plain,(
% 3.56/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.56/0.99    inference(nnf_transformation,[],[f7])).
% 3.56/0.99  
% 3.56/0.99  fof(f43,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.56/0.99    inference(cnf_transformation,[],[f25])).
% 3.56/0.99  
% 3.56/0.99  fof(f4,axiom,(
% 3.56/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f39,plain,(
% 3.56/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f4])).
% 3.56/0.99  
% 3.56/0.99  fof(f5,axiom,(
% 3.56/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f40,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f5])).
% 3.56/0.99  
% 3.56/0.99  fof(f6,axiom,(
% 3.56/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f41,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f6])).
% 3.56/0.99  
% 3.56/0.99  fof(f51,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f40,f41])).
% 3.56/0.99  
% 3.56/0.99  fof(f52,plain,(
% 3.56/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f39,f51])).
% 3.56/0.99  
% 3.56/0.99  fof(f53,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0) | X0 = X1) )),
% 3.56/0.99    inference(definition_unfolding,[],[f43,f52,f52,f52])).
% 3.56/0.99  
% 3.56/0.99  fof(f8,axiom,(
% 3.56/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f26,plain,(
% 3.56/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.56/0.99    inference(nnf_transformation,[],[f8])).
% 3.56/0.99  
% 3.56/0.99  fof(f27,plain,(
% 3.56/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.56/0.99    inference(flattening,[],[f26])).
% 3.56/0.99  
% 3.56/0.99  fof(f45,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f27])).
% 3.56/0.99  
% 3.56/0.99  fof(f56,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 3.56/0.99    inference(definition_unfolding,[],[f45,f52])).
% 3.56/0.99  
% 3.56/0.99  fof(f62,plain,(
% 3.56/0.99    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 3.56/0.99    inference(equality_resolution,[],[f56])).
% 3.56/0.99  
% 3.56/0.99  fof(f2,axiom,(
% 3.56/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f22,plain,(
% 3.56/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/0.99    inference(nnf_transformation,[],[f2])).
% 3.56/0.99  
% 3.56/0.99  fof(f23,plain,(
% 3.56/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/0.99    inference(flattening,[],[f22])).
% 3.56/0.99  
% 3.56/0.99  fof(f34,plain,(
% 3.56/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.56/0.99    inference(cnf_transformation,[],[f23])).
% 3.56/0.99  
% 3.56/0.99  fof(f60,plain,(
% 3.56/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.56/0.99    inference(equality_resolution,[],[f34])).
% 3.56/0.99  
% 3.56/0.99  fof(f3,axiom,(
% 3.56/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f24,plain,(
% 3.56/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.56/0.99    inference(nnf_transformation,[],[f3])).
% 3.56/0.99  
% 3.56/0.99  fof(f38,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f24])).
% 3.56/0.99  
% 3.56/0.99  fof(f42,plain,(
% 3.56/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f25])).
% 3.56/0.99  
% 3.56/0.99  fof(f54,plain,(
% 3.56/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f42,f52,f52,f52])).
% 3.56/0.99  
% 3.56/0.99  fof(f61,plain,(
% 3.56/0.99    ( ! [X1] : (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1)) )),
% 3.56/0.99    inference(equality_resolution,[],[f54])).
% 3.56/0.99  
% 3.56/0.99  fof(f36,plain,(
% 3.56/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f23])).
% 3.56/0.99  
% 3.56/0.99  fof(f1,axiom,(
% 3.56/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f13,plain,(
% 3.56/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.56/0.99    inference(ennf_transformation,[],[f1])).
% 3.56/0.99  
% 3.56/0.99  fof(f19,plain,(
% 3.56/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.56/0.99    inference(nnf_transformation,[],[f13])).
% 3.56/0.99  
% 3.56/0.99  fof(f20,plain,(
% 3.56/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.56/0.99    introduced(choice_axiom,[])).
% 3.56/0.99  
% 3.56/0.99  fof(f21,plain,(
% 3.56/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.56/0.99  
% 3.56/0.99  fof(f32,plain,(
% 3.56/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f21])).
% 3.56/0.99  
% 3.56/0.99  fof(f48,plain,(
% 3.56/0.99    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK1(X0,X1))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f29])).
% 3.56/0.99  
% 3.56/0.99  fof(f44,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f27])).
% 3.56/0.99  
% 3.56/0.99  fof(f57,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 3.56/0.99    inference(definition_unfolding,[],[f44,f52])).
% 3.56/0.99  
% 3.56/0.99  fof(f46,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f27])).
% 3.56/0.99  
% 3.56/0.99  fof(f55,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f46,f52])).
% 3.56/0.99  
% 3.56/0.99  fof(f33,plain,(
% 3.56/0.99    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f21])).
% 3.56/0.99  
% 3.56/0.99  fof(f11,conjecture,(
% 3.56/0.99    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f12,negated_conjecture,(
% 3.56/0.99    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.56/0.99    inference(negated_conjecture,[],[f11])).
% 3.56/0.99  
% 3.56/0.99  fof(f18,plain,(
% 3.56/0.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 3.56/0.99    inference(ennf_transformation,[],[f12])).
% 3.56/0.99  
% 3.56/0.99  fof(f30,plain,(
% 3.56/0.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK2)) != sK2),
% 3.56/0.99    introduced(choice_axiom,[])).
% 3.56/0.99  
% 3.56/0.99  fof(f31,plain,(
% 3.56/0.99    k1_setfam_1(k1_tarski(sK2)) != sK2),
% 3.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f30])).
% 3.56/0.99  
% 3.56/0.99  fof(f50,plain,(
% 3.56/0.99    k1_setfam_1(k1_tarski(sK2)) != sK2),
% 3.56/0.99    inference(cnf_transformation,[],[f31])).
% 3.56/0.99  
% 3.56/0.99  fof(f58,plain,(
% 3.56/0.99    k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != sK2),
% 3.56/0.99    inference(definition_unfolding,[],[f50,f52])).
% 3.56/0.99  
% 3.56/0.99  cnf(c_306,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.56/0.99      theory(equality) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_870,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1)
% 3.56/0.99      | r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),X2)
% 3.56/0.99      | X2 != X1
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != X0 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_306]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_12391,plain,
% 3.56/0.99      ( r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),X0)
% 3.56/0.99      | ~ r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))),X1)
% 3.56/0.99      | X0 != X1
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_870]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_12395,plain,
% 3.56/0.99      ( r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)
% 3.56/0.99      | ~ r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))),sK2)
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))))
% 3.56/0.99      | sK2 != sK2 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_12391]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_8380,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1)
% 3.56/0.99      | r1_tarski(X2,sK1(k2_enumset1(X3,X3,X3,X3),X2))
% 3.56/0.99      | X2 != X0
% 3.56/0.99      | sK1(k2_enumset1(X3,X3,X3,X3),X2) != X1 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_306]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_8382,plain,
% 3.56/0.99      ( r1_tarski(sK2,sK1(k2_enumset1(sK2,sK2,sK2,sK2),sK2))
% 3.56/0.99      | ~ r1_tarski(sK2,sK2)
% 3.56/0.99      | sK1(k2_enumset1(sK2,sK2,sK2,sK2),sK2) != sK2
% 3.56/0.99      | sK2 != sK2 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_8380]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_14,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1)
% 3.56/0.99      | r1_tarski(k1_setfam_1(X2),X1)
% 3.56/0.99      | ~ r2_hidden(X0,X2) ),
% 3.56/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4955,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1)
% 3.56/0.99      | r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))),X1)
% 3.56/0.99      | ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4957,plain,
% 3.56/0.99      ( r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))),sK2)
% 3.56/0.99      | ~ r1_tarski(sK2,sK2)
% 3.56/0.99      | ~ r2_hidden(sK2,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_4955]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_304,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_756,plain,
% 3.56/0.99      ( X0 != X1
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != X1
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = X0 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_304]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_937,plain,
% 3.56/0.99      ( X0 != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = X0
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_756]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4925,plain,
% 3.56/0.99      ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))))
% 3.56/0.99      | k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_937]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_13,plain,
% 3.56/0.99      ( r1_tarski(X0,k1_setfam_1(X1))
% 3.56/0.99      | r2_hidden(sK1(X1,X0),X1)
% 3.56/0.99      | k1_xboole_0 = X1 ),
% 3.56/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_625,plain,
% 3.56/0.99      ( k1_xboole_0 = X0
% 3.56/0.99      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
% 3.56/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_7,plain,
% 3.56/0.99      ( X0 = X1
% 3.56/0.99      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
% 3.56/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_10,plain,
% 3.56/0.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 3.56/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_628,plain,
% 3.56/0.99      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_940,plain,
% 3.56/0.99      ( X0 = X1 | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_7,c_628]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1224,plain,
% 3.56/0.99      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.56/0.99      | sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0
% 3.56/0.99      | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_625,c_940]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4,plain,
% 3.56/0.99      ( r1_tarski(X0,X0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_632,plain,
% 3.56/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_631,plain,
% 3.56/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.56/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1045,plain,
% 3.56/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_632,c_631]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_8,plain,
% 3.56/0.99      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1465,plain,
% 3.56/0.99      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1045,c_8]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1895,plain,
% 3.56/0.99      ( sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0
% 3.56/0.99      | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 3.56/0.99      inference(global_propositional_subsumption,
% 3.56/0.99                [status(thm)],
% 3.56/0.99                [c_1224,c_1465]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_624,plain,
% 3.56/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.56/0.99      | r1_tarski(k1_setfam_1(X2),X1) = iProver_top
% 3.56/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_811,plain,
% 3.56/0.99      ( r1_tarski(k1_setfam_1(X0),X1) = iProver_top
% 3.56/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_632,c_624]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.56/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_633,plain,
% 3.56/0.99      ( X0 = X1
% 3.56/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.56/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2225,plain,
% 3.56/0.99      ( k1_setfam_1(X0) = X1
% 3.56/0.99      | r1_tarski(X1,k1_setfam_1(X0)) != iProver_top
% 3.56/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_811,c_633]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3338,plain,
% 3.56/0.99      ( sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0
% 3.56/0.99      | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X1
% 3.56/0.99      | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1895,c_2225]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3344,plain,
% 3.56/0.99      ( sK1(k2_enumset1(sK2,sK2,sK2,sK2),sK2) = sK2
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
% 3.56/0.99      | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_3338]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1,plain,
% 3.56/0.99      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_634,plain,
% 3.56/0.99      ( X0 = X1
% 3.56/0.99      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.56/0.99      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1467,plain,
% 3.56/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1045,c_628]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1882,plain,
% 3.56/0.99      ( k1_xboole_0 = X0
% 3.56/0.99      | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_634,c_1467]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2070,plain,
% 3.56/0.99      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.56/0.99      | sK0(k2_enumset1(X0,X0,X0,X0),k1_xboole_0) = X0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1882,c_940]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3168,plain,
% 3.56/0.99      ( sK0(k2_enumset1(X0,X0,X0,X0),k1_xboole_0) = X0 ),
% 3.56/0.99      inference(global_propositional_subsumption,
% 3.56/0.99                [status(thm)],
% 3.56/0.99                [c_2070,c_1465]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3175,plain,
% 3.56/0.99      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.56/0.99      | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_3168,c_1882]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3184,plain,
% 3.56/0.99      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 3.56/0.99      | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_3175]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_309,plain,
% 3.56/0.99      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 3.56/0.99      theory(equality) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1187,plain,
% 3.56/0.99      ( X0 != k2_enumset1(sK2,sK2,sK2,sK2)
% 3.56/0.99      | k1_setfam_1(X0) = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_309]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2845,plain,
% 3.56/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))) != k2_enumset1(sK2,sK2,sK2,sK2)
% 3.56/0.99      | k1_setfam_1(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))))) = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_1187]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_305,plain,
% 3.56/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.56/0.99      theory(equality) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1030,plain,
% 3.56/0.99      ( r2_hidden(X0,X1)
% 3.56/0.99      | ~ r2_hidden(sK0(k2_enumset1(X2,X2,X2,X2),k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X2,X2,X2,X2))),k2_enumset1(X2,X2,X2,X2))
% 3.56/0.99      | X1 != k2_enumset1(X2,X2,X2,X2)
% 3.56/0.99      | X0 != sK0(k2_enumset1(X2,X2,X2,X2),k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X2,X2,X2,X2))) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_305]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2804,plain,
% 3.56/0.99      ( r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))))
% 3.56/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | X0 != sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
% 3.56/0.99      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))) != k2_enumset1(sK2,sK2,sK2,sK2) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2806,plain,
% 3.56/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | r2_hidden(sK2,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))))
% 3.56/0.99      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))) != k2_enumset1(sK2,sK2,sK2,sK2)
% 3.56/0.99      | sK2 != sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_2804]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_12,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,sK1(X1,X0))
% 3.56/0.99      | r1_tarski(X0,k1_setfam_1(X1))
% 3.56/0.99      | k1_xboole_0 = X1 ),
% 3.56/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2777,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,sK1(k2_enumset1(X1,X1,X1,X1),X0))
% 3.56/0.99      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 3.56/0.99      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2783,plain,
% 3.56/0.99      ( ~ r1_tarski(sK2,sK1(k2_enumset1(sK2,sK2,sK2,sK2),sK2))
% 3.56/0.99      | r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
% 3.56/0.99      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_2777]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2775,plain,
% 3.56/0.99      ( r2_hidden(X0,k1_xboole_0)
% 3.56/0.99      | ~ r2_hidden(sK0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))),k2_enumset1(X1,X1,X1,X1))
% 3.56/0.99      | X0 != sK0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))
% 3.56/0.99      | k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2779,plain,
% 3.56/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | r2_hidden(sK2,k1_xboole_0)
% 3.56/0.99      | sK2 != sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
% 3.56/0.99      | k1_xboole_0 != k2_enumset1(sK2,sK2,sK2,sK2) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_2775]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_11,plain,
% 3.56/0.99      ( r2_hidden(X0,X1)
% 3.56/0.99      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
% 3.56/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2042,plain,
% 3.56/0.99      ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0))
% 3.56/0.99      | ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2044,plain,
% 3.56/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_2042]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1470,plain,
% 3.56/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.56/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1467]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1472,plain,
% 3.56/0.99      ( ~ r2_hidden(sK2,k1_xboole_0) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_1470]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1469,plain,
% 3.56/0.99      ( k2_enumset1(sK2,sK2,sK2,sK2) != k1_xboole_0 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_1465]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_9,plain,
% 3.56/0.99      ( ~ r2_hidden(X0,X1)
% 3.56/0.99      | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
% 3.56/0.99      | X2 = X0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1029,plain,
% 3.56/0.99      ( ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0))
% 3.56/0.99      | r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))
% 3.56/0.99      | X1 = sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1036,plain,
% 3.56/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
% 3.56/0.99      | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_1029]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_0,plain,
% 3.56/0.99      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.56/0.99      | ~ r2_hidden(sK0(X0,X1),X0)
% 3.56/0.99      | X1 = X0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1024,plain,
% 3.56/0.99      ( ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0))
% 3.56/0.99      | ~ r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))
% 3.56/0.99      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X0,X0,X0,X0) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1026,plain,
% 3.56/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
% 3.56/0.99      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_1024]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_800,plain,
% 3.56/0.99      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)
% 3.56/0.99      | ~ r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
% 3.56/0.99      | sK2 = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_303,plain,( X0 = X0 ),theory(equality) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_758,plain,
% 3.56/0.99      ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_303]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_688,plain,
% 3.56/0.99      ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != X0
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
% 3.56/0.99      | sK2 != X0 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_304]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_757,plain,
% 3.56/0.99      ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
% 3.56/0.99      | sK2 != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_688]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_706,plain,
% 3.56/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))) = k2_enumset1(sK2,sK2,sK2,sK2)
% 3.56/0.99      | k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_697,plain,
% 3.56/0.99      ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k2_enumset1(X0,X0,X0,X0))
% 3.56/0.99      | r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))
% 3.56/0.99      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X0,X0,X0,X0) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_699,plain,
% 3.56/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.56/0.99      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
% 3.56/0.99      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_697]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_43,plain,
% 3.56/0.99      ( r1_tarski(sK2,sK2) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_35,plain,
% 3.56/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK2,sK2,sK2,sK2)
% 3.56/0.99      | sK2 = sK2 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_34,plain,
% 3.56/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_enumset1(sK2,sK2,sK2,sK2) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_15,negated_conjecture,
% 3.56/0.99      ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) != sK2 ),
% 3.56/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(contradiction,plain,
% 3.56/0.99      ( $false ),
% 3.56/0.99      inference(minisat,
% 3.56/0.99                [status(thm)],
% 3.56/0.99                [c_12395,c_8382,c_4957,c_4925,c_3344,c_3184,c_2845,
% 3.56/0.99                 c_2806,c_2783,c_2779,c_2044,c_1472,c_1469,c_1036,c_1026,
% 3.56/0.99                 c_800,c_758,c_757,c_706,c_699,c_43,c_35,c_34,c_15]) ).
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  ------                               Statistics
% 3.56/0.99  
% 3.56/0.99  ------ Selected
% 3.56/0.99  
% 3.56/0.99  total_time:                             0.451
% 3.56/0.99  
%------------------------------------------------------------------------------
