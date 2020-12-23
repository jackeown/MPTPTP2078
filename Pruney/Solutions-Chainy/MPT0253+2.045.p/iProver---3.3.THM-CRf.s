%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:45 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   60 (  91 expanded)
%              Number of clauses        :   26 (  29 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  126 ( 191 expanded)
%              Number of equality atoms :   70 ( 107 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f21,f24,f24,f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f24,f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).

fof(f34,plain,(
    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != sK1 ),
    inference(definition_unfolding,[],[f34,f24,f36])).

fof(f33,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2456,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_119,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1532,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_120,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_712,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) != X1
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != X1
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_1531,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))))
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_1533,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))))
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_304,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != X0
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_660,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))))
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = sK1
    | sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_661,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))))
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = sK1
    | sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_330,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_390,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_466,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) != sK1
    | sK1 = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_467,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) != sK1
    | sK1 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_344,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),sK1)
    | k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_351,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) = sK1 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_336,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ r2_hidden(sK2,sK1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_321,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK0,sK1)
    | r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_7,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2456,c_1532,c_1533,c_661,c_467,c_351,c_336,c_321,c_7,c_8,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.48/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.05  
% 3.48/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/1.05  
% 3.48/1.05  ------  iProver source info
% 3.48/1.05  
% 3.48/1.05  git: date: 2020-06-30 10:37:57 +0100
% 3.48/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/1.05  git: non_committed_changes: false
% 3.48/1.05  git: last_make_outside_of_git: false
% 3.48/1.05  
% 3.48/1.05  ------ 
% 3.48/1.05  
% 3.48/1.05  ------ Input Options
% 3.48/1.05  
% 3.48/1.05  --out_options                           all
% 3.48/1.05  --tptp_safe_out                         true
% 3.48/1.05  --problem_path                          ""
% 3.48/1.05  --include_path                          ""
% 3.48/1.05  --clausifier                            res/vclausify_rel
% 3.48/1.05  --clausifier_options                    --mode clausify
% 3.48/1.05  --stdin                                 false
% 3.48/1.05  --stats_out                             all
% 3.48/1.05  
% 3.48/1.05  ------ General Options
% 3.48/1.05  
% 3.48/1.05  --fof                                   false
% 3.48/1.05  --time_out_real                         305.
% 3.48/1.05  --time_out_virtual                      -1.
% 3.48/1.05  --symbol_type_check                     false
% 3.48/1.05  --clausify_out                          false
% 3.48/1.05  --sig_cnt_out                           false
% 3.48/1.05  --trig_cnt_out                          false
% 3.48/1.05  --trig_cnt_out_tolerance                1.
% 3.48/1.05  --trig_cnt_out_sk_spl                   false
% 3.48/1.05  --abstr_cl_out                          false
% 3.48/1.05  
% 3.48/1.05  ------ Global Options
% 3.48/1.05  
% 3.48/1.05  --schedule                              default
% 3.48/1.05  --add_important_lit                     false
% 3.48/1.05  --prop_solver_per_cl                    1000
% 3.48/1.05  --min_unsat_core                        false
% 3.48/1.05  --soft_assumptions                      false
% 3.48/1.05  --soft_lemma_size                       3
% 3.48/1.05  --prop_impl_unit_size                   0
% 3.48/1.05  --prop_impl_unit                        []
% 3.48/1.05  --share_sel_clauses                     true
% 3.48/1.05  --reset_solvers                         false
% 3.48/1.05  --bc_imp_inh                            [conj_cone]
% 3.48/1.05  --conj_cone_tolerance                   3.
% 3.48/1.05  --extra_neg_conj                        none
% 3.48/1.05  --large_theory_mode                     true
% 3.48/1.05  --prolific_symb_bound                   200
% 3.48/1.05  --lt_threshold                          2000
% 3.48/1.05  --clause_weak_htbl                      true
% 3.48/1.05  --gc_record_bc_elim                     false
% 3.48/1.05  
% 3.48/1.05  ------ Preprocessing Options
% 3.48/1.05  
% 3.48/1.05  --preprocessing_flag                    true
% 3.48/1.05  --time_out_prep_mult                    0.1
% 3.48/1.05  --splitting_mode                        input
% 3.48/1.05  --splitting_grd                         true
% 3.48/1.05  --splitting_cvd                         false
% 3.48/1.05  --splitting_cvd_svl                     false
% 3.48/1.05  --splitting_nvd                         32
% 3.48/1.05  --sub_typing                            true
% 3.48/1.05  --prep_gs_sim                           true
% 3.48/1.05  --prep_unflatten                        true
% 3.48/1.05  --prep_res_sim                          true
% 3.48/1.05  --prep_upred                            true
% 3.48/1.05  --prep_sem_filter                       exhaustive
% 3.48/1.05  --prep_sem_filter_out                   false
% 3.48/1.05  --pred_elim                             true
% 3.48/1.05  --res_sim_input                         true
% 3.48/1.05  --eq_ax_congr_red                       true
% 3.48/1.05  --pure_diseq_elim                       true
% 3.48/1.05  --brand_transform                       false
% 3.48/1.05  --non_eq_to_eq                          false
% 3.48/1.05  --prep_def_merge                        true
% 3.48/1.05  --prep_def_merge_prop_impl              false
% 3.48/1.05  --prep_def_merge_mbd                    true
% 3.48/1.05  --prep_def_merge_tr_red                 false
% 3.48/1.05  --prep_def_merge_tr_cl                  false
% 3.48/1.05  --smt_preprocessing                     true
% 3.48/1.05  --smt_ac_axioms                         fast
% 3.48/1.05  --preprocessed_out                      false
% 3.48/1.05  --preprocessed_stats                    false
% 3.48/1.05  
% 3.48/1.05  ------ Abstraction refinement Options
% 3.48/1.05  
% 3.48/1.05  --abstr_ref                             []
% 3.48/1.05  --abstr_ref_prep                        false
% 3.48/1.05  --abstr_ref_until_sat                   false
% 3.48/1.05  --abstr_ref_sig_restrict                funpre
% 3.48/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/1.05  --abstr_ref_under                       []
% 3.48/1.05  
% 3.48/1.05  ------ SAT Options
% 3.48/1.05  
% 3.48/1.05  --sat_mode                              false
% 3.48/1.05  --sat_fm_restart_options                ""
% 3.48/1.05  --sat_gr_def                            false
% 3.48/1.05  --sat_epr_types                         true
% 3.48/1.05  --sat_non_cyclic_types                  false
% 3.48/1.05  --sat_finite_models                     false
% 3.48/1.05  --sat_fm_lemmas                         false
% 3.48/1.05  --sat_fm_prep                           false
% 3.48/1.05  --sat_fm_uc_incr                        true
% 3.48/1.05  --sat_out_model                         small
% 3.48/1.05  --sat_out_clauses                       false
% 3.48/1.05  
% 3.48/1.05  ------ QBF Options
% 3.48/1.05  
% 3.48/1.05  --qbf_mode                              false
% 3.48/1.05  --qbf_elim_univ                         false
% 3.48/1.05  --qbf_dom_inst                          none
% 3.48/1.05  --qbf_dom_pre_inst                      false
% 3.48/1.05  --qbf_sk_in                             false
% 3.48/1.05  --qbf_pred_elim                         true
% 3.48/1.05  --qbf_split                             512
% 3.48/1.05  
% 3.48/1.05  ------ BMC1 Options
% 3.48/1.05  
% 3.48/1.05  --bmc1_incremental                      false
% 3.48/1.05  --bmc1_axioms                           reachable_all
% 3.48/1.05  --bmc1_min_bound                        0
% 3.48/1.05  --bmc1_max_bound                        -1
% 3.48/1.05  --bmc1_max_bound_default                -1
% 3.48/1.05  --bmc1_symbol_reachability              true
% 3.48/1.05  --bmc1_property_lemmas                  false
% 3.48/1.05  --bmc1_k_induction                      false
% 3.48/1.05  --bmc1_non_equiv_states                 false
% 3.48/1.05  --bmc1_deadlock                         false
% 3.48/1.05  --bmc1_ucm                              false
% 3.48/1.05  --bmc1_add_unsat_core                   none
% 3.48/1.05  --bmc1_unsat_core_children              false
% 3.48/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/1.05  --bmc1_out_stat                         full
% 3.48/1.05  --bmc1_ground_init                      false
% 3.48/1.05  --bmc1_pre_inst_next_state              false
% 3.48/1.05  --bmc1_pre_inst_state                   false
% 3.48/1.05  --bmc1_pre_inst_reach_state             false
% 3.48/1.05  --bmc1_out_unsat_core                   false
% 3.48/1.05  --bmc1_aig_witness_out                  false
% 3.48/1.05  --bmc1_verbose                          false
% 3.48/1.05  --bmc1_dump_clauses_tptp                false
% 3.48/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.48/1.05  --bmc1_dump_file                        -
% 3.48/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.48/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.48/1.05  --bmc1_ucm_extend_mode                  1
% 3.48/1.05  --bmc1_ucm_init_mode                    2
% 3.48/1.05  --bmc1_ucm_cone_mode                    none
% 3.48/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.48/1.05  --bmc1_ucm_relax_model                  4
% 3.48/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.48/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/1.05  --bmc1_ucm_layered_model                none
% 3.48/1.05  --bmc1_ucm_max_lemma_size               10
% 3.48/1.05  
% 3.48/1.05  ------ AIG Options
% 3.48/1.05  
% 3.48/1.05  --aig_mode                              false
% 3.48/1.05  
% 3.48/1.05  ------ Instantiation Options
% 3.48/1.05  
% 3.48/1.05  --instantiation_flag                    true
% 3.48/1.05  --inst_sos_flag                         false
% 3.48/1.05  --inst_sos_phase                        true
% 3.48/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/1.05  --inst_lit_sel_side                     num_symb
% 3.48/1.05  --inst_solver_per_active                1400
% 3.48/1.05  --inst_solver_calls_frac                1.
% 3.48/1.05  --inst_passive_queue_type               priority_queues
% 3.48/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/1.05  --inst_passive_queues_freq              [25;2]
% 3.48/1.05  --inst_dismatching                      true
% 3.48/1.05  --inst_eager_unprocessed_to_passive     true
% 3.48/1.05  --inst_prop_sim_given                   true
% 3.48/1.05  --inst_prop_sim_new                     false
% 3.48/1.05  --inst_subs_new                         false
% 3.48/1.05  --inst_eq_res_simp                      false
% 3.48/1.05  --inst_subs_given                       false
% 3.48/1.05  --inst_orphan_elimination               true
% 3.48/1.05  --inst_learning_loop_flag               true
% 3.48/1.05  --inst_learning_start                   3000
% 3.48/1.05  --inst_learning_factor                  2
% 3.48/1.05  --inst_start_prop_sim_after_learn       3
% 3.48/1.05  --inst_sel_renew                        solver
% 3.48/1.05  --inst_lit_activity_flag                true
% 3.48/1.05  --inst_restr_to_given                   false
% 3.48/1.05  --inst_activity_threshold               500
% 3.48/1.05  --inst_out_proof                        true
% 3.48/1.05  
% 3.48/1.05  ------ Resolution Options
% 3.48/1.05  
% 3.48/1.05  --resolution_flag                       true
% 3.48/1.05  --res_lit_sel                           adaptive
% 3.48/1.05  --res_lit_sel_side                      none
% 3.48/1.05  --res_ordering                          kbo
% 3.48/1.05  --res_to_prop_solver                    active
% 3.48/1.05  --res_prop_simpl_new                    false
% 3.48/1.05  --res_prop_simpl_given                  true
% 3.48/1.05  --res_passive_queue_type                priority_queues
% 3.48/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/1.05  --res_passive_queues_freq               [15;5]
% 3.48/1.05  --res_forward_subs                      full
% 3.48/1.05  --res_backward_subs                     full
% 3.48/1.05  --res_forward_subs_resolution           true
% 3.48/1.05  --res_backward_subs_resolution          true
% 3.48/1.05  --res_orphan_elimination                true
% 3.48/1.05  --res_time_limit                        2.
% 3.48/1.05  --res_out_proof                         true
% 3.48/1.05  
% 3.48/1.05  ------ Superposition Options
% 3.48/1.05  
% 3.48/1.05  --superposition_flag                    true
% 3.48/1.05  --sup_passive_queue_type                priority_queues
% 3.48/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.48/1.05  --demod_completeness_check              fast
% 3.48/1.05  --demod_use_ground                      true
% 3.48/1.05  --sup_to_prop_solver                    passive
% 3.48/1.05  --sup_prop_simpl_new                    true
% 3.48/1.05  --sup_prop_simpl_given                  true
% 3.48/1.05  --sup_fun_splitting                     false
% 3.48/1.05  --sup_smt_interval                      50000
% 3.48/1.05  
% 3.48/1.05  ------ Superposition Simplification Setup
% 3.48/1.05  
% 3.48/1.05  --sup_indices_passive                   []
% 3.48/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.05  --sup_full_bw                           [BwDemod]
% 3.48/1.05  --sup_immed_triv                        [TrivRules]
% 3.48/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.05  --sup_immed_bw_main                     []
% 3.48/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.05  
% 3.48/1.05  ------ Combination Options
% 3.48/1.05  
% 3.48/1.05  --comb_res_mult                         3
% 3.48/1.05  --comb_sup_mult                         2
% 3.48/1.05  --comb_inst_mult                        10
% 3.48/1.05  
% 3.48/1.05  ------ Debug Options
% 3.48/1.05  
% 3.48/1.05  --dbg_backtrace                         false
% 3.48/1.05  --dbg_dump_prop_clauses                 false
% 3.48/1.05  --dbg_dump_prop_clauses_file            -
% 3.48/1.05  --dbg_out_stat                          false
% 3.48/1.05  ------ Parsing...
% 3.48/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/1.05  
% 3.48/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.48/1.05  
% 3.48/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/1.05  
% 3.48/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.05  ------ Proving...
% 3.48/1.05  ------ Problem Properties 
% 3.48/1.05  
% 3.48/1.05  
% 3.48/1.05  clauses                                 10
% 3.48/1.05  conjectures                             3
% 3.48/1.05  EPR                                     2
% 3.48/1.05  Horn                                    10
% 3.48/1.05  unary                                   6
% 3.48/1.05  binary                                  3
% 3.48/1.05  lits                                    15
% 3.48/1.05  lits eq                                 5
% 3.48/1.05  fd_pure                                 0
% 3.48/1.05  fd_pseudo                               0
% 3.48/1.05  fd_cond                                 0
% 3.48/1.05  fd_pseudo_cond                          0
% 3.48/1.05  AC symbols                              0
% 3.48/1.05  
% 3.48/1.05  ------ Schedule dynamic 5 is on 
% 3.48/1.05  
% 3.48/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.48/1.05  
% 3.48/1.05  
% 3.48/1.05  ------ 
% 3.48/1.05  Current options:
% 3.48/1.05  ------ 
% 3.48/1.05  
% 3.48/1.05  ------ Input Options
% 3.48/1.05  
% 3.48/1.05  --out_options                           all
% 3.48/1.05  --tptp_safe_out                         true
% 3.48/1.05  --problem_path                          ""
% 3.48/1.05  --include_path                          ""
% 3.48/1.05  --clausifier                            res/vclausify_rel
% 3.48/1.05  --clausifier_options                    --mode clausify
% 3.48/1.05  --stdin                                 false
% 3.48/1.05  --stats_out                             all
% 3.48/1.05  
% 3.48/1.05  ------ General Options
% 3.48/1.05  
% 3.48/1.05  --fof                                   false
% 3.48/1.05  --time_out_real                         305.
% 3.48/1.05  --time_out_virtual                      -1.
% 3.48/1.05  --symbol_type_check                     false
% 3.48/1.05  --clausify_out                          false
% 3.48/1.05  --sig_cnt_out                           false
% 3.48/1.05  --trig_cnt_out                          false
% 3.48/1.05  --trig_cnt_out_tolerance                1.
% 3.48/1.05  --trig_cnt_out_sk_spl                   false
% 3.48/1.05  --abstr_cl_out                          false
% 3.48/1.05  
% 3.48/1.05  ------ Global Options
% 3.48/1.05  
% 3.48/1.05  --schedule                              default
% 3.48/1.05  --add_important_lit                     false
% 3.48/1.05  --prop_solver_per_cl                    1000
% 3.48/1.05  --min_unsat_core                        false
% 3.48/1.05  --soft_assumptions                      false
% 3.48/1.05  --soft_lemma_size                       3
% 3.48/1.05  --prop_impl_unit_size                   0
% 3.48/1.05  --prop_impl_unit                        []
% 3.48/1.05  --share_sel_clauses                     true
% 3.48/1.05  --reset_solvers                         false
% 3.48/1.05  --bc_imp_inh                            [conj_cone]
% 3.48/1.05  --conj_cone_tolerance                   3.
% 3.48/1.05  --extra_neg_conj                        none
% 3.48/1.05  --large_theory_mode                     true
% 3.48/1.05  --prolific_symb_bound                   200
% 3.48/1.05  --lt_threshold                          2000
% 3.48/1.05  --clause_weak_htbl                      true
% 3.48/1.05  --gc_record_bc_elim                     false
% 3.48/1.05  
% 3.48/1.05  ------ Preprocessing Options
% 3.48/1.05  
% 3.48/1.05  --preprocessing_flag                    true
% 3.48/1.05  --time_out_prep_mult                    0.1
% 3.48/1.05  --splitting_mode                        input
% 3.48/1.05  --splitting_grd                         true
% 3.48/1.05  --splitting_cvd                         false
% 3.48/1.05  --splitting_cvd_svl                     false
% 3.48/1.05  --splitting_nvd                         32
% 3.48/1.05  --sub_typing                            true
% 3.48/1.05  --prep_gs_sim                           true
% 3.48/1.05  --prep_unflatten                        true
% 3.48/1.05  --prep_res_sim                          true
% 3.48/1.05  --prep_upred                            true
% 3.48/1.05  --prep_sem_filter                       exhaustive
% 3.48/1.05  --prep_sem_filter_out                   false
% 3.48/1.05  --pred_elim                             true
% 3.48/1.05  --res_sim_input                         true
% 3.48/1.05  --eq_ax_congr_red                       true
% 3.48/1.05  --pure_diseq_elim                       true
% 3.48/1.05  --brand_transform                       false
% 3.48/1.05  --non_eq_to_eq                          false
% 3.48/1.05  --prep_def_merge                        true
% 3.48/1.05  --prep_def_merge_prop_impl              false
% 3.48/1.05  --prep_def_merge_mbd                    true
% 3.48/1.05  --prep_def_merge_tr_red                 false
% 3.48/1.05  --prep_def_merge_tr_cl                  false
% 3.48/1.05  --smt_preprocessing                     true
% 3.48/1.05  --smt_ac_axioms                         fast
% 3.48/1.05  --preprocessed_out                      false
% 3.48/1.05  --preprocessed_stats                    false
% 3.48/1.05  
% 3.48/1.05  ------ Abstraction refinement Options
% 3.48/1.05  
% 3.48/1.05  --abstr_ref                             []
% 3.48/1.05  --abstr_ref_prep                        false
% 3.48/1.05  --abstr_ref_until_sat                   false
% 3.48/1.05  --abstr_ref_sig_restrict                funpre
% 3.48/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/1.05  --abstr_ref_under                       []
% 3.48/1.05  
% 3.48/1.05  ------ SAT Options
% 3.48/1.05  
% 3.48/1.05  --sat_mode                              false
% 3.48/1.05  --sat_fm_restart_options                ""
% 3.48/1.05  --sat_gr_def                            false
% 3.48/1.05  --sat_epr_types                         true
% 3.48/1.05  --sat_non_cyclic_types                  false
% 3.48/1.05  --sat_finite_models                     false
% 3.48/1.05  --sat_fm_lemmas                         false
% 3.48/1.05  --sat_fm_prep                           false
% 3.48/1.05  --sat_fm_uc_incr                        true
% 3.48/1.05  --sat_out_model                         small
% 3.48/1.05  --sat_out_clauses                       false
% 3.48/1.05  
% 3.48/1.05  ------ QBF Options
% 3.48/1.05  
% 3.48/1.05  --qbf_mode                              false
% 3.48/1.05  --qbf_elim_univ                         false
% 3.48/1.05  --qbf_dom_inst                          none
% 3.48/1.05  --qbf_dom_pre_inst                      false
% 3.48/1.05  --qbf_sk_in                             false
% 3.48/1.05  --qbf_pred_elim                         true
% 3.48/1.05  --qbf_split                             512
% 3.48/1.05  
% 3.48/1.05  ------ BMC1 Options
% 3.48/1.05  
% 3.48/1.05  --bmc1_incremental                      false
% 3.48/1.05  --bmc1_axioms                           reachable_all
% 3.48/1.05  --bmc1_min_bound                        0
% 3.48/1.05  --bmc1_max_bound                        -1
% 3.48/1.05  --bmc1_max_bound_default                -1
% 3.48/1.05  --bmc1_symbol_reachability              true
% 3.48/1.05  --bmc1_property_lemmas                  false
% 3.48/1.05  --bmc1_k_induction                      false
% 3.48/1.05  --bmc1_non_equiv_states                 false
% 3.48/1.05  --bmc1_deadlock                         false
% 3.48/1.05  --bmc1_ucm                              false
% 3.48/1.05  --bmc1_add_unsat_core                   none
% 3.48/1.05  --bmc1_unsat_core_children              false
% 3.48/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/1.05  --bmc1_out_stat                         full
% 3.48/1.05  --bmc1_ground_init                      false
% 3.48/1.05  --bmc1_pre_inst_next_state              false
% 3.48/1.05  --bmc1_pre_inst_state                   false
% 3.48/1.05  --bmc1_pre_inst_reach_state             false
% 3.48/1.05  --bmc1_out_unsat_core                   false
% 3.48/1.05  --bmc1_aig_witness_out                  false
% 3.48/1.05  --bmc1_verbose                          false
% 3.48/1.05  --bmc1_dump_clauses_tptp                false
% 3.48/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.48/1.05  --bmc1_dump_file                        -
% 3.48/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.48/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.48/1.05  --bmc1_ucm_extend_mode                  1
% 3.48/1.05  --bmc1_ucm_init_mode                    2
% 3.48/1.05  --bmc1_ucm_cone_mode                    none
% 3.48/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.48/1.05  --bmc1_ucm_relax_model                  4
% 3.48/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.48/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/1.05  --bmc1_ucm_layered_model                none
% 3.48/1.05  --bmc1_ucm_max_lemma_size               10
% 3.48/1.05  
% 3.48/1.05  ------ AIG Options
% 3.48/1.05  
% 3.48/1.05  --aig_mode                              false
% 3.48/1.05  
% 3.48/1.05  ------ Instantiation Options
% 3.48/1.05  
% 3.48/1.05  --instantiation_flag                    true
% 3.48/1.05  --inst_sos_flag                         false
% 3.48/1.05  --inst_sos_phase                        true
% 3.48/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/1.05  --inst_lit_sel_side                     none
% 3.48/1.05  --inst_solver_per_active                1400
% 3.48/1.05  --inst_solver_calls_frac                1.
% 3.48/1.05  --inst_passive_queue_type               priority_queues
% 3.48/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/1.05  --inst_passive_queues_freq              [25;2]
% 3.48/1.05  --inst_dismatching                      true
% 3.48/1.05  --inst_eager_unprocessed_to_passive     true
% 3.48/1.05  --inst_prop_sim_given                   true
% 3.48/1.05  --inst_prop_sim_new                     false
% 3.48/1.05  --inst_subs_new                         false
% 3.48/1.05  --inst_eq_res_simp                      false
% 3.48/1.05  --inst_subs_given                       false
% 3.48/1.05  --inst_orphan_elimination               true
% 3.48/1.05  --inst_learning_loop_flag               true
% 3.48/1.05  --inst_learning_start                   3000
% 3.48/1.05  --inst_learning_factor                  2
% 3.48/1.05  --inst_start_prop_sim_after_learn       3
% 3.48/1.05  --inst_sel_renew                        solver
% 3.48/1.05  --inst_lit_activity_flag                true
% 3.48/1.05  --inst_restr_to_given                   false
% 3.48/1.05  --inst_activity_threshold               500
% 3.48/1.05  --inst_out_proof                        true
% 3.48/1.05  
% 3.48/1.05  ------ Resolution Options
% 3.48/1.05  
% 3.48/1.05  --resolution_flag                       false
% 3.48/1.05  --res_lit_sel                           adaptive
% 3.48/1.05  --res_lit_sel_side                      none
% 3.48/1.05  --res_ordering                          kbo
% 3.48/1.05  --res_to_prop_solver                    active
% 3.48/1.05  --res_prop_simpl_new                    false
% 3.48/1.05  --res_prop_simpl_given                  true
% 3.48/1.05  --res_passive_queue_type                priority_queues
% 3.48/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/1.05  --res_passive_queues_freq               [15;5]
% 3.48/1.05  --res_forward_subs                      full
% 3.48/1.05  --res_backward_subs                     full
% 3.48/1.05  --res_forward_subs_resolution           true
% 3.48/1.05  --res_backward_subs_resolution          true
% 3.48/1.05  --res_orphan_elimination                true
% 3.48/1.05  --res_time_limit                        2.
% 3.48/1.05  --res_out_proof                         true
% 3.48/1.05  
% 3.48/1.05  ------ Superposition Options
% 3.48/1.05  
% 3.48/1.05  --superposition_flag                    true
% 3.48/1.05  --sup_passive_queue_type                priority_queues
% 3.48/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.48/1.05  --demod_completeness_check              fast
% 3.48/1.05  --demod_use_ground                      true
% 3.48/1.05  --sup_to_prop_solver                    passive
% 3.48/1.05  --sup_prop_simpl_new                    true
% 3.48/1.05  --sup_prop_simpl_given                  true
% 3.48/1.05  --sup_fun_splitting                     false
% 3.48/1.05  --sup_smt_interval                      50000
% 3.48/1.05  
% 3.48/1.05  ------ Superposition Simplification Setup
% 3.48/1.05  
% 3.48/1.05  --sup_indices_passive                   []
% 3.48/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.05  --sup_full_bw                           [BwDemod]
% 3.48/1.05  --sup_immed_triv                        [TrivRules]
% 3.48/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.05  --sup_immed_bw_main                     []
% 3.48/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.05  
% 3.48/1.05  ------ Combination Options
% 3.48/1.05  
% 3.48/1.05  --comb_res_mult                         3
% 3.48/1.05  --comb_sup_mult                         2
% 3.48/1.05  --comb_inst_mult                        10
% 3.48/1.05  
% 3.48/1.05  ------ Debug Options
% 3.48/1.05  
% 3.48/1.05  --dbg_backtrace                         false
% 3.48/1.05  --dbg_dump_prop_clauses                 false
% 3.48/1.05  --dbg_dump_prop_clauses_file            -
% 3.48/1.05  --dbg_out_stat                          false
% 3.48/1.05  
% 3.48/1.05  
% 3.48/1.05  
% 3.48/1.05  
% 3.48/1.05  ------ Proving...
% 3.48/1.05  
% 3.48/1.05  
% 3.48/1.05  % SZS status Theorem for theBenchmark.p
% 3.48/1.05  
% 3.48/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/1.05  
% 3.48/1.05  fof(f2,axiom,(
% 3.48/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.48/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.05  
% 3.48/1.05  fof(f21,plain,(
% 3.48/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.48/1.05    inference(cnf_transformation,[],[f2])).
% 3.48/1.05  
% 3.48/1.05  fof(f5,axiom,(
% 3.48/1.05    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.48/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.05  
% 3.48/1.05  fof(f24,plain,(
% 3.48/1.05    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.48/1.05    inference(cnf_transformation,[],[f5])).
% 3.48/1.05  
% 3.48/1.05  fof(f1,axiom,(
% 3.48/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.48/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.05  
% 3.48/1.05  fof(f20,plain,(
% 3.48/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.48/1.05    inference(cnf_transformation,[],[f1])).
% 3.48/1.05  
% 3.48/1.05  fof(f37,plain,(
% 3.48/1.05    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.48/1.05    inference(definition_unfolding,[],[f21,f24,f24,f20])).
% 3.48/1.05  
% 3.48/1.05  fof(f3,axiom,(
% 3.48/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 3.48/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.05  
% 3.48/1.05  fof(f13,plain,(
% 3.48/1.05    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 3.48/1.05    inference(ennf_transformation,[],[f3])).
% 3.48/1.05  
% 3.48/1.05  fof(f22,plain,(
% 3.48/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.48/1.05    inference(cnf_transformation,[],[f13])).
% 3.48/1.05  
% 3.48/1.05  fof(f38,plain,(
% 3.48/1.05    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X1 | ~r1_tarski(X0,X1)) )),
% 3.48/1.05    inference(definition_unfolding,[],[f22,f24,f20])).
% 3.48/1.05  
% 3.48/1.05  fof(f10,axiom,(
% 3.48/1.05    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.48/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.05  
% 3.48/1.05  fof(f16,plain,(
% 3.48/1.05    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.48/1.05    inference(nnf_transformation,[],[f10])).
% 3.48/1.05  
% 3.48/1.05  fof(f17,plain,(
% 3.48/1.05    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.48/1.05    inference(flattening,[],[f16])).
% 3.48/1.05  
% 3.48/1.05  fof(f31,plain,(
% 3.48/1.05    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.48/1.05    inference(cnf_transformation,[],[f17])).
% 3.48/1.05  
% 3.48/1.05  fof(f6,axiom,(
% 3.48/1.05    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.48/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.05  
% 3.48/1.05  fof(f25,plain,(
% 3.48/1.05    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.48/1.05    inference(cnf_transformation,[],[f6])).
% 3.48/1.05  
% 3.48/1.05  fof(f7,axiom,(
% 3.48/1.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.48/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.05  
% 3.48/1.05  fof(f26,plain,(
% 3.48/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.48/1.05    inference(cnf_transformation,[],[f7])).
% 3.48/1.05  
% 3.48/1.05  fof(f8,axiom,(
% 3.48/1.05    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.48/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.05  
% 3.48/1.05  fof(f27,plain,(
% 3.48/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.48/1.05    inference(cnf_transformation,[],[f8])).
% 3.48/1.05  
% 3.48/1.05  fof(f35,plain,(
% 3.48/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.48/1.05    inference(definition_unfolding,[],[f26,f27])).
% 3.48/1.05  
% 3.48/1.05  fof(f36,plain,(
% 3.48/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.48/1.05    inference(definition_unfolding,[],[f25,f35])).
% 3.48/1.05  
% 3.48/1.05  fof(f40,plain,(
% 3.48/1.05    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.48/1.05    inference(definition_unfolding,[],[f31,f36])).
% 3.48/1.05  
% 3.48/1.05  fof(f11,conjecture,(
% 3.48/1.05    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 3.48/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.05  
% 3.48/1.05  fof(f12,negated_conjecture,(
% 3.48/1.05    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 3.48/1.05    inference(negated_conjecture,[],[f11])).
% 3.48/1.05  
% 3.48/1.05  fof(f14,plain,(
% 3.48/1.05    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 3.48/1.05    inference(ennf_transformation,[],[f12])).
% 3.48/1.05  
% 3.48/1.05  fof(f15,plain,(
% 3.48/1.05    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 3.48/1.05    inference(flattening,[],[f14])).
% 3.48/1.05  
% 3.48/1.05  fof(f18,plain,(
% 3.48/1.05    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 3.48/1.05    introduced(choice_axiom,[])).
% 3.48/1.05  
% 3.48/1.05  fof(f19,plain,(
% 3.48/1.05    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 3.48/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 3.48/1.05  
% 3.48/1.05  fof(f34,plain,(
% 3.48/1.05    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1),
% 3.48/1.05    inference(cnf_transformation,[],[f19])).
% 3.48/1.05  
% 3.48/1.05  fof(f43,plain,(
% 3.48/1.05    k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != sK1),
% 3.48/1.05    inference(definition_unfolding,[],[f34,f24,f36])).
% 3.48/1.05  
% 3.48/1.05  fof(f33,plain,(
% 3.48/1.05    r2_hidden(sK2,sK1)),
% 3.48/1.05    inference(cnf_transformation,[],[f19])).
% 3.48/1.05  
% 3.48/1.05  fof(f32,plain,(
% 3.48/1.05    r2_hidden(sK0,sK1)),
% 3.48/1.05    inference(cnf_transformation,[],[f19])).
% 3.48/1.05  
% 3.48/1.05  cnf(c_0,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 3.48/1.05      inference(cnf_transformation,[],[f37]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_2456,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_0]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_119,plain,( X0 = X0 ),theory(equality) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_1532,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_119]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_120,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_712,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) != X1
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != X1
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_120]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_1531,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))))
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_712]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_1533,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))))
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_1531]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_304,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != X0
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = sK1
% 3.48/1.05      | sK1 != X0 ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_120]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_660,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))))
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = sK1
% 3.48/1.05      | sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_304]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_661,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))))
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) = sK1
% 3.48/1.05      | sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_660]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_330,plain,
% 3.48/1.05      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_120]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_390,plain,
% 3.48/1.05      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_330]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_466,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) != sK1
% 3.48/1.05      | sK1 = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))))
% 3.48/1.05      | sK1 != sK1 ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_390]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_467,plain,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) != sK1
% 3.48/1.05      | sK1 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))))
% 3.48/1.05      | sK1 != sK1 ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_466]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_1,plain,
% 3.48/1.05      ( ~ r1_tarski(X0,X1)
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X1 ),
% 3.48/1.05      inference(cnf_transformation,[],[f38]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_344,plain,
% 3.48/1.05      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),sK1)
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2)))),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(X0,X0,X0,X0,sK2))))) = sK1 ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_351,plain,
% 3.48/1.05      ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
% 3.48/1.05      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))) = sK1 ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_344]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_336,plain,
% 3.48/1.05      ( sK1 = sK1 ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_119]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_4,plain,
% 3.48/1.05      ( ~ r2_hidden(X0,X1)
% 3.48/1.05      | ~ r2_hidden(X2,X1)
% 3.48/1.05      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 3.48/1.05      inference(cnf_transformation,[],[f40]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_319,plain,
% 3.48/1.05      ( ~ r2_hidden(X0,sK1)
% 3.48/1.05      | ~ r2_hidden(sK2,sK1)
% 3.48/1.05      | r1_tarski(k3_enumset1(X0,X0,X0,X0,sK2),sK1) ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_4]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_321,plain,
% 3.48/1.05      ( ~ r2_hidden(sK2,sK1)
% 3.48/1.05      | ~ r2_hidden(sK0,sK1)
% 3.48/1.05      | r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) ),
% 3.48/1.05      inference(instantiation,[status(thm)],[c_319]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_7,negated_conjecture,
% 3.48/1.05      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != sK1 ),
% 3.48/1.05      inference(cnf_transformation,[],[f43]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_8,negated_conjecture,
% 3.48/1.05      ( r2_hidden(sK2,sK1) ),
% 3.48/1.05      inference(cnf_transformation,[],[f33]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(c_9,negated_conjecture,
% 3.48/1.05      ( r2_hidden(sK0,sK1) ),
% 3.48/1.05      inference(cnf_transformation,[],[f32]) ).
% 3.48/1.05  
% 3.48/1.05  cnf(contradiction,plain,
% 3.48/1.05      ( $false ),
% 3.48/1.05      inference(minisat,
% 3.48/1.05                [status(thm)],
% 3.48/1.05                [c_2456,c_1532,c_1533,c_661,c_467,c_351,c_336,c_321,c_7,
% 3.48/1.05                 c_8,c_9]) ).
% 3.48/1.05  
% 3.48/1.05  
% 3.48/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/1.05  
% 3.48/1.05  ------                               Statistics
% 3.48/1.05  
% 3.48/1.05  ------ General
% 3.48/1.05  
% 3.48/1.05  abstr_ref_over_cycles:                  0
% 3.48/1.05  abstr_ref_under_cycles:                 0
% 3.48/1.05  gc_basic_clause_elim:                   0
% 3.48/1.05  forced_gc_time:                         0
% 3.48/1.05  parsing_time:                           0.018
% 3.48/1.05  unif_index_cands_time:                  0.
% 3.48/1.05  unif_index_add_time:                    0.
% 3.48/1.05  orderings_time:                         0.
% 3.48/1.05  out_proof_time:                         0.015
% 3.48/1.05  total_time:                             0.213
% 3.48/1.05  num_of_symbols:                         40
% 3.48/1.05  num_of_terms:                           4832
% 3.48/1.05  
% 3.48/1.05  ------ Preprocessing
% 3.48/1.05  
% 3.48/1.05  num_of_splits:                          0
% 3.48/1.05  num_of_split_atoms:                     0
% 3.48/1.05  num_of_reused_defs:                     0
% 3.48/1.05  num_eq_ax_congr_red:                    2
% 3.48/1.05  num_of_sem_filtered_clauses:            1
% 3.48/1.05  num_of_subtypes:                        0
% 3.48/1.05  monotx_restored_types:                  0
% 3.48/1.05  sat_num_of_epr_types:                   0
% 3.48/1.05  sat_num_of_non_cyclic_types:            0
% 3.48/1.05  sat_guarded_non_collapsed_types:        0
% 3.48/1.05  num_pure_diseq_elim:                    0
% 3.48/1.05  simp_replaced_by:                       0
% 3.48/1.05  res_preprocessed:                       47
% 3.48/1.05  prep_upred:                             0
% 3.48/1.05  prep_unflattend:                        3
% 3.48/1.05  smt_new_axioms:                         0
% 3.48/1.05  pred_elim_cands:                        2
% 3.48/1.05  pred_elim:                              0
% 3.48/1.05  pred_elim_cl:                           0
% 3.48/1.05  pred_elim_cycles:                       1
% 3.48/1.05  merged_defs:                            0
% 3.48/1.05  merged_defs_ncl:                        0
% 3.48/1.05  bin_hyper_res:                          0
% 3.48/1.05  prep_cycles:                            3
% 3.48/1.05  pred_elim_time:                         0.001
% 3.48/1.05  splitting_time:                         0.
% 3.48/1.05  sem_filter_time:                        0.
% 3.48/1.05  monotx_time:                            0.
% 3.48/1.05  subtype_inf_time:                       0.
% 3.48/1.05  
% 3.48/1.05  ------ Problem properties
% 3.48/1.05  
% 3.48/1.05  clauses:                                10
% 3.48/1.05  conjectures:                            3
% 3.48/1.05  epr:                                    2
% 3.48/1.05  horn:                                   10
% 3.48/1.05  ground:                                 3
% 3.48/1.05  unary:                                  6
% 3.48/1.05  binary:                                 3
% 3.48/1.05  lits:                                   15
% 3.48/1.05  lits_eq:                                5
% 3.48/1.05  fd_pure:                                0
% 3.48/1.05  fd_pseudo:                              0
% 3.48/1.05  fd_cond:                                0
% 3.48/1.05  fd_pseudo_cond:                         0
% 3.48/1.05  ac_symbols:                             0
% 3.48/1.05  
% 3.48/1.05  ------ Propositional Solver
% 3.48/1.05  
% 3.48/1.05  prop_solver_calls:                      24
% 3.48/1.05  prop_fast_solver_calls:                 231
% 3.48/1.05  smt_solver_calls:                       0
% 3.48/1.05  smt_fast_solver_calls:                  0
% 3.48/1.05  prop_num_of_clauses:                    930
% 3.48/1.05  prop_preprocess_simplified:             1858
% 3.48/1.05  prop_fo_subsumed:                       0
% 3.48/1.05  prop_solver_time:                       0.
% 3.48/1.05  smt_solver_time:                        0.
% 3.48/1.05  smt_fast_solver_time:                   0.
% 3.48/1.05  prop_fast_solver_time:                  0.
% 3.48/1.05  prop_unsat_core_time:                   0.
% 3.48/1.05  
% 3.48/1.05  ------ QBF
% 3.48/1.05  
% 3.48/1.05  qbf_q_res:                              0
% 3.48/1.05  qbf_num_tautologies:                    0
% 3.48/1.05  qbf_prep_cycles:                        0
% 3.48/1.05  
% 3.48/1.05  ------ BMC1
% 3.48/1.05  
% 3.48/1.05  bmc1_current_bound:                     -1
% 3.48/1.05  bmc1_last_solved_bound:                 -1
% 3.48/1.05  bmc1_unsat_core_size:                   -1
% 3.48/1.05  bmc1_unsat_core_parents_size:           -1
% 3.48/1.05  bmc1_merge_next_fun:                    0
% 3.48/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.48/1.05  
% 3.48/1.05  ------ Instantiation
% 3.48/1.05  
% 3.48/1.05  inst_num_of_clauses:                    210
% 3.48/1.05  inst_num_in_passive:                    57
% 3.48/1.05  inst_num_in_active:                     118
% 3.48/1.05  inst_num_in_unprocessed:                34
% 3.48/1.05  inst_num_of_loops:                      124
% 3.48/1.05  inst_num_of_learning_restarts:          0
% 3.48/1.05  inst_num_moves_active_passive:          1
% 3.48/1.05  inst_lit_activity:                      0
% 3.48/1.05  inst_lit_activity_moves:                0
% 3.48/1.05  inst_num_tautologies:                   0
% 3.48/1.05  inst_num_prop_implied:                  0
% 3.48/1.05  inst_num_existing_simplified:           0
% 3.48/1.05  inst_num_eq_res_simplified:             0
% 3.48/1.05  inst_num_child_elim:                    0
% 3.48/1.05  inst_num_of_dismatching_blockings:      37
% 3.48/1.05  inst_num_of_non_proper_insts:           187
% 3.48/1.05  inst_num_of_duplicates:                 0
% 3.48/1.05  inst_inst_num_from_inst_to_res:         0
% 3.48/1.05  inst_dismatching_checking_time:         0.
% 3.48/1.05  
% 3.48/1.05  ------ Resolution
% 3.48/1.05  
% 3.48/1.05  res_num_of_clauses:                     0
% 3.48/1.05  res_num_in_passive:                     0
% 3.48/1.05  res_num_in_active:                      0
% 3.48/1.05  res_num_of_loops:                       50
% 3.48/1.05  res_forward_subset_subsumed:            16
% 3.48/1.05  res_backward_subset_subsumed:           0
% 3.48/1.05  res_forward_subsumed:                   0
% 3.48/1.05  res_backward_subsumed:                  0
% 3.48/1.05  res_forward_subsumption_resolution:     0
% 3.48/1.05  res_backward_subsumption_resolution:    0
% 3.48/1.05  res_clause_to_clause_subsumption:       938
% 3.48/1.05  res_orphan_elimination:                 0
% 3.48/1.05  res_tautology_del:                      28
% 3.48/1.05  res_num_eq_res_simplified:              0
% 3.48/1.05  res_num_sel_changes:                    0
% 3.48/1.05  res_moves_from_active_to_pass:          0
% 3.48/1.05  
% 3.48/1.05  ------ Superposition
% 3.48/1.05  
% 3.48/1.05  sup_time_total:                         0.
% 3.48/1.05  sup_time_generating:                    0.
% 3.48/1.05  sup_time_sim_full:                      0.
% 3.48/1.05  sup_time_sim_immed:                     0.
% 3.48/1.05  
% 3.48/1.05  sup_num_of_clauses:                     251
% 3.48/1.05  sup_num_in_active:                      20
% 3.48/1.05  sup_num_in_passive:                     231
% 3.48/1.05  sup_num_of_loops:                       24
% 3.48/1.05  sup_fw_superposition:                   274
% 3.48/1.05  sup_bw_superposition:                   207
% 3.48/1.05  sup_immediate_simplified:               107
% 3.48/1.05  sup_given_eliminated:                   1
% 3.48/1.05  comparisons_done:                       0
% 3.48/1.05  comparisons_avoided:                    0
% 3.48/1.05  
% 3.48/1.05  ------ Simplifications
% 3.48/1.05  
% 3.48/1.05  
% 3.48/1.05  sim_fw_subset_subsumed:                 0
% 3.48/1.05  sim_bw_subset_subsumed:                 0
% 3.48/1.05  sim_fw_subsumed:                        22
% 3.48/1.05  sim_bw_subsumed:                        4
% 3.48/1.05  sim_fw_subsumption_res:                 0
% 3.48/1.05  sim_bw_subsumption_res:                 0
% 3.48/1.05  sim_tautology_del:                      2
% 3.48/1.05  sim_eq_tautology_del:                   3
% 3.48/1.05  sim_eq_res_simp:                        0
% 3.48/1.05  sim_fw_demodulated:                     74
% 3.48/1.05  sim_bw_demodulated:                     8
% 3.48/1.05  sim_light_normalised:                   12
% 3.48/1.05  sim_joinable_taut:                      0
% 3.48/1.05  sim_joinable_simp:                      0
% 3.48/1.05  sim_ac_normalised:                      0
% 3.48/1.05  sim_smt_subsumption:                    0
% 3.48/1.05  
%------------------------------------------------------------------------------
