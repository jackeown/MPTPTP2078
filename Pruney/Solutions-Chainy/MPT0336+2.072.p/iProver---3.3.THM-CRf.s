%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:45 EST 2020

% Result     : Theorem 35.44s
% Output     : CNFRefutation 35.44s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 334 expanded)
%              Number of clauses        :   81 ( 127 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  307 ( 710 expanded)
%              Number of equality atoms :   76 ( 181 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f48,f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f46,f46])).

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

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,
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

fof(f36,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f35])).

fof(f55,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f69,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f55,f46,f60])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f56,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(rectify,[],[f3])).

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

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f31])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_193,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X0_41,k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_116186,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),X0_41)
    | r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK3))) ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_116188,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_116186])).

cnf(c_210,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_98507,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,X2_41)))
    | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != X0_41
    | k4_xboole_0(sK3,k4_xboole_0(sK3,X2_41)) != X1_41 ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_100690,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)))
    | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),X1_41)
    | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))
    | k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)) != X1_41 ),
    inference(instantiation,[status(thm)],[c_98507])).

cnf(c_105720,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)))
    | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK3)))
    | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))
    | k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)) != k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK3)) ),
    inference(instantiation,[status(thm)],[c_100690])).

cnf(c_105722,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
    | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_105720])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_194,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X0_41,k2_xboole_0(X1_41,X2_41))
    | ~ r1_xboole_0(X0_41,X2_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_849,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),X0_41)
    | ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k2_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),X1_41) ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_60974,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k2_xboole_0(sK2,sK4))
    | r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK2)
    | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_201,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2027,plain,
    ( ~ r1_xboole_0(X0_41,k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41)))
    | r1_xboole_0(k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41)),X0_41) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_35665,plain,
    ( ~ r1_xboole_0(X0_41,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))))
    | r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),X0_41) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_35667,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),sK2)
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_35665])).

cnf(c_654,plain,
    ( r1_xboole_0(X0_41,sK4)
    | ~ r1_xboole_0(sK4,X0_41) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_879,plain,
    ( r1_xboole_0(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),sK4)
    | ~ r1_xboole_0(sK4,k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41))) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_3969,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)),sK4)
    | ~ r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41))) ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_24059,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),sK4)
    | ~ r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_3969])).

cnf(c_4002,plain,
    ( r1_xboole_0(X0_41,k4_xboole_0(sK3,k4_xboole_0(sK3,X1_41)))
    | ~ r1_xboole_0(X0_41,sK3) ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_13735,plain,
    ( r1_xboole_0(X0_41,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))))
    | ~ r1_xboole_0(X0_41,sK3) ),
    inference(instantiation,[status(thm)],[c_4002])).

cnf(c_13737,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))))
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_13735])).

cnf(c_659,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X2_41,sK4)
    | X2_41 != X0_41
    | sK4 != X1_41 ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_1041,plain,
    ( ~ r1_xboole_0(X0_41,sK4)
    | r1_xboole_0(X1_41,sK4)
    | X1_41 != X0_41
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_4322,plain,
    ( r1_xboole_0(X0_41,sK4)
    | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1_41)),sK4)
    | X0_41 != k4_xboole_0(sK3,k4_xboole_0(sK3,X1_41))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_10960,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK4)
    | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),sK4)
    | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4322])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_202,plain,
    ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_9616,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_1661,plain,
    ( ~ r1_xboole_0(sK4,X0_41)
    | r1_xboole_0(sK4,k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41))) ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_3470,plain,
    ( r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)))
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_7928,plain,
    ( r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))))
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_3470])).

cnf(c_519,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X0_41,k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_511,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X1_41,X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_1566,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41)),X0_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_519,c_511])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_186,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_526,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_1562,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X0_41,k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41))) = iProver_top ),
    inference(superposition,[status(thm)],[c_202,c_519])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_191,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_xboole_0(X0_41,X2_41)
    | ~ r1_xboole_0(X0_41,k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_521,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X0_41,X2_41) = iProver_top
    | r1_xboole_0(X0_41,k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_3524,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X0_41,X2_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_521])).

cnf(c_4405,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_41) = iProver_top
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_3524])).

cnf(c_4426,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK2) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_4405])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_200,plain,
    ( ~ r2_hidden(X0_42,X0_41)
    | ~ r2_hidden(X0_42,X1_41)
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_558,plain,
    ( ~ r2_hidden(X0_42,sK3)
    | ~ r2_hidden(X0_42,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_559,plain,
    ( r2_hidden(X0_42,sK3) != iProver_top
    | r2_hidden(X0_42,sK4) != iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_561,plain,
    ( r2_hidden(sK5,sK3) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_190,plain,
    ( r2_hidden(X0_42,X0_41)
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_708,plain,
    ( r2_hidden(X0_42,sK3)
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_709,plain,
    ( r2_hidden(X0_42,sK3) = iProver_top
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_711,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_1648,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41)),X0_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_511])).

cnf(c_4427,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_4405])).

cnf(c_4504,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_41) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4426,c_19,c_20,c_561,c_711,c_4427])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_192,plain,
    ( r1_xboole_0(X0_41,X1_41)
    | ~ r1_xboole_0(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),X1_41) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_520,plain,
    ( r1_xboole_0(X0_41,X1_41) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_4512,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4504,c_520])).

cnf(c_4523,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4512])).

cnf(c_3457,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_205,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_1554,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_195,plain,
    ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1298,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_591,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),X0_41)
    | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)))
    | r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_593,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK2)
    | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
    | r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_572,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_116188,c_105722,c_60974,c_35667,c_24059,c_13737,c_10960,c_9616,c_7928,c_4523,c_3457,c_1554,c_1298,c_593,c_572,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:41:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.44/4.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.44/4.99  
% 35.44/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.44/4.99  
% 35.44/4.99  ------  iProver source info
% 35.44/4.99  
% 35.44/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.44/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.44/4.99  git: non_committed_changes: false
% 35.44/4.99  git: last_make_outside_of_git: false
% 35.44/4.99  
% 35.44/4.99  ------ 
% 35.44/4.99  
% 35.44/4.99  ------ Input Options
% 35.44/4.99  
% 35.44/4.99  --out_options                           all
% 35.44/4.99  --tptp_safe_out                         true
% 35.44/4.99  --problem_path                          ""
% 35.44/4.99  --include_path                          ""
% 35.44/4.99  --clausifier                            res/vclausify_rel
% 35.44/4.99  --clausifier_options                    ""
% 35.44/4.99  --stdin                                 false
% 35.44/4.99  --stats_out                             all
% 35.44/4.99  
% 35.44/4.99  ------ General Options
% 35.44/4.99  
% 35.44/4.99  --fof                                   false
% 35.44/4.99  --time_out_real                         305.
% 35.44/4.99  --time_out_virtual                      -1.
% 35.44/4.99  --symbol_type_check                     false
% 35.44/4.99  --clausify_out                          false
% 35.44/4.99  --sig_cnt_out                           false
% 35.44/4.99  --trig_cnt_out                          false
% 35.44/4.99  --trig_cnt_out_tolerance                1.
% 35.44/4.99  --trig_cnt_out_sk_spl                   false
% 35.44/4.99  --abstr_cl_out                          false
% 35.44/4.99  
% 35.44/4.99  ------ Global Options
% 35.44/4.99  
% 35.44/4.99  --schedule                              default
% 35.44/4.99  --add_important_lit                     false
% 35.44/4.99  --prop_solver_per_cl                    1000
% 35.44/4.99  --min_unsat_core                        false
% 35.44/4.99  --soft_assumptions                      false
% 35.44/4.99  --soft_lemma_size                       3
% 35.44/4.99  --prop_impl_unit_size                   0
% 35.44/4.99  --prop_impl_unit                        []
% 35.44/4.99  --share_sel_clauses                     true
% 35.44/4.99  --reset_solvers                         false
% 35.44/4.99  --bc_imp_inh                            [conj_cone]
% 35.44/4.99  --conj_cone_tolerance                   3.
% 35.44/4.99  --extra_neg_conj                        none
% 35.44/4.99  --large_theory_mode                     true
% 35.44/4.99  --prolific_symb_bound                   200
% 35.44/4.99  --lt_threshold                          2000
% 35.44/4.99  --clause_weak_htbl                      true
% 35.44/4.99  --gc_record_bc_elim                     false
% 35.44/4.99  
% 35.44/4.99  ------ Preprocessing Options
% 35.44/4.99  
% 35.44/4.99  --preprocessing_flag                    true
% 35.44/4.99  --time_out_prep_mult                    0.1
% 35.44/4.99  --splitting_mode                        input
% 35.44/4.99  --splitting_grd                         true
% 35.44/4.99  --splitting_cvd                         false
% 35.44/4.99  --splitting_cvd_svl                     false
% 35.44/4.99  --splitting_nvd                         32
% 35.44/4.99  --sub_typing                            true
% 35.44/4.99  --prep_gs_sim                           true
% 35.44/4.99  --prep_unflatten                        true
% 35.44/4.99  --prep_res_sim                          true
% 35.44/4.99  --prep_upred                            true
% 35.44/4.99  --prep_sem_filter                       exhaustive
% 35.44/4.99  --prep_sem_filter_out                   false
% 35.44/4.99  --pred_elim                             true
% 35.44/4.99  --res_sim_input                         true
% 35.44/4.99  --eq_ax_congr_red                       true
% 35.44/4.99  --pure_diseq_elim                       true
% 35.44/4.99  --brand_transform                       false
% 35.44/4.99  --non_eq_to_eq                          false
% 35.44/4.99  --prep_def_merge                        true
% 35.44/4.99  --prep_def_merge_prop_impl              false
% 35.44/4.99  --prep_def_merge_mbd                    true
% 35.44/4.99  --prep_def_merge_tr_red                 false
% 35.44/4.99  --prep_def_merge_tr_cl                  false
% 35.44/4.99  --smt_preprocessing                     true
% 35.44/4.99  --smt_ac_axioms                         fast
% 35.44/4.99  --preprocessed_out                      false
% 35.44/4.99  --preprocessed_stats                    false
% 35.44/4.99  
% 35.44/4.99  ------ Abstraction refinement Options
% 35.44/4.99  
% 35.44/4.99  --abstr_ref                             []
% 35.44/4.99  --abstr_ref_prep                        false
% 35.44/4.99  --abstr_ref_until_sat                   false
% 35.44/4.99  --abstr_ref_sig_restrict                funpre
% 35.44/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.44/4.99  --abstr_ref_under                       []
% 35.44/4.99  
% 35.44/4.99  ------ SAT Options
% 35.44/4.99  
% 35.44/4.99  --sat_mode                              false
% 35.44/4.99  --sat_fm_restart_options                ""
% 35.44/4.99  --sat_gr_def                            false
% 35.44/4.99  --sat_epr_types                         true
% 35.44/4.99  --sat_non_cyclic_types                  false
% 35.44/4.99  --sat_finite_models                     false
% 35.44/4.99  --sat_fm_lemmas                         false
% 35.44/4.99  --sat_fm_prep                           false
% 35.44/4.99  --sat_fm_uc_incr                        true
% 35.44/4.99  --sat_out_model                         small
% 35.44/4.99  --sat_out_clauses                       false
% 35.44/4.99  
% 35.44/4.99  ------ QBF Options
% 35.44/4.99  
% 35.44/4.99  --qbf_mode                              false
% 35.44/4.99  --qbf_elim_univ                         false
% 35.44/4.99  --qbf_dom_inst                          none
% 35.44/4.99  --qbf_dom_pre_inst                      false
% 35.44/4.99  --qbf_sk_in                             false
% 35.44/4.99  --qbf_pred_elim                         true
% 35.44/4.99  --qbf_split                             512
% 35.44/4.99  
% 35.44/4.99  ------ BMC1 Options
% 35.44/4.99  
% 35.44/4.99  --bmc1_incremental                      false
% 35.44/4.99  --bmc1_axioms                           reachable_all
% 35.44/4.99  --bmc1_min_bound                        0
% 35.44/4.99  --bmc1_max_bound                        -1
% 35.44/4.99  --bmc1_max_bound_default                -1
% 35.44/4.99  --bmc1_symbol_reachability              true
% 35.44/4.99  --bmc1_property_lemmas                  false
% 35.44/4.99  --bmc1_k_induction                      false
% 35.44/4.99  --bmc1_non_equiv_states                 false
% 35.44/4.99  --bmc1_deadlock                         false
% 35.44/4.99  --bmc1_ucm                              false
% 35.44/4.99  --bmc1_add_unsat_core                   none
% 35.44/4.99  --bmc1_unsat_core_children              false
% 35.44/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.44/4.99  --bmc1_out_stat                         full
% 35.44/4.99  --bmc1_ground_init                      false
% 35.44/4.99  --bmc1_pre_inst_next_state              false
% 35.44/4.99  --bmc1_pre_inst_state                   false
% 35.44/4.99  --bmc1_pre_inst_reach_state             false
% 35.44/4.99  --bmc1_out_unsat_core                   false
% 35.44/4.99  --bmc1_aig_witness_out                  false
% 35.44/4.99  --bmc1_verbose                          false
% 35.44/4.99  --bmc1_dump_clauses_tptp                false
% 35.44/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.44/4.99  --bmc1_dump_file                        -
% 35.44/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.44/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.44/4.99  --bmc1_ucm_extend_mode                  1
% 35.44/4.99  --bmc1_ucm_init_mode                    2
% 35.44/4.99  --bmc1_ucm_cone_mode                    none
% 35.44/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.44/4.99  --bmc1_ucm_relax_model                  4
% 35.44/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.44/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.44/4.99  --bmc1_ucm_layered_model                none
% 35.44/4.99  --bmc1_ucm_max_lemma_size               10
% 35.44/4.99  
% 35.44/4.99  ------ AIG Options
% 35.44/4.99  
% 35.44/4.99  --aig_mode                              false
% 35.44/4.99  
% 35.44/4.99  ------ Instantiation Options
% 35.44/4.99  
% 35.44/4.99  --instantiation_flag                    true
% 35.44/4.99  --inst_sos_flag                         true
% 35.44/4.99  --inst_sos_phase                        true
% 35.44/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.44/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.44/4.99  --inst_lit_sel_side                     num_symb
% 35.44/4.99  --inst_solver_per_active                1400
% 35.44/4.99  --inst_solver_calls_frac                1.
% 35.44/4.99  --inst_passive_queue_type               priority_queues
% 35.44/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.44/4.99  --inst_passive_queues_freq              [25;2]
% 35.44/4.99  --inst_dismatching                      true
% 35.44/4.99  --inst_eager_unprocessed_to_passive     true
% 35.44/4.99  --inst_prop_sim_given                   true
% 35.44/4.99  --inst_prop_sim_new                     false
% 35.44/4.99  --inst_subs_new                         false
% 35.44/4.99  --inst_eq_res_simp                      false
% 35.44/4.99  --inst_subs_given                       false
% 35.44/4.99  --inst_orphan_elimination               true
% 35.44/4.99  --inst_learning_loop_flag               true
% 35.44/4.99  --inst_learning_start                   3000
% 35.44/4.99  --inst_learning_factor                  2
% 35.44/4.99  --inst_start_prop_sim_after_learn       3
% 35.44/4.99  --inst_sel_renew                        solver
% 35.44/4.99  --inst_lit_activity_flag                true
% 35.44/4.99  --inst_restr_to_given                   false
% 35.44/4.99  --inst_activity_threshold               500
% 35.44/4.99  --inst_out_proof                        true
% 35.44/4.99  
% 35.44/4.99  ------ Resolution Options
% 35.44/4.99  
% 35.44/4.99  --resolution_flag                       true
% 35.44/4.99  --res_lit_sel                           adaptive
% 35.44/4.99  --res_lit_sel_side                      none
% 35.44/4.99  --res_ordering                          kbo
% 35.44/4.99  --res_to_prop_solver                    active
% 35.44/4.99  --res_prop_simpl_new                    false
% 35.44/4.99  --res_prop_simpl_given                  true
% 35.44/4.99  --res_passive_queue_type                priority_queues
% 35.44/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.44/4.99  --res_passive_queues_freq               [15;5]
% 35.44/4.99  --res_forward_subs                      full
% 35.44/4.99  --res_backward_subs                     full
% 35.44/4.99  --res_forward_subs_resolution           true
% 35.44/4.99  --res_backward_subs_resolution          true
% 35.44/4.99  --res_orphan_elimination                true
% 35.44/4.99  --res_time_limit                        2.
% 35.44/4.99  --res_out_proof                         true
% 35.44/4.99  
% 35.44/4.99  ------ Superposition Options
% 35.44/4.99  
% 35.44/4.99  --superposition_flag                    true
% 35.44/4.99  --sup_passive_queue_type                priority_queues
% 35.44/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.44/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.44/4.99  --demod_completeness_check              fast
% 35.44/4.99  --demod_use_ground                      true
% 35.44/4.99  --sup_to_prop_solver                    passive
% 35.44/4.99  --sup_prop_simpl_new                    true
% 35.44/4.99  --sup_prop_simpl_given                  true
% 35.44/4.99  --sup_fun_splitting                     true
% 35.44/4.99  --sup_smt_interval                      50000
% 35.44/4.99  
% 35.44/4.99  ------ Superposition Simplification Setup
% 35.44/4.99  
% 35.44/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.44/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.44/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.44/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.44/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.44/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.44/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.44/4.99  --sup_immed_triv                        [TrivRules]
% 35.44/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.99  --sup_immed_bw_main                     []
% 35.44/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.44/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.44/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.99  --sup_input_bw                          []
% 35.44/4.99  
% 35.44/4.99  ------ Combination Options
% 35.44/4.99  
% 35.44/4.99  --comb_res_mult                         3
% 35.44/4.99  --comb_sup_mult                         2
% 35.44/4.99  --comb_inst_mult                        10
% 35.44/4.99  
% 35.44/4.99  ------ Debug Options
% 35.44/4.99  
% 35.44/4.99  --dbg_backtrace                         false
% 35.44/4.99  --dbg_dump_prop_clauses                 false
% 35.44/4.99  --dbg_dump_prop_clauses_file            -
% 35.44/4.99  --dbg_out_stat                          false
% 35.44/4.99  ------ Parsing...
% 35.44/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.44/4.99  
% 35.44/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.44/4.99  
% 35.44/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.44/4.99  
% 35.44/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.44/4.99  ------ Proving...
% 35.44/4.99  ------ Problem Properties 
% 35.44/4.99  
% 35.44/4.99  
% 35.44/4.99  clauses                                 18
% 35.44/4.99  conjectures                             4
% 35.44/4.99  EPR                                     4
% 35.44/4.99  Horn                                    14
% 35.44/4.99  unary                                   7
% 35.44/4.99  binary                                  8
% 35.44/4.99  lits                                    32
% 35.44/4.99  lits eq                                 2
% 35.44/4.99  fd_pure                                 0
% 35.44/4.99  fd_pseudo                               0
% 35.44/4.99  fd_cond                                 0
% 35.44/4.99  fd_pseudo_cond                          0
% 35.44/4.99  AC symbols                              0
% 35.44/4.99  
% 35.44/4.99  ------ Schedule dynamic 5 is on 
% 35.44/4.99  
% 35.44/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.44/4.99  
% 35.44/4.99  
% 35.44/4.99  ------ 
% 35.44/4.99  Current options:
% 35.44/4.99  ------ 
% 35.44/4.99  
% 35.44/4.99  ------ Input Options
% 35.44/4.99  
% 35.44/4.99  --out_options                           all
% 35.44/4.99  --tptp_safe_out                         true
% 35.44/4.99  --problem_path                          ""
% 35.44/4.99  --include_path                          ""
% 35.44/4.99  --clausifier                            res/vclausify_rel
% 35.44/4.99  --clausifier_options                    ""
% 35.44/4.99  --stdin                                 false
% 35.44/4.99  --stats_out                             all
% 35.44/4.99  
% 35.44/4.99  ------ General Options
% 35.44/4.99  
% 35.44/4.99  --fof                                   false
% 35.44/4.99  --time_out_real                         305.
% 35.44/4.99  --time_out_virtual                      -1.
% 35.44/4.99  --symbol_type_check                     false
% 35.44/4.99  --clausify_out                          false
% 35.44/4.99  --sig_cnt_out                           false
% 35.44/4.99  --trig_cnt_out                          false
% 35.44/4.99  --trig_cnt_out_tolerance                1.
% 35.44/4.99  --trig_cnt_out_sk_spl                   false
% 35.44/4.99  --abstr_cl_out                          false
% 35.44/4.99  
% 35.44/4.99  ------ Global Options
% 35.44/4.99  
% 35.44/4.99  --schedule                              default
% 35.44/4.99  --add_important_lit                     false
% 35.44/4.99  --prop_solver_per_cl                    1000
% 35.44/4.99  --min_unsat_core                        false
% 35.44/4.99  --soft_assumptions                      false
% 35.44/4.99  --soft_lemma_size                       3
% 35.44/4.99  --prop_impl_unit_size                   0
% 35.44/4.99  --prop_impl_unit                        []
% 35.44/4.99  --share_sel_clauses                     true
% 35.44/4.99  --reset_solvers                         false
% 35.44/4.99  --bc_imp_inh                            [conj_cone]
% 35.44/4.99  --conj_cone_tolerance                   3.
% 35.44/4.99  --extra_neg_conj                        none
% 35.44/4.99  --large_theory_mode                     true
% 35.44/4.99  --prolific_symb_bound                   200
% 35.44/4.99  --lt_threshold                          2000
% 35.44/4.99  --clause_weak_htbl                      true
% 35.44/4.99  --gc_record_bc_elim                     false
% 35.44/4.99  
% 35.44/4.99  ------ Preprocessing Options
% 35.44/4.99  
% 35.44/4.99  --preprocessing_flag                    true
% 35.44/4.99  --time_out_prep_mult                    0.1
% 35.44/4.99  --splitting_mode                        input
% 35.44/4.99  --splitting_grd                         true
% 35.44/4.99  --splitting_cvd                         false
% 35.44/4.99  --splitting_cvd_svl                     false
% 35.44/4.99  --splitting_nvd                         32
% 35.44/4.99  --sub_typing                            true
% 35.44/4.99  --prep_gs_sim                           true
% 35.44/4.99  --prep_unflatten                        true
% 35.44/4.99  --prep_res_sim                          true
% 35.44/4.99  --prep_upred                            true
% 35.44/4.99  --prep_sem_filter                       exhaustive
% 35.44/4.99  --prep_sem_filter_out                   false
% 35.44/4.99  --pred_elim                             true
% 35.44/4.99  --res_sim_input                         true
% 35.44/4.99  --eq_ax_congr_red                       true
% 35.44/4.99  --pure_diseq_elim                       true
% 35.44/4.99  --brand_transform                       false
% 35.44/4.99  --non_eq_to_eq                          false
% 35.44/4.99  --prep_def_merge                        true
% 35.44/4.99  --prep_def_merge_prop_impl              false
% 35.44/4.99  --prep_def_merge_mbd                    true
% 35.44/4.99  --prep_def_merge_tr_red                 false
% 35.44/4.99  --prep_def_merge_tr_cl                  false
% 35.44/4.99  --smt_preprocessing                     true
% 35.44/4.99  --smt_ac_axioms                         fast
% 35.44/4.99  --preprocessed_out                      false
% 35.44/4.99  --preprocessed_stats                    false
% 35.44/4.99  
% 35.44/4.99  ------ Abstraction refinement Options
% 35.44/4.99  
% 35.44/4.99  --abstr_ref                             []
% 35.44/4.99  --abstr_ref_prep                        false
% 35.44/4.99  --abstr_ref_until_sat                   false
% 35.44/4.99  --abstr_ref_sig_restrict                funpre
% 35.44/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.44/4.99  --abstr_ref_under                       []
% 35.44/4.99  
% 35.44/4.99  ------ SAT Options
% 35.44/4.99  
% 35.44/4.99  --sat_mode                              false
% 35.44/4.99  --sat_fm_restart_options                ""
% 35.44/4.99  --sat_gr_def                            false
% 35.44/4.99  --sat_epr_types                         true
% 35.44/4.99  --sat_non_cyclic_types                  false
% 35.44/4.99  --sat_finite_models                     false
% 35.44/4.99  --sat_fm_lemmas                         false
% 35.44/4.99  --sat_fm_prep                           false
% 35.44/4.99  --sat_fm_uc_incr                        true
% 35.44/4.99  --sat_out_model                         small
% 35.44/4.99  --sat_out_clauses                       false
% 35.44/4.99  
% 35.44/4.99  ------ QBF Options
% 35.44/4.99  
% 35.44/4.99  --qbf_mode                              false
% 35.44/4.99  --qbf_elim_univ                         false
% 35.44/4.99  --qbf_dom_inst                          none
% 35.44/4.99  --qbf_dom_pre_inst                      false
% 35.44/4.99  --qbf_sk_in                             false
% 35.44/4.99  --qbf_pred_elim                         true
% 35.44/4.99  --qbf_split                             512
% 35.44/4.99  
% 35.44/4.99  ------ BMC1 Options
% 35.44/4.99  
% 35.44/4.99  --bmc1_incremental                      false
% 35.44/4.99  --bmc1_axioms                           reachable_all
% 35.44/4.99  --bmc1_min_bound                        0
% 35.44/4.99  --bmc1_max_bound                        -1
% 35.44/4.99  --bmc1_max_bound_default                -1
% 35.44/4.99  --bmc1_symbol_reachability              true
% 35.44/4.99  --bmc1_property_lemmas                  false
% 35.44/4.99  --bmc1_k_induction                      false
% 35.44/4.99  --bmc1_non_equiv_states                 false
% 35.44/4.99  --bmc1_deadlock                         false
% 35.44/4.99  --bmc1_ucm                              false
% 35.44/4.99  --bmc1_add_unsat_core                   none
% 35.44/4.99  --bmc1_unsat_core_children              false
% 35.44/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.44/4.99  --bmc1_out_stat                         full
% 35.44/4.99  --bmc1_ground_init                      false
% 35.44/4.99  --bmc1_pre_inst_next_state              false
% 35.44/4.99  --bmc1_pre_inst_state                   false
% 35.44/4.99  --bmc1_pre_inst_reach_state             false
% 35.44/4.99  --bmc1_out_unsat_core                   false
% 35.44/4.99  --bmc1_aig_witness_out                  false
% 35.44/4.99  --bmc1_verbose                          false
% 35.44/4.99  --bmc1_dump_clauses_tptp                false
% 35.44/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.44/4.99  --bmc1_dump_file                        -
% 35.44/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.44/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.44/4.99  --bmc1_ucm_extend_mode                  1
% 35.44/4.99  --bmc1_ucm_init_mode                    2
% 35.44/4.99  --bmc1_ucm_cone_mode                    none
% 35.44/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.44/4.99  --bmc1_ucm_relax_model                  4
% 35.44/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.44/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.44/4.99  --bmc1_ucm_layered_model                none
% 35.44/4.99  --bmc1_ucm_max_lemma_size               10
% 35.44/4.99  
% 35.44/4.99  ------ AIG Options
% 35.44/4.99  
% 35.44/4.99  --aig_mode                              false
% 35.44/4.99  
% 35.44/4.99  ------ Instantiation Options
% 35.44/4.99  
% 35.44/4.99  --instantiation_flag                    true
% 35.44/4.99  --inst_sos_flag                         true
% 35.44/4.99  --inst_sos_phase                        true
% 35.44/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.44/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.44/4.99  --inst_lit_sel_side                     none
% 35.44/4.99  --inst_solver_per_active                1400
% 35.44/4.99  --inst_solver_calls_frac                1.
% 35.44/4.99  --inst_passive_queue_type               priority_queues
% 35.44/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.44/4.99  --inst_passive_queues_freq              [25;2]
% 35.44/4.99  --inst_dismatching                      true
% 35.44/4.99  --inst_eager_unprocessed_to_passive     true
% 35.44/4.99  --inst_prop_sim_given                   true
% 35.44/4.99  --inst_prop_sim_new                     false
% 35.44/4.99  --inst_subs_new                         false
% 35.44/4.99  --inst_eq_res_simp                      false
% 35.44/4.99  --inst_subs_given                       false
% 35.44/4.99  --inst_orphan_elimination               true
% 35.44/4.99  --inst_learning_loop_flag               true
% 35.44/4.99  --inst_learning_start                   3000
% 35.44/4.99  --inst_learning_factor                  2
% 35.44/4.99  --inst_start_prop_sim_after_learn       3
% 35.44/4.99  --inst_sel_renew                        solver
% 35.44/4.99  --inst_lit_activity_flag                true
% 35.44/4.99  --inst_restr_to_given                   false
% 35.44/4.99  --inst_activity_threshold               500
% 35.44/4.99  --inst_out_proof                        true
% 35.44/4.99  
% 35.44/4.99  ------ Resolution Options
% 35.44/4.99  
% 35.44/4.99  --resolution_flag                       false
% 35.44/4.99  --res_lit_sel                           adaptive
% 35.44/4.99  --res_lit_sel_side                      none
% 35.44/4.99  --res_ordering                          kbo
% 35.44/4.99  --res_to_prop_solver                    active
% 35.44/4.99  --res_prop_simpl_new                    false
% 35.44/4.99  --res_prop_simpl_given                  true
% 35.44/4.99  --res_passive_queue_type                priority_queues
% 35.44/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.44/4.99  --res_passive_queues_freq               [15;5]
% 35.44/4.99  --res_forward_subs                      full
% 35.44/4.99  --res_backward_subs                     full
% 35.44/4.99  --res_forward_subs_resolution           true
% 35.44/4.99  --res_backward_subs_resolution          true
% 35.44/4.99  --res_orphan_elimination                true
% 35.44/4.99  --res_time_limit                        2.
% 35.44/4.99  --res_out_proof                         true
% 35.44/4.99  
% 35.44/4.99  ------ Superposition Options
% 35.44/4.99  
% 35.44/4.99  --superposition_flag                    true
% 35.44/4.99  --sup_passive_queue_type                priority_queues
% 35.44/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.44/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.44/4.99  --demod_completeness_check              fast
% 35.44/4.99  --demod_use_ground                      true
% 35.44/4.99  --sup_to_prop_solver                    passive
% 35.44/4.99  --sup_prop_simpl_new                    true
% 35.44/4.99  --sup_prop_simpl_given                  true
% 35.44/4.99  --sup_fun_splitting                     true
% 35.44/4.99  --sup_smt_interval                      50000
% 35.44/4.99  
% 35.44/4.99  ------ Superposition Simplification Setup
% 35.44/4.99  
% 35.44/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.44/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.44/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.44/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.44/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.44/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.44/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.44/4.99  --sup_immed_triv                        [TrivRules]
% 35.44/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.99  --sup_immed_bw_main                     []
% 35.44/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.44/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.44/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.99  --sup_input_bw                          []
% 35.44/4.99  
% 35.44/4.99  ------ Combination Options
% 35.44/4.99  
% 35.44/4.99  --comb_res_mult                         3
% 35.44/4.99  --comb_sup_mult                         2
% 35.44/4.99  --comb_inst_mult                        10
% 35.44/4.99  
% 35.44/4.99  ------ Debug Options
% 35.44/4.99  
% 35.44/4.99  --dbg_backtrace                         false
% 35.44/4.99  --dbg_dump_prop_clauses                 false
% 35.44/4.99  --dbg_dump_prop_clauses_file            -
% 35.44/4.99  --dbg_out_stat                          false
% 35.44/4.99  
% 35.44/4.99  
% 35.44/4.99  
% 35.44/4.99  
% 35.44/4.99  ------ Proving...
% 35.44/4.99  
% 35.44/4.99  
% 35.44/4.99  % SZS status Theorem for theBenchmark.p
% 35.44/4.99  
% 35.44/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.44/4.99  
% 35.44/4.99  fof(f9,axiom,(
% 35.44/4.99    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f25,plain,(
% 35.44/4.99    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 35.44/4.99    inference(ennf_transformation,[],[f9])).
% 35.44/4.99  
% 35.44/4.99  fof(f48,plain,(
% 35.44/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 35.44/4.99    inference(cnf_transformation,[],[f25])).
% 35.44/4.99  
% 35.44/4.99  fof(f7,axiom,(
% 35.44/4.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f46,plain,(
% 35.44/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.44/4.99    inference(cnf_transformation,[],[f7])).
% 35.44/4.99  
% 35.44/4.99  fof(f65,plain,(
% 35.44/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 35.44/4.99    inference(definition_unfolding,[],[f48,f46])).
% 35.44/4.99  
% 35.44/4.99  fof(f8,axiom,(
% 35.44/4.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f23,plain,(
% 35.44/4.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 35.44/4.99    inference(ennf_transformation,[],[f8])).
% 35.44/4.99  
% 35.44/4.99  fof(f24,plain,(
% 35.44/4.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.44/4.99    inference(flattening,[],[f23])).
% 35.44/4.99  
% 35.44/4.99  fof(f47,plain,(
% 35.44/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 35.44/4.99    inference(cnf_transformation,[],[f24])).
% 35.44/4.99  
% 35.44/4.99  fof(f2,axiom,(
% 35.44/4.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f20,plain,(
% 35.44/4.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 35.44/4.99    inference(ennf_transformation,[],[f2])).
% 35.44/4.99  
% 35.44/4.99  fof(f38,plain,(
% 35.44/4.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f20])).
% 35.44/4.99  
% 35.44/4.99  fof(f1,axiom,(
% 35.44/4.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f37,plain,(
% 35.44/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f1])).
% 35.44/4.99  
% 35.44/4.99  fof(f62,plain,(
% 35.44/4.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 35.44/4.99    inference(definition_unfolding,[],[f37,f46,f46])).
% 35.44/4.99  
% 35.44/4.99  fof(f16,conjecture,(
% 35.44/4.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f17,negated_conjecture,(
% 35.44/4.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.44/4.99    inference(negated_conjecture,[],[f16])).
% 35.44/4.99  
% 35.44/4.99  fof(f29,plain,(
% 35.44/4.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 35.44/4.99    inference(ennf_transformation,[],[f17])).
% 35.44/4.99  
% 35.44/4.99  fof(f30,plain,(
% 35.44/4.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 35.44/4.99    inference(flattening,[],[f29])).
% 35.44/4.99  
% 35.44/4.99  fof(f35,plain,(
% 35.44/4.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 35.44/4.99    introduced(choice_axiom,[])).
% 35.44/4.99  
% 35.44/4.99  fof(f36,plain,(
% 35.44/4.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 35.44/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f35])).
% 35.44/4.99  
% 35.44/4.99  fof(f55,plain,(
% 35.44/4.99    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 35.44/4.99    inference(cnf_transformation,[],[f36])).
% 35.44/4.99  
% 35.44/4.99  fof(f12,axiom,(
% 35.44/4.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f51,plain,(
% 35.44/4.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f12])).
% 35.44/4.99  
% 35.44/4.99  fof(f13,axiom,(
% 35.44/4.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f52,plain,(
% 35.44/4.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f13])).
% 35.44/4.99  
% 35.44/4.99  fof(f14,axiom,(
% 35.44/4.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f53,plain,(
% 35.44/4.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f14])).
% 35.44/4.99  
% 35.44/4.99  fof(f59,plain,(
% 35.44/4.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 35.44/4.99    inference(definition_unfolding,[],[f52,f53])).
% 35.44/4.99  
% 35.44/4.99  fof(f60,plain,(
% 35.44/4.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 35.44/4.99    inference(definition_unfolding,[],[f51,f59])).
% 35.44/4.99  
% 35.44/4.99  fof(f69,plain,(
% 35.44/4.99    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))),
% 35.44/4.99    inference(definition_unfolding,[],[f55,f46,f60])).
% 35.44/4.99  
% 35.44/4.99  fof(f11,axiom,(
% 35.44/4.99    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f27,plain,(
% 35.44/4.99    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 35.44/4.99    inference(ennf_transformation,[],[f11])).
% 35.44/4.99  
% 35.44/4.99  fof(f50,plain,(
% 35.44/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f27])).
% 35.44/4.99  
% 35.44/4.99  fof(f67,plain,(
% 35.44/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 35.44/4.99    inference(definition_unfolding,[],[f50,f46])).
% 35.44/4.99  
% 35.44/4.99  fof(f56,plain,(
% 35.44/4.99    r2_hidden(sK5,sK4)),
% 35.44/4.99    inference(cnf_transformation,[],[f36])).
% 35.44/4.99  
% 35.44/4.99  fof(f57,plain,(
% 35.44/4.99    r1_xboole_0(sK4,sK3)),
% 35.44/4.99    inference(cnf_transformation,[],[f36])).
% 35.44/4.99  
% 35.44/4.99  fof(f3,axiom,(
% 35.44/4.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f18,plain,(
% 35.44/4.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.44/4.99    inference(rectify,[],[f3])).
% 35.44/4.99  
% 35.44/4.99  fof(f21,plain,(
% 35.44/4.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 35.44/4.99    inference(ennf_transformation,[],[f18])).
% 35.44/4.99  
% 35.44/4.99  fof(f31,plain,(
% 35.44/4.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 35.44/4.99    introduced(choice_axiom,[])).
% 35.44/4.99  
% 35.44/4.99  fof(f32,plain,(
% 35.44/4.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 35.44/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f31])).
% 35.44/4.99  
% 35.44/4.99  fof(f41,plain,(
% 35.44/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f32])).
% 35.44/4.99  
% 35.44/4.99  fof(f15,axiom,(
% 35.44/4.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f28,plain,(
% 35.44/4.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 35.44/4.99    inference(ennf_transformation,[],[f15])).
% 35.44/4.99  
% 35.44/4.99  fof(f54,plain,(
% 35.44/4.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f28])).
% 35.44/4.99  
% 35.44/4.99  fof(f68,plain,(
% 35.44/4.99    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 35.44/4.99    inference(definition_unfolding,[],[f54,f60])).
% 35.44/4.99  
% 35.44/4.99  fof(f10,axiom,(
% 35.44/4.99    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f26,plain,(
% 35.44/4.99    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 35.44/4.99    inference(ennf_transformation,[],[f10])).
% 35.44/4.99  
% 35.44/4.99  fof(f49,plain,(
% 35.44/4.99    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f26])).
% 35.44/4.99  
% 35.44/4.99  fof(f66,plain,(
% 35.44/4.99    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 35.44/4.99    inference(definition_unfolding,[],[f49,f46])).
% 35.44/4.99  
% 35.44/4.99  fof(f6,axiom,(
% 35.44/4.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.44/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.99  
% 35.44/4.99  fof(f45,plain,(
% 35.44/4.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.44/4.99    inference(cnf_transformation,[],[f6])).
% 35.44/4.99  
% 35.44/4.99  fof(f58,plain,(
% 35.44/4.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 35.44/4.99    inference(cnf_transformation,[],[f36])).
% 35.44/4.99  
% 35.44/4.99  cnf(c_10,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0,X1)
% 35.44/4.99      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 35.44/4.99      inference(cnf_transformation,[],[f65]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_193,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 35.44/4.99      | r1_xboole_0(X0_41,k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41))) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_10]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_116186,plain,
% 35.44/4.99      ( ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),X0_41)
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK3))) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_193]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_116188,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),sK2) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_116186]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_210,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 35.44/4.99      | r1_xboole_0(X2_41,X3_41)
% 35.44/4.99      | X2_41 != X0_41
% 35.44/4.99      | X3_41 != X1_41 ),
% 35.44/4.99      theory(equality) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_98507,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,X2_41)))
% 35.44/4.99      | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != X0_41
% 35.44/4.99      | k4_xboole_0(sK3,k4_xboole_0(sK3,X2_41)) != X1_41 ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_210]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_100690,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)))
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),X1_41)
% 35.44/4.99      | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))
% 35.44/4.99      | k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)) != X1_41 ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_98507]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_105720,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)))
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK3)))
% 35.44/4.99      | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))
% 35.44/4.99      | k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)) != k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK3)) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_100690]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_105722,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.44/4.99      | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))
% 35.44/4.99      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_105720]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_9,plain,
% 35.44/4.99      ( r1_tarski(X0,X1)
% 35.44/4.99      | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 35.44/4.99      | ~ r1_xboole_0(X0,X2) ),
% 35.44/4.99      inference(cnf_transformation,[],[f47]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_194,plain,
% 35.44/4.99      ( r1_tarski(X0_41,X1_41)
% 35.44/4.99      | ~ r1_tarski(X0_41,k2_xboole_0(X1_41,X2_41))
% 35.44/4.99      | ~ r1_xboole_0(X0_41,X2_41) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_9]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_849,plain,
% 35.44/4.99      ( r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),X0_41)
% 35.44/4.99      | ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k2_xboole_0(X0_41,X1_41))
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),X1_41) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_194]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_60974,plain,
% 35.44/4.99      ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k2_xboole_0(sK2,sK4))
% 35.44/4.99      | r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK2)
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK4) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_849]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_2,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 35.44/4.99      inference(cnf_transformation,[],[f38]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_201,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0_41,X1_41) | r1_xboole_0(X1_41,X0_41) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_2]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_2027,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0_41,k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41)))
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41)),X0_41) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_201]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_35665,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0_41,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))))
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),X0_41) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_2027]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_35667,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),sK2)
% 35.44/4.99      | ~ r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_35665]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_654,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,sK4) | ~ r1_xboole_0(sK4,X0_41) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_201]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_879,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),sK4)
% 35.44/4.99      | ~ r1_xboole_0(sK4,k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41))) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_654]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_3969,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)),sK4)
% 35.44/4.99      | ~ r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41))) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_879]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_24059,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),sK4)
% 35.44/4.99      | ~ r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_3969]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_4002,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,k4_xboole_0(sK3,k4_xboole_0(sK3,X1_41)))
% 35.44/4.99      | ~ r1_xboole_0(X0_41,sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_193]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_13735,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))))
% 35.44/4.99      | ~ r1_xboole_0(X0_41,sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_4002]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_13737,plain,
% 35.44/4.99      ( r1_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))))
% 35.44/4.99      | ~ r1_xboole_0(sK2,sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_13735]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_659,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0_41,X1_41)
% 35.44/4.99      | r1_xboole_0(X2_41,sK4)
% 35.44/4.99      | X2_41 != X0_41
% 35.44/4.99      | sK4 != X1_41 ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_210]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_1041,plain,
% 35.44/4.99      ( ~ r1_xboole_0(X0_41,sK4)
% 35.44/4.99      | r1_xboole_0(X1_41,sK4)
% 35.44/4.99      | X1_41 != X0_41
% 35.44/4.99      | sK4 != sK4 ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_659]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_4322,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,sK4)
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1_41)),sK4)
% 35.44/4.99      | X0_41 != k4_xboole_0(sK3,k4_xboole_0(sK3,X1_41))
% 35.44/4.99      | sK4 != sK4 ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_1041]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_10960,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK4)
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))),sK4)
% 35.44/4.99      | k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4)))
% 35.44/4.99      | sK4 != sK4 ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_4322]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_1,plain,
% 35.44/4.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 35.44/4.99      inference(cnf_transformation,[],[f62]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_202,plain,
% 35.44/4.99      ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_1]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_9616,plain,
% 35.44/4.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_202]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_1661,plain,
% 35.44/4.99      ( ~ r1_xboole_0(sK4,X0_41)
% 35.44/4.99      | r1_xboole_0(sK4,k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41))) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_193]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_3470,plain,
% 35.44/4.99      ( r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)))
% 35.44/4.99      | ~ r1_xboole_0(sK4,sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_1661]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_7928,plain,
% 35.44/4.99      ( r1_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))))
% 35.44/4.99      | ~ r1_xboole_0(sK4,sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_3470]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_519,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 35.44/4.99      | r1_xboole_0(X0_41,k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41))) = iProver_top ),
% 35.44/4.99      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_511,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 35.44/4.99      | r1_xboole_0(X1_41,X0_41) = iProver_top ),
% 35.44/4.99      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_1566,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(X1_41,k4_xboole_0(X1_41,X2_41)),X0_41) = iProver_top ),
% 35.44/4.99      inference(superposition,[status(thm)],[c_519,c_511]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_17,negated_conjecture,
% 35.44/4.99      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 35.44/4.99      inference(cnf_transformation,[],[f69]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_186,negated_conjecture,
% 35.44/4.99      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_17]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_526,plain,
% 35.44/4.99      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 35.44/4.99      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_1562,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 35.44/4.99      | r1_xboole_0(X0_41,k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41))) = iProver_top ),
% 35.44/4.99      inference(superposition,[status(thm)],[c_202,c_519]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_12,plain,
% 35.44/4.99      ( ~ r1_tarski(X0,X1)
% 35.44/4.99      | r1_xboole_0(X0,X2)
% 35.44/4.99      | ~ r1_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 35.44/4.99      inference(cnf_transformation,[],[f67]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_191,plain,
% 35.44/4.99      ( ~ r1_tarski(X0_41,X1_41)
% 35.44/4.99      | r1_xboole_0(X0_41,X2_41)
% 35.44/4.99      | ~ r1_xboole_0(X0_41,k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41))) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_12]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_521,plain,
% 35.44/4.99      ( r1_tarski(X0_41,X1_41) != iProver_top
% 35.44/4.99      | r1_xboole_0(X0_41,X2_41) = iProver_top
% 35.44/4.99      | r1_xboole_0(X0_41,k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41))) != iProver_top ),
% 35.44/4.99      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_3524,plain,
% 35.44/4.99      ( r1_tarski(X0_41,X1_41) != iProver_top
% 35.44/4.99      | r1_xboole_0(X0_41,X1_41) != iProver_top
% 35.44/4.99      | r1_xboole_0(X0_41,X2_41) = iProver_top ),
% 35.44/4.99      inference(superposition,[status(thm)],[c_1562,c_521]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_4405,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_41) = iProver_top
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
% 35.44/4.99      inference(superposition,[status(thm)],[c_526,c_3524]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_4426,plain,
% 35.44/4.99      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK2) != iProver_top
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_41) = iProver_top ),
% 35.44/4.99      inference(superposition,[status(thm)],[c_1566,c_4405]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_16,negated_conjecture,
% 35.44/4.99      ( r2_hidden(sK5,sK4) ),
% 35.44/4.99      inference(cnf_transformation,[],[f56]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_19,plain,
% 35.44/4.99      ( r2_hidden(sK5,sK4) = iProver_top ),
% 35.44/4.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_15,negated_conjecture,
% 35.44/4.99      ( r1_xboole_0(sK4,sK3) ),
% 35.44/4.99      inference(cnf_transformation,[],[f57]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_20,plain,
% 35.44/4.99      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 35.44/4.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_3,plain,
% 35.44/4.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 35.44/4.99      inference(cnf_transformation,[],[f41]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_200,plain,
% 35.44/4.99      ( ~ r2_hidden(X0_42,X0_41)
% 35.44/4.99      | ~ r2_hidden(X0_42,X1_41)
% 35.44/4.99      | ~ r1_xboole_0(X0_41,X1_41) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_3]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_558,plain,
% 35.44/4.99      ( ~ r2_hidden(X0_42,sK3)
% 35.44/4.99      | ~ r2_hidden(X0_42,sK4)
% 35.44/4.99      | ~ r1_xboole_0(sK4,sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_200]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_559,plain,
% 35.44/4.99      ( r2_hidden(X0_42,sK3) != iProver_top
% 35.44/4.99      | r2_hidden(X0_42,sK4) != iProver_top
% 35.44/4.99      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 35.44/4.99      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_561,plain,
% 35.44/4.99      ( r2_hidden(sK5,sK3) != iProver_top
% 35.44/4.99      | r2_hidden(sK5,sK4) != iProver_top
% 35.44/4.99      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_559]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_13,plain,
% 35.44/4.99      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 35.44/4.99      inference(cnf_transformation,[],[f68]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_190,plain,
% 35.44/4.99      ( r2_hidden(X0_42,X0_41)
% 35.44/4.99      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_13]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_708,plain,
% 35.44/4.99      ( r2_hidden(X0_42,sK3)
% 35.44/4.99      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_190]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_709,plain,
% 35.44/4.99      ( r2_hidden(X0_42,sK3) = iProver_top
% 35.44/4.99      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) = iProver_top ),
% 35.44/4.99      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_711,plain,
% 35.44/4.99      ( r2_hidden(sK5,sK3) = iProver_top
% 35.44/4.99      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = iProver_top ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_709]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_1648,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41)),X0_41) = iProver_top ),
% 35.44/4.99      inference(superposition,[status(thm)],[c_1562,c_511]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_4427,plain,
% 35.44/4.99      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_41) = iProver_top ),
% 35.44/4.99      inference(superposition,[status(thm)],[c_1648,c_4405]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_4504,plain,
% 35.44/4.99      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_41) = iProver_top ),
% 35.44/4.99      inference(global_propositional_subsumption,
% 35.44/4.99                [status(thm)],
% 35.44/4.99                [c_4426,c_19,c_20,c_561,c_711,c_4427]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_11,plain,
% 35.44/4.99      ( r1_xboole_0(X0,X1)
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 35.44/4.99      inference(cnf_transformation,[],[f66]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_192,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,X1_41)
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),X1_41) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_11]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_520,plain,
% 35.44/4.99      ( r1_xboole_0(X0_41,X1_41) = iProver_top
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),X1_41) != iProver_top ),
% 35.44/4.99      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_4512,plain,
% 35.44/4.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 35.44/4.99      inference(superposition,[status(thm)],[c_4504,c_520]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_4523,plain,
% 35.44/4.99      ( r1_xboole_0(sK2,sK3) ),
% 35.44/4.99      inference(predicate_to_equality_rev,[status(thm)],[c_4512]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_3457,plain,
% 35.44/4.99      ( k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK2,sK4))) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_202]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_205,plain,( X0_41 = X0_41 ),theory(equality) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_1554,plain,
% 35.44/4.99      ( sK4 = sK4 ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_205]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_8,plain,
% 35.44/4.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 35.44/4.99      inference(cnf_transformation,[],[f45]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_195,plain,
% 35.44/4.99      ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) ),
% 35.44/4.99      inference(subtyping,[status(esa)],[c_8]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_1298,plain,
% 35.44/4.99      ( r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k2_xboole_0(sK2,sK4)) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_195]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_591,plain,
% 35.44/4.99      ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),X0_41)
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,X0_41)))
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_191]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_593,plain,
% 35.44/4.99      ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK2)
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
% 35.44/4.99      | r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_591]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_572,plain,
% 35.44/4.99      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 35.44/4.99      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),k4_xboole_0(k2_xboole_0(sK2,sK4),sK3)),sK3) ),
% 35.44/4.99      inference(instantiation,[status(thm)],[c_192]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(c_14,negated_conjecture,
% 35.44/4.99      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 35.44/4.99      inference(cnf_transformation,[],[f58]) ).
% 35.44/4.99  
% 35.44/4.99  cnf(contradiction,plain,
% 35.44/4.99      ( $false ),
% 35.44/4.99      inference(minisat,
% 35.44/4.99                [status(thm)],
% 35.44/4.99                [c_116188,c_105722,c_60974,c_35667,c_24059,c_13737,
% 35.44/4.99                 c_10960,c_9616,c_7928,c_4523,c_3457,c_1554,c_1298,c_593,
% 35.44/4.99                 c_572,c_14,c_15]) ).
% 35.44/4.99  
% 35.44/4.99  
% 35.44/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.44/4.99  
% 35.44/4.99  ------                               Statistics
% 35.44/4.99  
% 35.44/4.99  ------ General
% 35.44/4.99  
% 35.44/4.99  abstr_ref_over_cycles:                  0
% 35.44/4.99  abstr_ref_under_cycles:                 0
% 35.44/4.99  gc_basic_clause_elim:                   0
% 35.44/4.99  forced_gc_time:                         0
% 35.44/4.99  parsing_time:                           0.011
% 35.44/4.99  unif_index_cands_time:                  0.
% 35.44/4.99  unif_index_add_time:                    0.
% 35.44/4.99  orderings_time:                         0.
% 35.44/4.99  out_proof_time:                         0.015
% 35.44/4.99  total_time:                             4.114
% 35.44/4.99  num_of_symbols:                         46
% 35.44/4.99  num_of_terms:                           137732
% 35.44/4.99  
% 35.44/4.99  ------ Preprocessing
% 35.44/4.99  
% 35.44/4.99  num_of_splits:                          0
% 35.44/4.99  num_of_split_atoms:                     0
% 35.44/4.99  num_of_reused_defs:                     0
% 35.44/4.99  num_eq_ax_congr_red:                    10
% 35.44/4.99  num_of_sem_filtered_clauses:            1
% 35.44/4.99  num_of_subtypes:                        2
% 35.44/4.99  monotx_restored_types:                  0
% 35.44/4.99  sat_num_of_epr_types:                   0
% 35.44/4.99  sat_num_of_non_cyclic_types:            0
% 35.44/4.99  sat_guarded_non_collapsed_types:        0
% 35.44/4.99  num_pure_diseq_elim:                    0
% 35.44/4.99  simp_replaced_by:                       0
% 35.44/4.99  res_preprocessed:                       75
% 35.44/4.99  prep_upred:                             0
% 35.44/4.99  prep_unflattend:                        0
% 35.44/4.99  smt_new_axioms:                         0
% 35.44/4.99  pred_elim_cands:                        3
% 35.44/4.99  pred_elim:                              0
% 35.44/4.99  pred_elim_cl:                           0
% 35.44/4.99  pred_elim_cycles:                       1
% 35.44/4.99  merged_defs:                            0
% 35.44/4.99  merged_defs_ncl:                        0
% 35.44/4.99  bin_hyper_res:                          0
% 35.44/4.99  prep_cycles:                            3
% 35.44/4.99  pred_elim_time:                         0.
% 35.44/4.99  splitting_time:                         0.
% 35.44/4.99  sem_filter_time:                        0.
% 35.44/4.99  monotx_time:                            0.
% 35.44/4.99  subtype_inf_time:                       0.
% 35.44/4.99  
% 35.44/4.99  ------ Problem properties
% 35.44/4.99  
% 35.44/4.99  clauses:                                18
% 35.44/4.99  conjectures:                            4
% 35.44/4.99  epr:                                    4
% 35.44/4.99  horn:                                   14
% 35.44/4.99  ground:                                 4
% 35.44/4.99  unary:                                  7
% 35.44/4.99  binary:                                 8
% 35.44/4.99  lits:                                   32
% 35.44/4.99  lits_eq:                                2
% 35.44/4.99  fd_pure:                                0
% 35.44/4.99  fd_pseudo:                              0
% 35.44/4.99  fd_cond:                                0
% 35.44/4.99  fd_pseudo_cond:                         0
% 35.44/4.99  ac_symbols:                             0
% 35.44/4.99  
% 35.44/4.99  ------ Propositional Solver
% 35.44/4.99  
% 35.44/4.99  prop_solver_calls:                      56
% 35.44/4.99  prop_fast_solver_calls:                 1394
% 35.44/4.99  smt_solver_calls:                       0
% 35.44/4.99  smt_fast_solver_calls:                  0
% 35.44/4.99  prop_num_of_clauses:                    54374
% 35.44/4.99  prop_preprocess_simplified:             56554
% 35.44/4.99  prop_fo_subsumed:                       2
% 35.44/4.99  prop_solver_time:                       0.
% 35.44/4.99  smt_solver_time:                        0.
% 35.44/4.99  smt_fast_solver_time:                   0.
% 35.44/4.99  prop_fast_solver_time:                  0.
% 35.44/4.99  prop_unsat_core_time:                   0.005
% 35.44/4.99  
% 35.44/4.99  ------ QBF
% 35.44/4.99  
% 35.44/4.99  qbf_q_res:                              0
% 35.44/4.99  qbf_num_tautologies:                    0
% 35.44/4.99  qbf_prep_cycles:                        0
% 35.44/4.99  
% 35.44/4.99  ------ BMC1
% 35.44/4.99  
% 35.44/4.99  bmc1_current_bound:                     -1
% 35.44/4.99  bmc1_last_solved_bound:                 -1
% 35.44/4.99  bmc1_unsat_core_size:                   -1
% 35.44/4.99  bmc1_unsat_core_parents_size:           -1
% 35.44/4.99  bmc1_merge_next_fun:                    0
% 35.44/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.44/4.99  
% 35.44/4.99  ------ Instantiation
% 35.44/4.99  
% 35.44/4.99  inst_num_of_clauses:                    1202
% 35.44/4.99  inst_num_in_passive:                    460
% 35.44/4.99  inst_num_in_active:                     3133
% 35.44/4.99  inst_num_in_unprocessed:                236
% 35.44/4.99  inst_num_of_loops:                      3513
% 35.44/4.99  inst_num_of_learning_restarts:          1
% 35.44/4.99  inst_num_moves_active_passive:          378
% 35.44/4.99  inst_lit_activity:                      0
% 35.44/4.99  inst_lit_activity_moves:                1
% 35.44/4.99  inst_num_tautologies:                   0
% 35.44/4.99  inst_num_prop_implied:                  0
% 35.44/4.99  inst_num_existing_simplified:           0
% 35.44/4.99  inst_num_eq_res_simplified:             0
% 35.44/4.99  inst_num_child_elim:                    0
% 35.44/4.99  inst_num_of_dismatching_blockings:      14152
% 35.44/4.99  inst_num_of_non_proper_insts:           11123
% 35.44/4.99  inst_num_of_duplicates:                 0
% 35.44/4.99  inst_inst_num_from_inst_to_res:         0
% 35.44/4.99  inst_dismatching_checking_time:         0.
% 35.44/4.99  
% 35.44/4.99  ------ Resolution
% 35.44/4.99  
% 35.44/4.99  res_num_of_clauses:                     28
% 35.44/4.99  res_num_in_passive:                     28
% 35.44/4.99  res_num_in_active:                      0
% 35.44/4.99  res_num_of_loops:                       78
% 35.44/4.99  res_forward_subset_subsumed:            465
% 35.44/4.99  res_backward_subset_subsumed:           18
% 35.44/4.99  res_forward_subsumed:                   0
% 35.44/4.99  res_backward_subsumed:                  0
% 35.44/4.99  res_forward_subsumption_resolution:     0
% 35.44/4.99  res_backward_subsumption_resolution:    0
% 35.44/4.99  res_clause_to_clause_subsumption:       200164
% 35.44/4.99  res_orphan_elimination:                 0
% 35.44/4.99  res_tautology_del:                      399
% 35.44/4.99  res_num_eq_res_simplified:              0
% 35.44/4.99  res_num_sel_changes:                    0
% 35.44/4.99  res_moves_from_active_to_pass:          0
% 35.44/4.99  
% 35.44/4.99  ------ Superposition
% 35.44/4.99  
% 35.44/4.99  sup_time_total:                         0.
% 35.44/4.99  sup_time_generating:                    0.
% 35.44/4.99  sup_time_sim_full:                      0.
% 35.44/4.99  sup_time_sim_immed:                     0.
% 35.44/4.99  
% 35.44/4.99  sup_num_of_clauses:                     8306
% 35.44/4.99  sup_num_in_active:                      692
% 35.44/4.99  sup_num_in_passive:                     7614
% 35.44/4.99  sup_num_of_loops:                       702
% 35.44/4.99  sup_fw_superposition:                   12979
% 35.44/4.99  sup_bw_superposition:                   13923
% 35.44/4.99  sup_immediate_simplified:               4290
% 35.44/4.99  sup_given_eliminated:                   0
% 35.44/4.99  comparisons_done:                       0
% 35.44/4.99  comparisons_avoided:                    0
% 35.44/4.99  
% 35.44/4.99  ------ Simplifications
% 35.44/4.99  
% 35.44/4.99  
% 35.44/4.99  sim_fw_subset_subsumed:                 293
% 35.44/4.99  sim_bw_subset_subsumed:                 1
% 35.44/4.99  sim_fw_subsumed:                        3005
% 35.44/4.99  sim_bw_subsumed:                        1021
% 35.44/4.99  sim_fw_subsumption_res:                 0
% 35.44/4.99  sim_bw_subsumption_res:                 0
% 35.44/4.99  sim_tautology_del:                      63
% 35.44/4.99  sim_eq_tautology_del:                   0
% 35.44/4.99  sim_eq_res_simp:                        0
% 35.44/4.99  sim_fw_demodulated:                     3
% 35.44/4.99  sim_bw_demodulated:                     0
% 35.44/4.99  sim_light_normalised:                   1
% 35.44/4.99  sim_joinable_taut:                      0
% 35.44/4.99  sim_joinable_simp:                      0
% 35.44/4.99  sim_ac_normalised:                      0
% 35.44/4.99  sim_smt_subsumption:                    0
% 35.44/4.99  
%------------------------------------------------------------------------------
