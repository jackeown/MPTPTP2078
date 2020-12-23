%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:45 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 122 expanded)
%              Number of clauses        :   64 (  69 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  219 ( 279 expanded)
%              Number of equality atoms :  134 ( 166 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f32,plain,(
    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != sK1 ),
    inference(definition_unfolding,[],[f32,f24,f33])).

fof(f31,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_149,plain,
    ( ~ r2_hidden(X0_38,X0_39)
    | ~ r2_hidden(X1_38,X0_39)
    | r1_tarski(k4_enumset1(X1_38,X1_38,X1_38,X1_38,X1_38,X0_38),X0_39) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_16377,plain,
    ( ~ r2_hidden(sK2,X0_39)
    | ~ r2_hidden(sK0,X0_39)
    | r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),X0_39) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_16379,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK0,sK1)
    | r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_16377])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_151,plain,
    ( ~ r1_xboole_0(X0_39,X0_40)
    | k4_xboole_0(X0_39,X0_40) = X0_39 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_594,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0_39,X0_40),X1_40)
    | k4_xboole_0(k4_xboole_0(X0_39,X0_40),X1_40) = k4_xboole_0(X0_39,X0_40) ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_4379,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),X0_40)
    | k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),X0_40) = k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_15914,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
    | k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) = k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_4379])).

cnf(c_161,plain,
    ( ~ r1_xboole_0(X0_39,X0_40)
    | r1_xboole_0(X1_39,X0_40)
    | X1_39 != X0_39 ),
    theory(equality)).

cnf(c_437,plain,
    ( r1_xboole_0(X0_39,X0_40)
    | ~ r1_xboole_0(k4_xboole_0(X1_39,k3_xboole_0(X1_39,X0_40)),X0_40)
    | X0_39 != k4_xboole_0(X1_39,k3_xboole_0(X1_39,X0_40)) ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_485,plain,
    ( r1_xboole_0(k4_xboole_0(X0_39,X0_40),X1_40)
    | ~ r1_xboole_0(k4_xboole_0(X1_39,k3_xboole_0(X1_39,X1_40)),X1_40)
    | k4_xboole_0(X0_39,X0_40) != k4_xboole_0(X1_39,k3_xboole_0(X1_39,X1_40)) ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_2448,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)),X0_40)
    | r1_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),X0_40)
    | k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_9641,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
    | ~ r1_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
    | k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_2448])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_153,plain,
    ( ~ r1_tarski(X0_40,X0_39)
    | k5_xboole_0(X0_40,k4_xboole_0(k4_xboole_0(X0_39,X0_40),X0_40)) = X0_39 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_442,plain,
    ( ~ r1_tarski(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),X0_39)
    | k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) = X0_39 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_5859,plain,
    ( ~ r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),X0_39)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = X0_39 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_5861,plain,
    ( ~ r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1 ),
    inference(instantiation,[status(thm)],[c_5859])).

cnf(c_157,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_454,plain,
    ( X0_39 != X1_39
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != X1_39
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = X0_39 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_517,plain,
    ( X0_39 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = X0_39
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_683,plain,
    ( k5_xboole_0(X0_40,X0_39) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(X0_40,X0_39)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1688,plain,
    ( k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_5806,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_5808,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_5806])).

cnf(c_159,plain,
    ( X0_40 != X1_40
    | X0_39 != X1_39
    | k5_xboole_0(X0_40,X0_39) = k5_xboole_0(X1_40,X1_39) ),
    theory(equality)).

cnf(c_684,plain,
    ( X0_40 != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
    | X0_39 != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
    | k5_xboole_0(X0_40,X0_39) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_876,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
    | X0_39 != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),X0_39) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_1461,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(X0_39,X0_40)) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k4_xboole_0(X0_39,X0_40) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_4105,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_5805,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_4105])).

cnf(c_5807,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_5805])).

cnf(c_3,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_150,plain,
    ( r1_xboole_0(k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)),X0_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4669,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_567,plain,
    ( k5_xboole_0(X0_40,X0_39) != X1_39
    | sK1 != X1_39
    | sK1 = k5_xboole_0(X0_40,X0_39) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_698,plain,
    ( k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) != X0_39
    | sK1 != X0_39
    | sK1 = k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_4062,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != X0_39
    | sK1 != X0_39
    | sK1 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_4064,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != sK1
    | sK1 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4062])).

cnf(c_427,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != X0_39
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
    | sK1 != X0_39 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_455,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(X0_40,X0_39)
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
    | sK1 != k5_xboole_0(X0_40,X0_39) ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_958,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
    | sK1 != k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_2147,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
    | sK1 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_2149,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
    | sK1 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_152,plain,
    ( k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)) = k4_xboole_0(X0_39,X0_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1458,plain,
    ( k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_483,plain,
    ( X0_39 != X1_39
    | X0_39 = k4_xboole_0(X2_39,k3_xboole_0(X2_39,X0_40))
    | k4_xboole_0(X2_39,k3_xboole_0(X2_39,X0_40)) != X1_39 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_505,plain,
    ( X0_39 != k4_xboole_0(X1_39,X0_40)
    | X0_39 = k4_xboole_0(X1_39,k3_xboole_0(X1_39,X0_40))
    | k4_xboole_0(X1_39,k3_xboole_0(X1_39,X0_40)) != k4_xboole_0(X1_39,X0_40) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_604,plain,
    ( k4_xboole_0(X0_39,X0_40) != k4_xboole_0(X0_39,X0_40)
    | k4_xboole_0(X0_39,X0_40) = k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40))
    | k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)) != k4_xboole_0(X0_39,X0_40) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_1129,plain,
    ( k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
    | k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) = k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_155,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_605,plain,
    ( k4_xboole_0(X0_39,X0_40) = k4_xboole_0(X0_39,X0_40) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_940,plain,
    ( k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) = k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_156,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_570,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_453,plain,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_7,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != sK1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_146,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != sK1 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_169,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16379,c_15914,c_9641,c_5861,c_5808,c_5807,c_4669,c_4064,c_2149,c_1458,c_1129,c_940,c_570,c_453,c_146,c_169,c_8,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:12:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.09/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/0.99  
% 4.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.09/0.99  
% 4.09/0.99  ------  iProver source info
% 4.09/0.99  
% 4.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.09/0.99  git: non_committed_changes: false
% 4.09/0.99  git: last_make_outside_of_git: false
% 4.09/0.99  
% 4.09/0.99  ------ 
% 4.09/0.99  ------ Parsing...
% 4.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.09/0.99  
% 4.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.09/0.99  
% 4.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.09/0.99  
% 4.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.09/0.99  ------ Proving...
% 4.09/0.99  ------ Problem Properties 
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  clauses                                 10
% 4.09/0.99  conjectures                             3
% 4.09/0.99  EPR                                     2
% 4.09/0.99  Horn                                    10
% 4.09/0.99  unary                                   5
% 4.09/0.99  binary                                  4
% 4.09/0.99  lits                                    16
% 4.09/0.99  lits eq                                 4
% 4.09/0.99  fd_pure                                 0
% 4.09/0.99  fd_pseudo                               0
% 4.09/0.99  fd_cond                                 0
% 4.09/0.99  fd_pseudo_cond                          0
% 4.09/0.99  AC symbols                              0
% 4.09/0.99  
% 4.09/0.99  ------ Input Options Time Limit: Unbounded
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  ------ 
% 4.09/0.99  Current options:
% 4.09/0.99  ------ 
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  ------ Proving...
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  % SZS status Theorem for theBenchmark.p
% 4.09/0.99  
% 4.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.09/0.99  
% 4.09/0.99  fof(f8,axiom,(
% 4.09/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 4.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f16,plain,(
% 4.09/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 4.09/0.99    inference(nnf_transformation,[],[f8])).
% 4.09/0.99  
% 4.09/0.99  fof(f17,plain,(
% 4.09/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 4.09/0.99    inference(flattening,[],[f16])).
% 4.09/0.99  
% 4.09/0.99  fof(f29,plain,(
% 4.09/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f17])).
% 4.09/0.99  
% 4.09/0.99  fof(f7,axiom,(
% 4.09/0.99    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 4.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f26,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f7])).
% 4.09/0.99  
% 4.09/0.99  fof(f6,axiom,(
% 4.09/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f25,plain,(
% 4.09/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f6])).
% 4.09/0.99  
% 4.09/0.99  fof(f33,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.09/0.99    inference(definition_unfolding,[],[f26,f25])).
% 4.09/0.99  
% 4.09/0.99  fof(f35,plain,(
% 4.09/0.99    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 4.09/0.99    inference(definition_unfolding,[],[f29,f33])).
% 4.09/0.99  
% 4.09/0.99  fof(f3,axiom,(
% 4.09/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 4.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f11,plain,(
% 4.09/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 4.09/0.99    inference(unused_predicate_definition_removal,[],[f3])).
% 4.09/0.99  
% 4.09/0.99  fof(f13,plain,(
% 4.09/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 4.09/0.99    inference(ennf_transformation,[],[f11])).
% 4.09/0.99  
% 4.09/0.99  fof(f22,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f13])).
% 4.09/0.99  
% 4.09/0.99  fof(f1,axiom,(
% 4.09/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 4.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f12,plain,(
% 4.09/0.99    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 4.09/0.99    inference(ennf_transformation,[],[f1])).
% 4.09/0.99  
% 4.09/0.99  fof(f20,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f12])).
% 4.09/0.99  
% 4.09/0.99  fof(f5,axiom,(
% 4.09/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f24,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.09/0.99    inference(cnf_transformation,[],[f5])).
% 4.09/0.99  
% 4.09/0.99  fof(f34,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 4.09/0.99    inference(definition_unfolding,[],[f20,f24])).
% 4.09/0.99  
% 4.09/0.99  fof(f4,axiom,(
% 4.09/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 4.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f23,plain,(
% 4.09/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 4.09/0.99    inference(cnf_transformation,[],[f4])).
% 4.09/0.99  
% 4.09/0.99  fof(f2,axiom,(
% 4.09/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f21,plain,(
% 4.09/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.09/0.99    inference(cnf_transformation,[],[f2])).
% 4.09/0.99  
% 4.09/0.99  fof(f9,conjecture,(
% 4.09/0.99    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 4.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/0.99  
% 4.09/0.99  fof(f10,negated_conjecture,(
% 4.09/0.99    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 4.09/0.99    inference(negated_conjecture,[],[f9])).
% 4.09/0.99  
% 4.09/0.99  fof(f14,plain,(
% 4.09/0.99    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 4.09/0.99    inference(ennf_transformation,[],[f10])).
% 4.09/0.99  
% 4.09/0.99  fof(f15,plain,(
% 4.09/0.99    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 4.09/0.99    inference(flattening,[],[f14])).
% 4.09/0.99  
% 4.09/0.99  fof(f18,plain,(
% 4.09/0.99    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 4.09/0.99    introduced(choice_axiom,[])).
% 4.09/0.99  
% 4.09/0.99  fof(f19,plain,(
% 4.09/0.99    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 4.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 4.09/0.99  
% 4.09/0.99  fof(f32,plain,(
% 4.09/0.99    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1),
% 4.09/0.99    inference(cnf_transformation,[],[f19])).
% 4.09/0.99  
% 4.09/0.99  fof(f38,plain,(
% 4.09/0.99    k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != sK1),
% 4.09/0.99    inference(definition_unfolding,[],[f32,f24,f33])).
% 4.09/0.99  
% 4.09/0.99  fof(f31,plain,(
% 4.09/0.99    r2_hidden(sK2,sK1)),
% 4.09/0.99    inference(cnf_transformation,[],[f19])).
% 4.09/0.99  
% 4.09/0.99  fof(f30,plain,(
% 4.09/0.99    r2_hidden(sK0,sK1)),
% 4.09/0.99    inference(cnf_transformation,[],[f19])).
% 4.09/0.99  
% 4.09/0.99  cnf(c_4,plain,
% 4.09/0.99      ( ~ r2_hidden(X0,X1)
% 4.09/0.99      | ~ r2_hidden(X2,X1)
% 4.09/0.99      | r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X0),X1) ),
% 4.09/0.99      inference(cnf_transformation,[],[f35]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_149,plain,
% 4.09/0.99      ( ~ r2_hidden(X0_38,X0_39)
% 4.09/0.99      | ~ r2_hidden(X1_38,X0_39)
% 4.09/0.99      | r1_tarski(k4_enumset1(X1_38,X1_38,X1_38,X1_38,X1_38,X0_38),X0_39) ),
% 4.09/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_16377,plain,
% 4.09/0.99      ( ~ r2_hidden(sK2,X0_39)
% 4.09/0.99      | ~ r2_hidden(sK0,X0_39)
% 4.09/0.99      | r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),X0_39) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_149]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_16379,plain,
% 4.09/0.99      ( ~ r2_hidden(sK2,sK1)
% 4.09/0.99      | ~ r2_hidden(sK0,sK1)
% 4.09/0.99      | r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_16377]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2,plain,
% 4.09/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 4.09/0.99      inference(cnf_transformation,[],[f22]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_151,plain,
% 4.09/0.99      ( ~ r1_xboole_0(X0_39,X0_40) | k4_xboole_0(X0_39,X0_40) = X0_39 ),
% 4.09/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_594,plain,
% 4.09/0.99      ( ~ r1_xboole_0(k4_xboole_0(X0_39,X0_40),X1_40)
% 4.09/0.99      | k4_xboole_0(k4_xboole_0(X0_39,X0_40),X1_40) = k4_xboole_0(X0_39,X0_40) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_151]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_4379,plain,
% 4.09/0.99      ( ~ r1_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),X0_40)
% 4.09/0.99      | k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),X0_40) = k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_594]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_15914,plain,
% 4.09/0.99      ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
% 4.09/0.99      | k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) = k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_4379]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_161,plain,
% 4.09/0.99      ( ~ r1_xboole_0(X0_39,X0_40)
% 4.09/0.99      | r1_xboole_0(X1_39,X0_40)
% 4.09/0.99      | X1_39 != X0_39 ),
% 4.09/0.99      theory(equality) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_437,plain,
% 4.09/0.99      ( r1_xboole_0(X0_39,X0_40)
% 4.09/0.99      | ~ r1_xboole_0(k4_xboole_0(X1_39,k3_xboole_0(X1_39,X0_40)),X0_40)
% 4.09/0.99      | X0_39 != k4_xboole_0(X1_39,k3_xboole_0(X1_39,X0_40)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_161]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_485,plain,
% 4.09/0.99      ( r1_xboole_0(k4_xboole_0(X0_39,X0_40),X1_40)
% 4.09/0.99      | ~ r1_xboole_0(k4_xboole_0(X1_39,k3_xboole_0(X1_39,X1_40)),X1_40)
% 4.09/0.99      | k4_xboole_0(X0_39,X0_40) != k4_xboole_0(X1_39,k3_xboole_0(X1_39,X1_40)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_437]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2448,plain,
% 4.09/0.99      ( ~ r1_xboole_0(k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)),X0_40)
% 4.09/0.99      | r1_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),X0_40)
% 4.09/0.99      | k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_485]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_9641,plain,
% 4.09/0.99      ( r1_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
% 4.09/0.99      | ~ r1_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
% 4.09/0.99      | k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_2448]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_0,plain,
% 4.09/0.99      ( ~ r1_tarski(X0,X1)
% 4.09/0.99      | k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
% 4.09/0.99      inference(cnf_transformation,[],[f34]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_153,plain,
% 4.09/0.99      ( ~ r1_tarski(X0_40,X0_39)
% 4.09/0.99      | k5_xboole_0(X0_40,k4_xboole_0(k4_xboole_0(X0_39,X0_40),X0_40)) = X0_39 ),
% 4.09/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_442,plain,
% 4.09/0.99      ( ~ r1_tarski(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),X0_39)
% 4.09/0.99      | k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) = X0_39 ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_153]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_5859,plain,
% 4.09/0.99      ( ~ r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),X0_39)
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = X0_39 ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_442]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_5861,plain,
% 4.09/0.99      ( ~ r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1 ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_5859]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_157,plain,
% 4.09/0.99      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 4.09/0.99      theory(equality) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_454,plain,
% 4.09/0.99      ( X0_39 != X1_39
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != X1_39
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = X0_39 ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_157]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_517,plain,
% 4.09/0.99      ( X0_39 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = X0_39
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_454]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_683,plain,
% 4.09/0.99      ( k5_xboole_0(X0_40,X0_39) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(X0_40,X0_39)
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_517]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_1688,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_683]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_5806,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_1688]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_5808,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_5806]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_159,plain,
% 4.09/0.99      ( X0_40 != X1_40
% 4.09/0.99      | X0_39 != X1_39
% 4.09/0.99      | k5_xboole_0(X0_40,X0_39) = k5_xboole_0(X1_40,X1_39) ),
% 4.09/0.99      theory(equality) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_684,plain,
% 4.09/0.99      ( X0_40 != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
% 4.09/0.99      | X0_39 != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
% 4.09/0.99      | k5_xboole_0(X0_40,X0_39) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_159]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_876,plain,
% 4.09/0.99      ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
% 4.09/0.99      | X0_39 != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),X0_39) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_684]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_1461,plain,
% 4.09/0.99      ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(X0_39,X0_40)) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k4_xboole_0(X0_39,X0_40) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_876]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_4105,plain,
% 4.09/0.99      ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_1461]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_5805,plain,
% 4.09/0.99      ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_4105]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_5807,plain,
% 4.09/0.99      ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_5805]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_3,plain,
% 4.09/0.99      ( r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 4.09/0.99      inference(cnf_transformation,[],[f23]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_150,plain,
% 4.09/0.99      ( r1_xboole_0(k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)),X0_40) ),
% 4.09/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_4669,plain,
% 4.09/0.99      ( r1_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_150]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_567,plain,
% 4.09/0.99      ( k5_xboole_0(X0_40,X0_39) != X1_39
% 4.09/0.99      | sK1 != X1_39
% 4.09/0.99      | sK1 = k5_xboole_0(X0_40,X0_39) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_157]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_698,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) != X0_39
% 4.09/0.99      | sK1 != X0_39
% 4.09/0.99      | sK1 = k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_567]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_4062,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != X0_39
% 4.09/0.99      | sK1 != X0_39
% 4.09/0.99      | sK1 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_698]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_4064,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != sK1
% 4.09/0.99      | sK1 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | sK1 != sK1 ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_4062]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_427,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != X0_39
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
% 4.09/0.99      | sK1 != X0_39 ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_157]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_455,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(X0_40,X0_39)
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
% 4.09/0.99      | sK1 != k5_xboole_0(X0_40,X0_39) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_427]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_958,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
% 4.09/0.99      | sK1 != k5_xboole_0(k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38)),k4_enumset1(X0_38,X0_38,X0_38,X0_38,X0_38,X1_38))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_455]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2147,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
% 4.09/0.99      | sK1 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(X0_39,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_958]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_2149,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = sK1
% 4.09/0.99      | sK1 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_2147]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_1,plain,
% 4.09/0.99      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 4.09/0.99      inference(cnf_transformation,[],[f21]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_152,plain,
% 4.09/0.99      ( k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)) = k4_xboole_0(X0_39,X0_40) ),
% 4.09/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_1458,plain,
% 4.09/0.99      ( k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_152]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_483,plain,
% 4.09/0.99      ( X0_39 != X1_39
% 4.09/0.99      | X0_39 = k4_xboole_0(X2_39,k3_xboole_0(X2_39,X0_40))
% 4.09/0.99      | k4_xboole_0(X2_39,k3_xboole_0(X2_39,X0_40)) != X1_39 ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_157]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_505,plain,
% 4.09/0.99      ( X0_39 != k4_xboole_0(X1_39,X0_40)
% 4.09/0.99      | X0_39 = k4_xboole_0(X1_39,k3_xboole_0(X1_39,X0_40))
% 4.09/0.99      | k4_xboole_0(X1_39,k3_xboole_0(X1_39,X0_40)) != k4_xboole_0(X1_39,X0_40) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_483]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_604,plain,
% 4.09/0.99      ( k4_xboole_0(X0_39,X0_40) != k4_xboole_0(X0_39,X0_40)
% 4.09/0.99      | k4_xboole_0(X0_39,X0_40) = k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40))
% 4.09/0.99      | k4_xboole_0(X0_39,k3_xboole_0(X0_39,X0_40)) != k4_xboole_0(X0_39,X0_40) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_505]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_1129,plain,
% 4.09/0.99      ( k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))
% 4.09/0.99      | k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) = k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
% 4.09/0.99      | k4_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_604]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_155,plain,( X0_39 = X0_39 ),theory(equality) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_605,plain,
% 4.09/0.99      ( k4_xboole_0(X0_39,X0_40) = k4_xboole_0(X0_39,X0_40) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_155]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_940,plain,
% 4.09/0.99      ( k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) = k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_605]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_156,plain,( X0_40 = X0_40 ),theory(equality) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_570,plain,
% 4.09/0.99      ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_156]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_453,plain,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_155]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_7,negated_conjecture,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != sK1 ),
% 4.09/0.99      inference(cnf_transformation,[],[f38]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_146,negated_conjecture,
% 4.09/0.99      ( k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) != sK1 ),
% 4.09/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_169,plain,
% 4.09/0.99      ( sK1 = sK1 ),
% 4.09/0.99      inference(instantiation,[status(thm)],[c_155]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_8,negated_conjecture,
% 4.09/0.99      ( r2_hidden(sK2,sK1) ),
% 4.09/0.99      inference(cnf_transformation,[],[f31]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(c_9,negated_conjecture,
% 4.09/0.99      ( r2_hidden(sK0,sK1) ),
% 4.09/0.99      inference(cnf_transformation,[],[f30]) ).
% 4.09/0.99  
% 4.09/0.99  cnf(contradiction,plain,
% 4.09/0.99      ( $false ),
% 4.09/0.99      inference(minisat,
% 4.09/0.99                [status(thm)],
% 4.09/0.99                [c_16379,c_15914,c_9641,c_5861,c_5808,c_5807,c_4669,
% 4.09/0.99                 c_4064,c_2149,c_1458,c_1129,c_940,c_570,c_453,c_146,
% 4.09/0.99                 c_169,c_8,c_9]) ).
% 4.09/0.99  
% 4.09/0.99  
% 4.09/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.09/0.99  
% 4.09/0.99  ------                               Statistics
% 4.09/0.99  
% 4.09/0.99  ------ Selected
% 4.09/0.99  
% 4.09/0.99  total_time:                             0.495
% 4.09/0.99  
%------------------------------------------------------------------------------
