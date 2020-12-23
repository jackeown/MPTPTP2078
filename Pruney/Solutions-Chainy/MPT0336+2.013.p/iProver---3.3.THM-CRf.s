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
% DateTime   : Thu Dec  3 11:38:36 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 272 expanded)
%              Number of clauses        :   71 ( 100 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  246 ( 604 expanded)
%              Number of equality atoms :   95 ( 195 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).

fof(f44,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f40,f48,f48])).

fof(f43,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f46,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_201,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_202,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_494,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_498,plain,
    ( ~ r1_tarski(X0_39,k2_enumset1(X0_40,X0_40,X0_40,X0_40))
    | k2_enumset1(X0_40,X0_40,X0_40,X0_40) = X0_39
    | k1_xboole_0 = X0_39 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_515,plain,
    ( ~ r1_xboole_0(X0_39,X1_39)
    | r1_xboole_0(X2_39,X3_39)
    | X2_39 != X0_39
    | X3_39 != X1_39 ),
    theory(equality)).

cnf(c_511,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_1349,plain,
    ( ~ r1_xboole_0(X0_39,X1_39)
    | r1_xboole_0(X2_39,X1_39)
    | X2_39 != X0_39 ),
    inference(resolution,[status(thm)],[c_515,c_511])).

cnf(c_2282,plain,
    ( ~ r1_tarski(X0_39,k2_enumset1(X0_40,X0_40,X0_40,X0_40))
    | ~ r1_xboole_0(X0_39,X1_39)
    | r1_xboole_0(k2_enumset1(X0_40,X0_40,X0_40,X0_40),X1_39)
    | k1_xboole_0 = X0_39 ),
    inference(resolution,[status(thm)],[c_498,c_1349])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_495,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_11065,plain,
    ( r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0_39)
    | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),X0_39)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_2282,c_495])).

cnf(c_11583,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_494,c_11065])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_522,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_505,plain,
    ( ~ r1_xboole_0(X0_39,X1_39)
    | r1_xboole_0(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_962,plain,
    ( r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_507,plain,
    ( r1_xboole_0(X0_39,X1_39)
    | k3_xboole_0(X0_39,X1_39) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1053,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_512,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_1147,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != X0_39
    | k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != X0_39 ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_1605,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k3_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_501,plain,
    ( ~ r1_xboole_0(X0_39,X1_39)
    | k3_xboole_0(X0_39,k2_xboole_0(X1_39,X2_39)) = k3_xboole_0(X0_39,X2_39) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1606,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_496,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_869,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_860,plain,
    ( r1_xboole_0(X0_39,X1_39) != iProver_top
    | r1_xboole_0(X1_39,X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_1539,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_860])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_506,plain,
    ( ~ r1_xboole_0(X0_39,X1_39)
    | k3_xboole_0(X0_39,X1_39) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_859,plain,
    ( k3_xboole_0(X0_39,X1_39) = k1_xboole_0
    | r1_xboole_0(X0_39,X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_1686,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1539,c_859])).

cnf(c_1096,plain,
    ( X0_39 != X1_39
    | X0_39 = k3_xboole_0(X2_39,X3_39)
    | k3_xboole_0(X2_39,X3_39) != X1_39 ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_2327,plain,
    ( k3_xboole_0(sK1,sK2) != X0_39
    | k1_xboole_0 != X0_39
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1096])).

cnf(c_2328,plain,
    ( k3_xboole_0(sK1,sK2) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2327])).

cnf(c_1657,plain,
    ( ~ r1_xboole_0(X0_39,sK1)
    | r1_xboole_0(sK1,X0_39) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_2811,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_870,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_867,plain,
    ( k2_enumset1(X0_40,X0_40,X0_40,X0_40) = X0_39
    | k1_xboole_0 = X0_39
    | r1_tarski(X0_39,k2_enumset1(X0_40,X0_40,X0_40,X0_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_3286,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k3_xboole_0(sK0,sK1)
    | k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_870,c_867])).

cnf(c_871,plain,
    ( r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_3803,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3286,c_871])).

cnf(c_3827,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3803])).

cnf(c_5315,plain,
    ( r1_xboole_0(sK0,sK1)
    | k3_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_11654,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11583,c_13,c_522,c_962,c_1053,c_1605,c_1606,c_1686,c_2328,c_2811,c_3827,c_5315])).

cnf(c_1470,plain,
    ( ~ r1_xboole_0(X0_39,X1_39)
    | r1_xboole_0(k3_xboole_0(X0_39,X1_39),X2_39)
    | ~ r1_xboole_0(k1_xboole_0,X2_39) ),
    inference(resolution,[status(thm)],[c_1349,c_506])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_503,plain,
    ( r1_xboole_0(X0_39,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1046,plain,
    ( r1_xboole_0(k1_xboole_0,X0_39) ),
    inference(resolution,[status(thm)],[c_505,c_503])).

cnf(c_2589,plain,
    ( ~ r1_xboole_0(X0_39,X1_39)
    | r1_xboole_0(k3_xboole_0(X0_39,X1_39),X2_39) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1470,c_1046])).

cnf(c_2747,plain,
    ( ~ r1_xboole_0(X0_39,X1_39)
    | r1_xboole_0(X2_39,k3_xboole_0(X0_39,X1_39)) ),
    inference(resolution,[status(thm)],[c_2589,c_505])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_502,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_xboole_0(X0_39,X2_39)
    | ~ r1_xboole_0(X0_39,k3_xboole_0(X2_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2765,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_xboole_0(X2_39,X1_39)
    | r1_xboole_0(X0_39,X2_39) ),
    inference(resolution,[status(thm)],[c_2747,c_502])).

cnf(c_2990,plain,
    ( ~ r1_tarski(X0_39,sK1)
    | r1_xboole_0(X0_39,sK2) ),
    inference(resolution,[status(thm)],[c_2765,c_496])).

cnf(c_516,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(X2_39,X3_39)
    | X2_39 != X0_39
    | X3_39 != X1_39 ),
    theory(equality)).

cnf(c_1449,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(X2_39,X1_39)
    | X2_39 != X0_39 ),
    inference(resolution,[status(thm)],[c_516,c_511])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_508,plain,
    ( k3_xboole_0(X0_39,X1_39) = k3_xboole_0(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1702,plain,
    ( ~ r1_tarski(k3_xboole_0(X0_39,X1_39),X2_39)
    | r1_tarski(k3_xboole_0(X1_39,X0_39),X2_39) ),
    inference(resolution,[status(thm)],[c_1449,c_508])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_504,plain,
    ( r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1717,plain,
    ( r1_tarski(k3_xboole_0(X0_39,X1_39),X1_39) ),
    inference(resolution,[status(thm)],[c_1702,c_504])).

cnf(c_3178,plain,
    ( r1_xboole_0(k3_xboole_0(X0_39,sK1),sK2) ),
    inference(resolution,[status(thm)],[c_2990,c_1717])).

cnf(c_11659,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11654,c_3178])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 3.39/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.01  
% 3.39/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/1.01  
% 3.39/1.01  ------  iProver source info
% 3.39/1.01  
% 3.39/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.39/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/1.01  git: non_committed_changes: false
% 3.39/1.01  git: last_make_outside_of_git: false
% 3.39/1.01  
% 3.39/1.01  ------ 
% 3.39/1.01  ------ Parsing...
% 3.39/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.01  
% 3.39/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.39/1.01  
% 3.39/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.01  
% 3.39/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.01  ------ Proving...
% 3.39/1.01  ------ Problem Properties 
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  clauses                                 16
% 3.39/1.01  conjectures                             3
% 3.39/1.01  EPR                                     3
% 3.39/1.01  Horn                                    15
% 3.39/1.01  unary                                   10
% 3.39/1.01  binary                                  4
% 3.39/1.01  lits                                    24
% 3.39/1.01  lits eq                                 7
% 3.39/1.01  fd_pure                                 0
% 3.39/1.01  fd_pseudo                               0
% 3.39/1.01  fd_cond                                 0
% 3.39/1.01  fd_pseudo_cond                          1
% 3.39/1.01  AC symbols                              0
% 3.39/1.01  
% 3.39/1.01  ------ Input Options Time Limit: Unbounded
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  ------ 
% 3.39/1.01  Current options:
% 3.39/1.01  ------ 
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  ------ Proving...
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  % SZS status Theorem for theBenchmark.p
% 3.39/1.01  
% 3.39/1.01   Resolution empty clause
% 3.39/1.01  
% 3.39/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.01  
% 3.39/1.01  fof(f12,axiom,(
% 3.39/1.01    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f19,plain,(
% 3.39/1.01    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.39/1.01    inference(ennf_transformation,[],[f12])).
% 3.39/1.01  
% 3.39/1.01  fof(f39,plain,(
% 3.39/1.01    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f19])).
% 3.39/1.01  
% 3.39/1.01  fof(f9,axiom,(
% 3.39/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f36,plain,(
% 3.39/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f9])).
% 3.39/1.01  
% 3.39/1.01  fof(f10,axiom,(
% 3.39/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f37,plain,(
% 3.39/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f10])).
% 3.39/1.01  
% 3.39/1.01  fof(f11,axiom,(
% 3.39/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f38,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f11])).
% 3.39/1.01  
% 3.39/1.01  fof(f47,plain,(
% 3.39/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.39/1.01    inference(definition_unfolding,[],[f37,f38])).
% 3.39/1.01  
% 3.39/1.01  fof(f48,plain,(
% 3.39/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.39/1.01    inference(definition_unfolding,[],[f36,f47])).
% 3.39/1.01  
% 3.39/1.01  fof(f49,plain,(
% 3.39/1.01    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 3.39/1.01    inference(definition_unfolding,[],[f39,f48])).
% 3.39/1.01  
% 3.39/1.01  fof(f14,conjecture,(
% 3.39/1.01    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f15,negated_conjecture,(
% 3.39/1.01    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.39/1.01    inference(negated_conjecture,[],[f14])).
% 3.39/1.01  
% 3.39/1.01  fof(f20,plain,(
% 3.39/1.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 3.39/1.01    inference(ennf_transformation,[],[f15])).
% 3.39/1.01  
% 3.39/1.01  fof(f21,plain,(
% 3.39/1.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 3.39/1.01    inference(flattening,[],[f20])).
% 3.39/1.01  
% 3.39/1.01  fof(f25,plain,(
% 3.39/1.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 3.39/1.01    introduced(choice_axiom,[])).
% 3.39/1.01  
% 3.39/1.01  fof(f26,plain,(
% 3.39/1.01    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 3.39/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).
% 3.39/1.01  
% 3.39/1.01  fof(f44,plain,(
% 3.39/1.01    r2_hidden(sK3,sK2)),
% 3.39/1.01    inference(cnf_transformation,[],[f26])).
% 3.39/1.01  
% 3.39/1.01  fof(f13,axiom,(
% 3.39/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f23,plain,(
% 3.39/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.39/1.01    inference(nnf_transformation,[],[f13])).
% 3.39/1.01  
% 3.39/1.01  fof(f24,plain,(
% 3.39/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.39/1.01    inference(flattening,[],[f23])).
% 3.39/1.01  
% 3.39/1.01  fof(f40,plain,(
% 3.39/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.39/1.01    inference(cnf_transformation,[],[f24])).
% 3.39/1.01  
% 3.39/1.01  fof(f52,plain,(
% 3.39/1.01    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.39/1.01    inference(definition_unfolding,[],[f40,f48,f48])).
% 3.39/1.01  
% 3.39/1.01  fof(f43,plain,(
% 3.39/1.01    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 3.39/1.01    inference(cnf_transformation,[],[f26])).
% 3.39/1.01  
% 3.39/1.01  fof(f53,plain,(
% 3.39/1.01    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 3.39/1.01    inference(definition_unfolding,[],[f43,f48])).
% 3.39/1.01  
% 3.39/1.01  fof(f46,plain,(
% 3.39/1.01    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 3.39/1.01    inference(cnf_transformation,[],[f26])).
% 3.39/1.01  
% 3.39/1.01  fof(f4,axiom,(
% 3.39/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f16,plain,(
% 3.39/1.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.39/1.01    inference(ennf_transformation,[],[f4])).
% 3.39/1.01  
% 3.39/1.01  fof(f31,plain,(
% 3.39/1.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f16])).
% 3.39/1.01  
% 3.39/1.01  fof(f3,axiom,(
% 3.39/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f22,plain,(
% 3.39/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.39/1.01    inference(nnf_transformation,[],[f3])).
% 3.39/1.01  
% 3.39/1.01  fof(f30,plain,(
% 3.39/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.39/1.01    inference(cnf_transformation,[],[f22])).
% 3.39/1.01  
% 3.39/1.01  fof(f8,axiom,(
% 3.39/1.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f18,plain,(
% 3.39/1.01    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 3.39/1.01    inference(ennf_transformation,[],[f8])).
% 3.39/1.01  
% 3.39/1.01  fof(f35,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f18])).
% 3.39/1.01  
% 3.39/1.01  fof(f45,plain,(
% 3.39/1.01    r1_xboole_0(sK2,sK1)),
% 3.39/1.01    inference(cnf_transformation,[],[f26])).
% 3.39/1.01  
% 3.39/1.01  fof(f29,plain,(
% 3.39/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f22])).
% 3.39/1.01  
% 3.39/1.01  fof(f6,axiom,(
% 3.39/1.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f33,plain,(
% 3.39/1.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f6])).
% 3.39/1.01  
% 3.39/1.01  fof(f7,axiom,(
% 3.39/1.01    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f17,plain,(
% 3.39/1.01    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 3.39/1.01    inference(ennf_transformation,[],[f7])).
% 3.39/1.01  
% 3.39/1.01  fof(f34,plain,(
% 3.39/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f17])).
% 3.39/1.01  
% 3.39/1.01  fof(f2,axiom,(
% 3.39/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f28,plain,(
% 3.39/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f2])).
% 3.39/1.01  
% 3.39/1.01  fof(f5,axiom,(
% 3.39/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.01  
% 3.39/1.01  fof(f32,plain,(
% 3.39/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.39/1.01    inference(cnf_transformation,[],[f5])).
% 3.39/1.01  
% 3.39/1.01  cnf(c_9,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 3.39/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_15,negated_conjecture,
% 3.39/1.01      ( r2_hidden(sK3,sK2) ),
% 3.39/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_201,plain,
% 3.39/1.01      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | sK3 != X0 | sK2 != X1 ),
% 3.39/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_202,plain,
% 3.39/1.01      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
% 3.39/1.01      inference(unflattening,[status(thm)],[c_201]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_494,plain,
% 3.39/1.01      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_202]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_12,plain,
% 3.39/1.01      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.39/1.01      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.39/1.01      | k1_xboole_0 = X0 ),
% 3.39/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_498,plain,
% 3.39/1.01      ( ~ r1_tarski(X0_39,k2_enumset1(X0_40,X0_40,X0_40,X0_40))
% 3.39/1.01      | k2_enumset1(X0_40,X0_40,X0_40,X0_40) = X0_39
% 3.39/1.01      | k1_xboole_0 = X0_39 ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_515,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0_39,X1_39)
% 3.39/1.01      | r1_xboole_0(X2_39,X3_39)
% 3.39/1.01      | X2_39 != X0_39
% 3.39/1.01      | X3_39 != X1_39 ),
% 3.39/1.01      theory(equality) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_511,plain,( X0_39 = X0_39 ),theory(equality) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1349,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0_39,X1_39)
% 3.39/1.01      | r1_xboole_0(X2_39,X1_39)
% 3.39/1.01      | X2_39 != X0_39 ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_515,c_511]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_2282,plain,
% 3.39/1.01      ( ~ r1_tarski(X0_39,k2_enumset1(X0_40,X0_40,X0_40,X0_40))
% 3.39/1.01      | ~ r1_xboole_0(X0_39,X1_39)
% 3.39/1.01      | r1_xboole_0(k2_enumset1(X0_40,X0_40,X0_40,X0_40),X1_39)
% 3.39/1.01      | k1_xboole_0 = X0_39 ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_498,c_1349]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_16,negated_conjecture,
% 3.39/1.01      ( r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 3.39/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_495,negated_conjecture,
% 3.39/1.01      ( r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_11065,plain,
% 3.39/1.01      ( r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0_39)
% 3.39/1.01      | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),X0_39)
% 3.39/1.01      | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_2282,c_495]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_11583,plain,
% 3.39/1.01      ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
% 3.39/1.01      | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_494,c_11065]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_13,negated_conjecture,
% 3.39/1.01      ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
% 3.39/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_522,plain,
% 3.39/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_511]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_505,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0_39,X1_39) | r1_xboole_0(X1_39,X0_39) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_962,plain,
% 3.39/1.01      ( r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
% 3.39/1.01      | ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_505]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_2,plain,
% 3.39/1.01      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.39/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_507,plain,
% 3.39/1.01      ( r1_xboole_0(X0_39,X1_39) | k3_xboole_0(X0_39,X1_39) != k1_xboole_0 ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1053,plain,
% 3.39/1.01      ( r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
% 3.39/1.01      | k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_507]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_512,plain,
% 3.39/1.01      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 3.39/1.01      theory(equality) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1147,plain,
% 3.39/1.01      ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != X0_39
% 3.39/1.01      | k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k1_xboole_0
% 3.39/1.01      | k1_xboole_0 != X0_39 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_512]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1605,plain,
% 3.39/1.01      ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k3_xboole_0(sK1,sK2)
% 3.39/1.01      | k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k1_xboole_0
% 3.39/1.01      | k1_xboole_0 != k3_xboole_0(sK1,sK2) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_1147]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_8,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.39/1.01      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
% 3.39/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_501,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0_39,X1_39)
% 3.39/1.01      | k3_xboole_0(X0_39,k2_xboole_0(X1_39,X2_39)) = k3_xboole_0(X0_39,X2_39) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1606,plain,
% 3.39/1.01      ( ~ r1_xboole_0(sK1,sK0)
% 3.39/1.01      | k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k3_xboole_0(sK1,sK2) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_501]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_14,negated_conjecture,
% 3.39/1.01      ( r1_xboole_0(sK2,sK1) ),
% 3.39/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_496,negated_conjecture,
% 3.39/1.01      ( r1_xboole_0(sK2,sK1) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_869,plain,
% 3.39/1.01      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_860,plain,
% 3.39/1.01      ( r1_xboole_0(X0_39,X1_39) != iProver_top
% 3.39/1.01      | r1_xboole_0(X1_39,X0_39) = iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1539,plain,
% 3.39/1.01      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_869,c_860]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.39/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_506,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0_39,X1_39) | k3_xboole_0(X0_39,X1_39) = k1_xboole_0 ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_859,plain,
% 3.39/1.01      ( k3_xboole_0(X0_39,X1_39) = k1_xboole_0
% 3.39/1.01      | r1_xboole_0(X0_39,X1_39) != iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1686,plain,
% 3.39/1.01      ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_1539,c_859]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1096,plain,
% 3.39/1.01      ( X0_39 != X1_39
% 3.39/1.01      | X0_39 = k3_xboole_0(X2_39,X3_39)
% 3.39/1.01      | k3_xboole_0(X2_39,X3_39) != X1_39 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_512]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_2327,plain,
% 3.39/1.01      ( k3_xboole_0(sK1,sK2) != X0_39
% 3.39/1.01      | k1_xboole_0 != X0_39
% 3.39/1.01      | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_1096]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_2328,plain,
% 3.39/1.01      ( k3_xboole_0(sK1,sK2) != k1_xboole_0
% 3.39/1.01      | k1_xboole_0 = k3_xboole_0(sK1,sK2)
% 3.39/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_2327]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1657,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0_39,sK1) | r1_xboole_0(sK1,X0_39) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_505]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_2811,plain,
% 3.39/1.01      ( r1_xboole_0(sK1,sK0) | ~ r1_xboole_0(sK0,sK1) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_1657]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_870,plain,
% 3.39/1.01      ( r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_867,plain,
% 3.39/1.01      ( k2_enumset1(X0_40,X0_40,X0_40,X0_40) = X0_39
% 3.39/1.01      | k1_xboole_0 = X0_39
% 3.39/1.01      | r1_tarski(X0_39,k2_enumset1(X0_40,X0_40,X0_40,X0_40)) != iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_498]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3286,plain,
% 3.39/1.01      ( k2_enumset1(sK3,sK3,sK3,sK3) = k3_xboole_0(sK0,sK1)
% 3.39/1.01      | k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_870,c_867]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_871,plain,
% 3.39/1.01      ( r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2) != iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3803,plain,
% 3.39/1.01      ( k3_xboole_0(sK0,sK1) = k1_xboole_0
% 3.39/1.01      | r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) != iProver_top ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_3286,c_871]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3827,plain,
% 3.39/1.01      ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
% 3.39/1.01      | k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 3.39/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3803]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5315,plain,
% 3.39/1.01      ( r1_xboole_0(sK0,sK1) | k3_xboole_0(sK0,sK1) != k1_xboole_0 ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_507]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_11654,plain,
% 3.39/1.01      ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_11583,c_13,c_522,c_962,c_1053,c_1605,c_1606,c_1686,c_2328,
% 3.39/1.01                 c_2811,c_3827,c_5315]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1470,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0_39,X1_39)
% 3.39/1.01      | r1_xboole_0(k3_xboole_0(X0_39,X1_39),X2_39)
% 3.39/1.01      | ~ r1_xboole_0(k1_xboole_0,X2_39) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_1349,c_506]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_6,plain,
% 3.39/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_503,plain,
% 3.39/1.01      ( r1_xboole_0(X0_39,k1_xboole_0) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1046,plain,
% 3.39/1.01      ( r1_xboole_0(k1_xboole_0,X0_39) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_505,c_503]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_2589,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0_39,X1_39)
% 3.39/1.01      | r1_xboole_0(k3_xboole_0(X0_39,X1_39),X2_39) ),
% 3.39/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_1470,c_1046]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_2747,plain,
% 3.39/1.01      ( ~ r1_xboole_0(X0_39,X1_39)
% 3.39/1.01      | r1_xboole_0(X2_39,k3_xboole_0(X0_39,X1_39)) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_2589,c_505]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_7,plain,
% 3.39/1.01      ( ~ r1_tarski(X0,X1)
% 3.39/1.01      | r1_xboole_0(X0,X2)
% 3.39/1.01      | ~ r1_xboole_0(X0,k3_xboole_0(X2,X1)) ),
% 3.39/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_502,plain,
% 3.39/1.01      ( ~ r1_tarski(X0_39,X1_39)
% 3.39/1.01      | r1_xboole_0(X0_39,X2_39)
% 3.39/1.01      | ~ r1_xboole_0(X0_39,k3_xboole_0(X2_39,X1_39)) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_2765,plain,
% 3.39/1.01      ( ~ r1_tarski(X0_39,X1_39)
% 3.39/1.01      | ~ r1_xboole_0(X2_39,X1_39)
% 3.39/1.01      | r1_xboole_0(X0_39,X2_39) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_2747,c_502]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_2990,plain,
% 3.39/1.01      ( ~ r1_tarski(X0_39,sK1) | r1_xboole_0(X0_39,sK2) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_2765,c_496]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_516,plain,
% 3.39/1.01      ( ~ r1_tarski(X0_39,X1_39)
% 3.39/1.01      | r1_tarski(X2_39,X3_39)
% 3.39/1.01      | X2_39 != X0_39
% 3.39/1.01      | X3_39 != X1_39 ),
% 3.39/1.01      theory(equality) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1449,plain,
% 3.39/1.01      ( ~ r1_tarski(X0_39,X1_39) | r1_tarski(X2_39,X1_39) | X2_39 != X0_39 ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_516,c_511]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1,plain,
% 3.39/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f28]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_508,plain,
% 3.39/1.01      ( k3_xboole_0(X0_39,X1_39) = k3_xboole_0(X1_39,X0_39) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1702,plain,
% 3.39/1.01      ( ~ r1_tarski(k3_xboole_0(X0_39,X1_39),X2_39)
% 3.39/1.01      | r1_tarski(k3_xboole_0(X1_39,X0_39),X2_39) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_1449,c_508]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5,plain,
% 3.39/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_504,plain,
% 3.39/1.01      ( r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
% 3.39/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1717,plain,
% 3.39/1.01      ( r1_tarski(k3_xboole_0(X0_39,X1_39),X1_39) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_1702,c_504]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_3178,plain,
% 3.39/1.01      ( r1_xboole_0(k3_xboole_0(X0_39,sK1),sK2) ),
% 3.39/1.01      inference(resolution,[status(thm)],[c_2990,c_1717]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_11659,plain,
% 3.39/1.01      ( $false ),
% 3.39/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_11654,c_3178]) ).
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.01  
% 3.39/1.01  ------                               Statistics
% 3.39/1.01  
% 3.39/1.01  ------ Selected
% 3.39/1.01  
% 3.39/1.01  total_time:                             0.349
% 3.39/1.01  
%------------------------------------------------------------------------------
