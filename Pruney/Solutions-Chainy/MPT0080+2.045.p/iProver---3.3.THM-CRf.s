%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:00 EST 2020

% Result     : Theorem 23.78s
% Output     : CNFRefutation 23.78s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 165 expanded)
%              Number of clauses        :   72 (  94 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  238 ( 434 expanded)
%              Number of equality atoms :  134 ( 194 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f10])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f21,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f23,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_172,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_171,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_810,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_172,c_171])).

cnf(c_173,plain,
    ( X0 != X1
    | X2 != X3
    | k2_xboole_0(X0,X2) = k2_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_967,plain,
    ( X0 != X1
    | X2 != X3
    | k2_xboole_0(X1,X3) = k2_xboole_0(X0,X2) ),
    inference(resolution,[status(thm)],[c_810,c_173])).

cnf(c_175,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10405,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(X3,k2_xboole_0(X4,X5))
    | X3 != X0
    | X1 != X4
    | X2 != X5 ),
    inference(resolution,[status(thm)],[c_967,c_175])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_100868,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | X0 != sK0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution,[status(thm)],[c_10405,c_8])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,negated_conjecture,
    ( r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_95,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | sK2 != X2
    | sK0 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_96,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(X0,sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_95])).

cnf(c_4078,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK2)
    | ~ r1_tarski(X1,sK0)
    | r1_tarski(X2,k1_xboole_0)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_96,c_175])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4820,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X0)
    | r1_tarski(k2_xboole_0(X2,X1),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4078,c_0])).

cnf(c_101628,plain,
    ( ~ r1_tarski(k2_xboole_0(X0,X1),sK2)
    | ~ r1_tarski(k2_xboole_0(X0,X1),sK0)
    | r1_tarski(k2_xboole_0(X2,X3),k1_xboole_0)
    | k2_xboole_0(X3,X2) != sK0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution,[status(thm)],[c_100868,c_4820])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_179,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_416,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_389,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1))
    | k4_xboole_0(X0,k2_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_509,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK0,X0))
    | k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_868,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1312,plain,
    ( r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_423,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k2_xboole_0(X2,X3))
    | X0 != X2
    | X1 != k2_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_580,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
    | r1_tarski(X2,k2_xboole_0(X1,X0))
    | X2 != X0
    | k2_xboole_0(X1,X0) != k2_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_1038,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
    | r1_tarski(sK0,k2_xboole_0(X1,X0))
    | k2_xboole_0(X1,X0) != k2_xboole_0(X0,X1)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_1646,plain,
    ( r1_tarski(sK0,k2_xboole_0(X0,sK0))
    | ~ r1_tarski(sK0,k2_xboole_0(sK0,X0))
    | k2_xboole_0(X0,sK0) != k2_xboole_0(sK0,X0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_413,plain,
    ( k4_xboole_0(X0,X1) != X2
    | k4_xboole_0(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_432,plain,
    ( k4_xboole_0(X0,X1) != k4_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_2318,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_2670,plain,
    ( k2_xboole_0(X0,sK0) = k2_xboole_0(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1862,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),sK2)
    | ~ r1_tarski(k4_xboole_0(X0,X1),sK0)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_2780,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1862])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_463,plain,
    ( ~ r1_tarski(sK0,X0)
    | k4_xboole_0(sK0,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1039,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(X0,X1))
    | k4_xboole_0(sK0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_3258,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(X0,sK0))
    | k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_331,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_334,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1654,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_331,c_334])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_333,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_761,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_333])).

cnf(c_4629,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_761])).

cnf(c_4736,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4629])).

cnf(c_174,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_2799,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_5061,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,X0)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2799])).

cnf(c_433,plain,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_5095,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_592,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != X3
    | k1_xboole_0 != X3
    | k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_5327,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,sK0)) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,sK0)) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_7186,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,sK0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5327])).

cnf(c_1025,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X2)
    | k4_xboole_0(k4_xboole_0(X0,X1),X2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1861,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),sK0)
    | k4_xboole_0(k4_xboole_0(X0,X1),sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_8836,plain,
    ( r1_tarski(k4_xboole_0(sK0,X0),sK0)
    | k4_xboole_0(k4_xboole_0(sK0,X0),sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1861])).

cnf(c_429,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_2447,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),sK0) != k4_xboole_0(X0,k2_xboole_0(X1,sK0))
    | k4_xboole_0(k4_xboole_0(X0,X1),sK0) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,sK0)) ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_9833,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),sK0) != k4_xboole_0(sK0,k2_xboole_0(X0,sK0))
    | k4_xboole_0(k4_xboole_0(sK0,X0),sK0) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2447])).

cnf(c_3022,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),sK0) = k4_xboole_0(X0,k2_xboole_0(X1,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_19338,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),sK0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_3022])).

cnf(c_1702,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK0)
    | X2 != X0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_2458,plain,
    ( ~ r1_tarski(X0,sK0)
    | r1_tarski(X1,sK0)
    | X1 != X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1702])).

cnf(c_4166,plain,
    ( r1_tarski(X0,sK0)
    | ~ r1_tarski(k4_xboole_0(X1,X2),sK0)
    | X0 != k4_xboole_0(X1,X2)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_10239,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),sK0)
    | r1_tarski(k4_xboole_0(sK0,X2),sK0)
    | k4_xboole_0(sK0,X2) != k4_xboole_0(X0,X1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_4166])).

cnf(c_20536,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,X0),sK0)
    | r1_tarski(k4_xboole_0(sK0,X1),sK0)
    | k4_xboole_0(sK0,X1) != k4_xboole_0(sK0,X0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_10239])).

cnf(c_46610,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,X0),sK0)
    | r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,X0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_20536])).

cnf(c_105147,plain,
    ( sK1 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_101628,c_6,c_179,c_416,c_509,c_868,c_1312,c_1646,c_2318,c_2670,c_2780,c_3258,c_4736,c_5061,c_5095,c_7186,c_8836,c_9833,c_19338,c_46610])).

cnf(c_105154,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_105147,c_171])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:18:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 23.78/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.78/3.49  
% 23.78/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.78/3.49  
% 23.78/3.49  ------  iProver source info
% 23.78/3.49  
% 23.78/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.78/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.78/3.49  git: non_committed_changes: false
% 23.78/3.49  git: last_make_outside_of_git: false
% 23.78/3.49  
% 23.78/3.49  ------ 
% 23.78/3.49  ------ Parsing...
% 23.78/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.78/3.49  
% 23.78/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.78/3.49  
% 23.78/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.78/3.49  
% 23.78/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.78/3.49  ------ Proving...
% 23.78/3.49  ------ Problem Properties 
% 23.78/3.49  
% 23.78/3.49  
% 23.78/3.49  clauses                                 8
% 23.78/3.49  conjectures                             2
% 23.78/3.49  EPR                                     2
% 23.78/3.49  Horn                                    8
% 23.78/3.49  unary                                   5
% 23.78/3.49  binary                                  2
% 23.78/3.49  lits                                    12
% 23.78/3.49  lits eq                                 6
% 23.78/3.49  fd_pure                                 0
% 23.78/3.49  fd_pseudo                               0
% 23.78/3.49  fd_cond                                 1
% 23.78/3.49  fd_pseudo_cond                          0
% 23.78/3.49  AC symbols                              0
% 23.78/3.49  
% 23.78/3.49  ------ Input Options Time Limit: Unbounded
% 23.78/3.49  
% 23.78/3.49  
% 23.78/3.49  ------ 
% 23.78/3.49  Current options:
% 23.78/3.49  ------ 
% 23.78/3.49  
% 23.78/3.49  
% 23.78/3.49  
% 23.78/3.49  
% 23.78/3.49  ------ Proving...
% 23.78/3.49  
% 23.78/3.49  
% 23.78/3.49  % SZS status Theorem for theBenchmark.p
% 23.78/3.49  
% 23.78/3.49   Resolution empty clause
% 23.78/3.49  
% 23.78/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.78/3.49  
% 23.78/3.49  fof(f6,conjecture,(
% 23.78/3.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 23.78/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.78/3.49  
% 23.78/3.49  fof(f7,negated_conjecture,(
% 23.78/3.49    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 23.78/3.49    inference(negated_conjecture,[],[f6])).
% 23.78/3.49  
% 23.78/3.49  fof(f10,plain,(
% 23.78/3.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 23.78/3.49    inference(ennf_transformation,[],[f7])).
% 23.78/3.49  
% 23.78/3.49  fof(f11,plain,(
% 23.78/3.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.78/3.49    inference(flattening,[],[f10])).
% 23.78/3.49  
% 23.78/3.49  fof(f13,plain,(
% 23.78/3.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 23.78/3.49    introduced(choice_axiom,[])).
% 23.78/3.49  
% 23.78/3.49  fof(f14,plain,(
% 23.78/3.49    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 23.78/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 23.78/3.49  
% 23.78/3.49  fof(f21,plain,(
% 23.78/3.49    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 23.78/3.49    inference(cnf_transformation,[],[f14])).
% 23.78/3.49  
% 23.78/3.49  fof(f5,axiom,(
% 23.78/3.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 23.78/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.78/3.49  
% 23.78/3.49  fof(f8,plain,(
% 23.78/3.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 23.78/3.49    inference(ennf_transformation,[],[f5])).
% 23.78/3.49  
% 23.78/3.49  fof(f9,plain,(
% 23.78/3.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 23.78/3.49    inference(flattening,[],[f8])).
% 23.78/3.49  
% 23.78/3.49  fof(f20,plain,(
% 23.78/3.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.78/3.49    inference(cnf_transformation,[],[f9])).
% 23.78/3.49  
% 23.78/3.49  fof(f22,plain,(
% 23.78/3.49    r1_xboole_0(sK0,sK2)),
% 23.78/3.49    inference(cnf_transformation,[],[f14])).
% 23.78/3.49  
% 23.78/3.49  fof(f1,axiom,(
% 23.78/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.78/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.78/3.49  
% 23.78/3.49  fof(f15,plain,(
% 23.78/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.78/3.49    inference(cnf_transformation,[],[f1])).
% 23.78/3.49  
% 23.78/3.49  fof(f23,plain,(
% 23.78/3.49    ~r1_tarski(sK0,sK1)),
% 23.78/3.49    inference(cnf_transformation,[],[f14])).
% 23.78/3.49  
% 23.78/3.49  fof(f2,axiom,(
% 23.78/3.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 23.78/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.78/3.49  
% 23.78/3.49  fof(f12,plain,(
% 23.78/3.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 23.78/3.49    inference(nnf_transformation,[],[f2])).
% 23.78/3.49  
% 23.78/3.49  fof(f16,plain,(
% 23.78/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 23.78/3.49    inference(cnf_transformation,[],[f12])).
% 23.78/3.49  
% 23.78/3.49  fof(f4,axiom,(
% 23.78/3.49    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 23.78/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.78/3.49  
% 23.78/3.49  fof(f19,plain,(
% 23.78/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 23.78/3.49    inference(cnf_transformation,[],[f4])).
% 23.78/3.49  
% 23.78/3.49  fof(f17,plain,(
% 23.78/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 23.78/3.49    inference(cnf_transformation,[],[f12])).
% 23.78/3.49  
% 23.78/3.49  fof(f3,axiom,(
% 23.78/3.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 23.78/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.78/3.49  
% 23.78/3.49  fof(f18,plain,(
% 23.78/3.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 23.78/3.49    inference(cnf_transformation,[],[f3])).
% 23.78/3.49  
% 23.78/3.49  cnf(c_172,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_171,plain,( X0 = X0 ),theory(equality) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_810,plain,
% 23.78/3.49      ( X0 != X1 | X1 = X0 ),
% 23.78/3.49      inference(resolution,[status(thm)],[c_172,c_171]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_173,plain,
% 23.78/3.49      ( X0 != X1 | X2 != X3 | k2_xboole_0(X0,X2) = k2_xboole_0(X1,X3) ),
% 23.78/3.49      theory(equality) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_967,plain,
% 23.78/3.49      ( X0 != X1 | X2 != X3 | k2_xboole_0(X1,X3) = k2_xboole_0(X0,X2) ),
% 23.78/3.49      inference(resolution,[status(thm)],[c_810,c_173]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_175,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.78/3.49      theory(equality) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_10405,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 23.78/3.49      | r1_tarski(X3,k2_xboole_0(X4,X5))
% 23.78/3.49      | X3 != X0
% 23.78/3.49      | X1 != X4
% 23.78/3.49      | X2 != X5 ),
% 23.78/3.49      inference(resolution,[status(thm)],[c_967,c_175]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_8,negated_conjecture,
% 23.78/3.49      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 23.78/3.49      inference(cnf_transformation,[],[f21]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_100868,plain,
% 23.78/3.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) | X0 != sK0 | sK2 != X2 | sK1 != X1 ),
% 23.78/3.49      inference(resolution,[status(thm)],[c_10405,c_8]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_5,plain,
% 23.78/3.49      ( ~ r1_xboole_0(X0,X1)
% 23.78/3.49      | ~ r1_tarski(X2,X0)
% 23.78/3.49      | ~ r1_tarski(X2,X1)
% 23.78/3.49      | k1_xboole_0 = X2 ),
% 23.78/3.49      inference(cnf_transformation,[],[f20]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_7,negated_conjecture,
% 23.78/3.49      ( r1_xboole_0(sK0,sK2) ),
% 23.78/3.49      inference(cnf_transformation,[],[f22]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_95,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,X1)
% 23.78/3.49      | ~ r1_tarski(X0,X2)
% 23.78/3.49      | sK2 != X2
% 23.78/3.49      | sK0 != X1
% 23.78/3.49      | k1_xboole_0 = X0 ),
% 23.78/3.49      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_96,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(X0,sK0) | k1_xboole_0 = X0 ),
% 23.78/3.49      inference(unflattening,[status(thm)],[c_95]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_4078,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,X1)
% 23.78/3.49      | ~ r1_tarski(X1,sK2)
% 23.78/3.49      | ~ r1_tarski(X1,sK0)
% 23.78/3.49      | r1_tarski(X2,k1_xboole_0)
% 23.78/3.49      | X2 != X0 ),
% 23.78/3.49      inference(resolution,[status(thm)],[c_96,c_175]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_0,plain,
% 23.78/3.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 23.78/3.49      inference(cnf_transformation,[],[f15]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_4820,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,sK2)
% 23.78/3.49      | ~ r1_tarski(X0,sK0)
% 23.78/3.49      | ~ r1_tarski(k2_xboole_0(X1,X2),X0)
% 23.78/3.49      | r1_tarski(k2_xboole_0(X2,X1),k1_xboole_0) ),
% 23.78/3.49      inference(resolution,[status(thm)],[c_4078,c_0]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_101628,plain,
% 23.78/3.49      ( ~ r1_tarski(k2_xboole_0(X0,X1),sK2)
% 23.78/3.49      | ~ r1_tarski(k2_xboole_0(X0,X1),sK0)
% 23.78/3.49      | r1_tarski(k2_xboole_0(X2,X3),k1_xboole_0)
% 23.78/3.49      | k2_xboole_0(X3,X2) != sK0
% 23.78/3.49      | sK2 != X1
% 23.78/3.49      | sK1 != X0 ),
% 23.78/3.49      inference(resolution,[status(thm)],[c_100868,c_4820]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_6,negated_conjecture,
% 23.78/3.49      ( ~ r1_tarski(sK0,sK1) ),
% 23.78/3.49      inference(cnf_transformation,[],[f23]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_179,plain,
% 23.78/3.49      ( k1_xboole_0 = k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_171]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_416,plain,
% 23.78/3.49      ( sK0 = sK0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_171]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_2,plain,
% 23.78/3.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 23.78/3.49      inference(cnf_transformation,[],[f16]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_389,plain,
% 23.78/3.49      ( r1_tarski(X0,k2_xboole_0(X0,X1))
% 23.78/3.49      | k4_xboole_0(X0,k2_xboole_0(X0,X1)) != k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_509,plain,
% 23.78/3.49      ( r1_tarski(sK0,k2_xboole_0(sK0,X0))
% 23.78/3.49      | k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) != k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_389]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_4,plain,
% 23.78/3.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.78/3.49      inference(cnf_transformation,[],[f19]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_868,plain,
% 23.78/3.49      ( k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) = k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_4]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1312,plain,
% 23.78/3.49      ( r1_tarski(sK0,sK1) | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_423,plain,
% 23.78/3.49      ( r1_tarski(X0,X1)
% 23.78/3.49      | ~ r1_tarski(X2,k2_xboole_0(X2,X3))
% 23.78/3.49      | X0 != X2
% 23.78/3.49      | X1 != k2_xboole_0(X2,X3) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_175]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_580,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
% 23.78/3.49      | r1_tarski(X2,k2_xboole_0(X1,X0))
% 23.78/3.49      | X2 != X0
% 23.78/3.49      | k2_xboole_0(X1,X0) != k2_xboole_0(X0,X1) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_423]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1038,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
% 23.78/3.49      | r1_tarski(sK0,k2_xboole_0(X1,X0))
% 23.78/3.49      | k2_xboole_0(X1,X0) != k2_xboole_0(X0,X1)
% 23.78/3.49      | sK0 != X0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_580]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1646,plain,
% 23.78/3.49      ( r1_tarski(sK0,k2_xboole_0(X0,sK0))
% 23.78/3.49      | ~ r1_tarski(sK0,k2_xboole_0(sK0,X0))
% 23.78/3.49      | k2_xboole_0(X0,sK0) != k2_xboole_0(sK0,X0)
% 23.78/3.49      | sK0 != sK0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_1038]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_413,plain,
% 23.78/3.49      ( k4_xboole_0(X0,X1) != X2
% 23.78/3.49      | k4_xboole_0(X0,X1) = k1_xboole_0
% 23.78/3.49      | k1_xboole_0 != X2 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_172]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_432,plain,
% 23.78/3.49      ( k4_xboole_0(X0,X1) != k4_xboole_0(X0,X1)
% 23.78/3.49      | k4_xboole_0(X0,X1) = k1_xboole_0
% 23.78/3.49      | k1_xboole_0 != k4_xboole_0(X0,X1) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_413]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_2318,plain,
% 23.78/3.49      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
% 23.78/3.49      | k4_xboole_0(sK0,sK1) = k1_xboole_0
% 23.78/3.49      | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_432]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_2670,plain,
% 23.78/3.49      ( k2_xboole_0(X0,sK0) = k2_xboole_0(sK0,X0) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_0]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1862,plain,
% 23.78/3.49      ( ~ r1_tarski(k4_xboole_0(X0,X1),sK2)
% 23.78/3.49      | ~ r1_tarski(k4_xboole_0(X0,X1),sK0)
% 23.78/3.49      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_96]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_2780,plain,
% 23.78/3.49      ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2)
% 23.78/3.49      | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
% 23.78/3.49      | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_1862]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 23.78/3.49      inference(cnf_transformation,[],[f17]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_463,plain,
% 23.78/3.49      ( ~ r1_tarski(sK0,X0) | k4_xboole_0(sK0,X0) = k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_1]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1039,plain,
% 23.78/3.49      ( ~ r1_tarski(sK0,k2_xboole_0(X0,X1))
% 23.78/3.49      | k4_xboole_0(sK0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_463]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_3258,plain,
% 23.78/3.49      ( ~ r1_tarski(sK0,k2_xboole_0(X0,sK0))
% 23.78/3.49      | k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) = k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_1039]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_331,plain,
% 23.78/3.49      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 23.78/3.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_334,plain,
% 23.78/3.49      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 23.78/3.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1654,plain,
% 23.78/3.49      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 23.78/3.49      inference(superposition,[status(thm)],[c_331,c_334]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_3,plain,
% 23.78/3.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.78/3.49      inference(cnf_transformation,[],[f18]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_333,plain,
% 23.78/3.49      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 23.78/3.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_761,plain,
% 23.78/3.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0
% 23.78/3.49      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 23.78/3.49      inference(superposition,[status(thm)],[c_3,c_333]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_4629,plain,
% 23.78/3.49      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
% 23.78/3.49      inference(superposition,[status(thm)],[c_1654,c_761]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_4736,plain,
% 23.78/3.49      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
% 23.78/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_4629]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_174,plain,
% 23.78/3.49      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 23.78/3.49      theory(equality) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_2799,plain,
% 23.78/3.49      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X1) | sK1 != X1 | sK0 != X0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_174]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_5061,plain,
% 23.78/3.49      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,X0) | sK1 != X0 | sK0 != sK0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_2799]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_433,plain,
% 23.78/3.49      ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,X1) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_171]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_5095,plain,
% 23.78/3.49      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_433]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_592,plain,
% 23.78/3.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != X3
% 23.78/3.49      | k1_xboole_0 != X3
% 23.78/3.49      | k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_172]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_5327,plain,
% 23.78/3.49      ( k4_xboole_0(X0,k2_xboole_0(X1,sK0)) != X2
% 23.78/3.49      | k1_xboole_0 != X2
% 23.78/3.49      | k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,sK0)) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_592]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_7186,plain,
% 23.78/3.49      ( k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) != k1_xboole_0
% 23.78/3.49      | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,sK0))
% 23.78/3.49      | k1_xboole_0 != k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_5327]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1025,plain,
% 23.78/3.49      ( r1_tarski(k4_xboole_0(X0,X1),X2)
% 23.78/3.49      | k4_xboole_0(k4_xboole_0(X0,X1),X2) != k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1861,plain,
% 23.78/3.49      ( r1_tarski(k4_xboole_0(X0,X1),sK0)
% 23.78/3.49      | k4_xboole_0(k4_xboole_0(X0,X1),sK0) != k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_1025]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_8836,plain,
% 23.78/3.49      ( r1_tarski(k4_xboole_0(sK0,X0),sK0)
% 23.78/3.49      | k4_xboole_0(k4_xboole_0(sK0,X0),sK0) != k1_xboole_0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_1861]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_429,plain,
% 23.78/3.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2))
% 23.78/3.49      | k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
% 23.78/3.49      | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_413]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_2447,plain,
% 23.78/3.49      ( k4_xboole_0(k4_xboole_0(X0,X1),sK0) != k4_xboole_0(X0,k2_xboole_0(X1,sK0))
% 23.78/3.49      | k4_xboole_0(k4_xboole_0(X0,X1),sK0) = k1_xboole_0
% 23.78/3.49      | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,sK0)) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_429]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_9833,plain,
% 23.78/3.49      ( k4_xboole_0(k4_xboole_0(sK0,X0),sK0) != k4_xboole_0(sK0,k2_xboole_0(X0,sK0))
% 23.78/3.49      | k4_xboole_0(k4_xboole_0(sK0,X0),sK0) = k1_xboole_0
% 23.78/3.49      | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_2447]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_3022,plain,
% 23.78/3.49      ( k4_xboole_0(k4_xboole_0(X0,X1),sK0) = k4_xboole_0(X0,k2_xboole_0(X1,sK0)) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_3]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_19338,plain,
% 23.78/3.49      ( k4_xboole_0(k4_xboole_0(sK0,X0),sK0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_3022]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_1702,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK0) | X2 != X0 | sK0 != X1 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_175]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_2458,plain,
% 23.78/3.49      ( ~ r1_tarski(X0,sK0) | r1_tarski(X1,sK0) | X1 != X0 | sK0 != sK0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_1702]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_4166,plain,
% 23.78/3.49      ( r1_tarski(X0,sK0)
% 23.78/3.49      | ~ r1_tarski(k4_xboole_0(X1,X2),sK0)
% 23.78/3.49      | X0 != k4_xboole_0(X1,X2)
% 23.78/3.49      | sK0 != sK0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_2458]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_10239,plain,
% 23.78/3.49      ( ~ r1_tarski(k4_xboole_0(X0,X1),sK0)
% 23.78/3.49      | r1_tarski(k4_xboole_0(sK0,X2),sK0)
% 23.78/3.49      | k4_xboole_0(sK0,X2) != k4_xboole_0(X0,X1)
% 23.78/3.49      | sK0 != sK0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_4166]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_20536,plain,
% 23.78/3.49      ( ~ r1_tarski(k4_xboole_0(sK0,X0),sK0)
% 23.78/3.49      | r1_tarski(k4_xboole_0(sK0,X1),sK0)
% 23.78/3.49      | k4_xboole_0(sK0,X1) != k4_xboole_0(sK0,X0)
% 23.78/3.49      | sK0 != sK0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_10239]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_46610,plain,
% 23.78/3.49      ( ~ r1_tarski(k4_xboole_0(sK0,X0),sK0)
% 23.78/3.49      | r1_tarski(k4_xboole_0(sK0,sK1),sK0)
% 23.78/3.49      | k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,X0)
% 23.78/3.49      | sK0 != sK0 ),
% 23.78/3.49      inference(instantiation,[status(thm)],[c_20536]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_105147,plain,
% 23.78/3.49      ( sK1 != X0 ),
% 23.78/3.49      inference(global_propositional_subsumption,
% 23.78/3.49                [status(thm)],
% 23.78/3.49                [c_101628,c_6,c_179,c_416,c_509,c_868,c_1312,c_1646,c_2318,
% 23.78/3.49                 c_2670,c_2780,c_3258,c_4736,c_5061,c_5095,c_7186,c_8836,
% 23.78/3.49                 c_9833,c_19338,c_46610]) ).
% 23.78/3.49  
% 23.78/3.49  cnf(c_105154,plain,
% 23.78/3.49      ( $false ),
% 23.78/3.49      inference(resolution,[status(thm)],[c_105147,c_171]) ).
% 23.78/3.49  
% 23.78/3.49  
% 23.78/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.78/3.49  
% 23.78/3.49  ------                               Statistics
% 23.78/3.49  
% 23.78/3.49  ------ Selected
% 23.78/3.49  
% 23.78/3.49  total_time:                             2.983
% 23.78/3.49  
%------------------------------------------------------------------------------
