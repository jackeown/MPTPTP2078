%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:53 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 142 expanded)
%              Number of clauses        :   54 (  61 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 ( 343 expanded)
%              Number of equality atoms :  109 ( 185 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f25])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f29])).

fof(f46,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3233,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),X1)
    | ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_9096,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ r1_xboole_0(X0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3233])).

cnf(c_31140,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK3)
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ r1_xboole_0(sK3,sK1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_9096])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_685,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_13260,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_17,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_499,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1153,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_499])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_500,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_502,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1756,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_502])).

cnf(c_6283,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1153,c_1756])).

cnf(c_6437,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17,c_6283])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_501,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6890,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6437,c_501])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_498,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7183,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6890,c_498])).

cnf(c_7219,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7183])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_495,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2535,plain,
    ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_498])).

cnf(c_2772,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_495,c_2535])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_492,plain,
    ( r1_xboole_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_503,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1783,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_492,c_503])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5202,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_1783,c_9])).

cnf(c_5204,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_5202,c_7])).

cnf(c_5901,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2772,c_5204])).

cnf(c_824,plain,
    ( ~ r1_tarski(X0,sK1)
    | k4_xboole_0(X0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5423,plain,
    ( ~ r1_tarski(sK2,sK1)
    | k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_5427,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5423])).

cnf(c_171,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_819,plain,
    ( X0 != X1
    | k4_xboole_0(sK1,sK2) != X1
    | k4_xboole_0(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_1514,plain,
    ( X0 != k4_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) = X0
    | k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1515,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_170,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_818,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_672,plain,
    ( k4_xboole_0(sK2,sK1) != X0
    | k4_xboole_0(sK1,sK2) != X0
    | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_673,plain,
    ( k4_xboole_0(sK2,sK1) != k1_xboole_0
    | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1)
    | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_5,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_631,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK2,sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_14,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31140,c_13260,c_7219,c_5901,c_5427,c_1515,c_818,c_673,c_631,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.88/1.56  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/1.56  
% 7.88/1.56  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.88/1.56  
% 7.88/1.56  ------  iProver source info
% 7.88/1.56  
% 7.88/1.56  git: date: 2020-06-30 10:37:57 +0100
% 7.88/1.56  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.88/1.56  git: non_committed_changes: false
% 7.88/1.56  git: last_make_outside_of_git: false
% 7.88/1.56  
% 7.88/1.56  ------ 
% 7.88/1.56  
% 7.88/1.56  ------ Input Options
% 7.88/1.56  
% 7.88/1.56  --out_options                           all
% 7.88/1.56  --tptp_safe_out                         true
% 7.88/1.56  --problem_path                          ""
% 7.88/1.56  --include_path                          ""
% 7.88/1.56  --clausifier                            res/vclausify_rel
% 7.88/1.56  --clausifier_options                    --mode clausify
% 7.88/1.56  --stdin                                 false
% 7.88/1.56  --stats_out                             sel
% 7.88/1.56  
% 7.88/1.56  ------ General Options
% 7.88/1.56  
% 7.88/1.56  --fof                                   false
% 7.88/1.56  --time_out_real                         604.97
% 7.88/1.56  --time_out_virtual                      -1.
% 7.88/1.56  --symbol_type_check                     false
% 7.88/1.56  --clausify_out                          false
% 7.88/1.56  --sig_cnt_out                           false
% 7.88/1.56  --trig_cnt_out                          false
% 7.88/1.56  --trig_cnt_out_tolerance                1.
% 7.88/1.56  --trig_cnt_out_sk_spl                   false
% 7.88/1.56  --abstr_cl_out                          false
% 7.88/1.56  
% 7.88/1.56  ------ Global Options
% 7.88/1.56  
% 7.88/1.56  --schedule                              none
% 7.88/1.56  --add_important_lit                     false
% 7.88/1.56  --prop_solver_per_cl                    1000
% 7.88/1.56  --min_unsat_core                        false
% 7.88/1.56  --soft_assumptions                      false
% 7.88/1.56  --soft_lemma_size                       3
% 7.88/1.56  --prop_impl_unit_size                   0
% 7.88/1.56  --prop_impl_unit                        []
% 7.88/1.56  --share_sel_clauses                     true
% 7.88/1.56  --reset_solvers                         false
% 7.88/1.56  --bc_imp_inh                            [conj_cone]
% 7.88/1.56  --conj_cone_tolerance                   3.
% 7.88/1.56  --extra_neg_conj                        none
% 7.88/1.56  --large_theory_mode                     true
% 7.88/1.56  --prolific_symb_bound                   200
% 7.88/1.56  --lt_threshold                          2000
% 7.88/1.56  --clause_weak_htbl                      true
% 7.88/1.56  --gc_record_bc_elim                     false
% 7.88/1.56  
% 7.88/1.56  ------ Preprocessing Options
% 7.88/1.56  
% 7.88/1.56  --preprocessing_flag                    true
% 7.88/1.56  --time_out_prep_mult                    0.1
% 7.88/1.56  --splitting_mode                        input
% 7.88/1.56  --splitting_grd                         true
% 7.88/1.56  --splitting_cvd                         false
% 7.88/1.56  --splitting_cvd_svl                     false
% 7.88/1.56  --splitting_nvd                         32
% 7.88/1.56  --sub_typing                            true
% 7.88/1.56  --prep_gs_sim                           false
% 7.88/1.56  --prep_unflatten                        true
% 7.88/1.56  --prep_res_sim                          true
% 7.88/1.56  --prep_upred                            true
% 7.88/1.56  --prep_sem_filter                       exhaustive
% 7.88/1.56  --prep_sem_filter_out                   false
% 7.88/1.56  --pred_elim                             false
% 7.88/1.56  --res_sim_input                         true
% 7.88/1.56  --eq_ax_congr_red                       true
% 7.88/1.56  --pure_diseq_elim                       true
% 7.88/1.56  --brand_transform                       false
% 7.88/1.56  --non_eq_to_eq                          false
% 7.88/1.56  --prep_def_merge                        true
% 7.88/1.56  --prep_def_merge_prop_impl              false
% 7.88/1.56  --prep_def_merge_mbd                    true
% 7.88/1.56  --prep_def_merge_tr_red                 false
% 7.88/1.56  --prep_def_merge_tr_cl                  false
% 7.88/1.56  --smt_preprocessing                     true
% 7.88/1.56  --smt_ac_axioms                         fast
% 7.88/1.56  --preprocessed_out                      false
% 7.88/1.56  --preprocessed_stats                    false
% 7.88/1.56  
% 7.88/1.56  ------ Abstraction refinement Options
% 7.88/1.56  
% 7.88/1.56  --abstr_ref                             []
% 7.88/1.56  --abstr_ref_prep                        false
% 7.88/1.56  --abstr_ref_until_sat                   false
% 7.88/1.56  --abstr_ref_sig_restrict                funpre
% 7.88/1.56  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.56  --abstr_ref_under                       []
% 7.88/1.56  
% 7.88/1.56  ------ SAT Options
% 7.88/1.56  
% 7.88/1.56  --sat_mode                              false
% 7.88/1.56  --sat_fm_restart_options                ""
% 7.88/1.56  --sat_gr_def                            false
% 7.88/1.56  --sat_epr_types                         true
% 7.88/1.56  --sat_non_cyclic_types                  false
% 7.88/1.56  --sat_finite_models                     false
% 7.88/1.56  --sat_fm_lemmas                         false
% 7.88/1.56  --sat_fm_prep                           false
% 7.88/1.56  --sat_fm_uc_incr                        true
% 7.88/1.56  --sat_out_model                         small
% 7.88/1.56  --sat_out_clauses                       false
% 7.88/1.56  
% 7.88/1.56  ------ QBF Options
% 7.88/1.56  
% 7.88/1.56  --qbf_mode                              false
% 7.88/1.56  --qbf_elim_univ                         false
% 7.88/1.56  --qbf_dom_inst                          none
% 7.88/1.56  --qbf_dom_pre_inst                      false
% 7.88/1.56  --qbf_sk_in                             false
% 7.88/1.56  --qbf_pred_elim                         true
% 7.88/1.56  --qbf_split                             512
% 7.88/1.56  
% 7.88/1.56  ------ BMC1 Options
% 7.88/1.56  
% 7.88/1.56  --bmc1_incremental                      false
% 7.88/1.56  --bmc1_axioms                           reachable_all
% 7.88/1.56  --bmc1_min_bound                        0
% 7.88/1.56  --bmc1_max_bound                        -1
% 7.88/1.56  --bmc1_max_bound_default                -1
% 7.88/1.56  --bmc1_symbol_reachability              true
% 7.88/1.56  --bmc1_property_lemmas                  false
% 7.88/1.56  --bmc1_k_induction                      false
% 7.88/1.56  --bmc1_non_equiv_states                 false
% 7.88/1.56  --bmc1_deadlock                         false
% 7.88/1.56  --bmc1_ucm                              false
% 7.88/1.56  --bmc1_add_unsat_core                   none
% 7.88/1.56  --bmc1_unsat_core_children              false
% 7.88/1.56  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.56  --bmc1_out_stat                         full
% 7.88/1.56  --bmc1_ground_init                      false
% 7.88/1.56  --bmc1_pre_inst_next_state              false
% 7.88/1.56  --bmc1_pre_inst_state                   false
% 7.88/1.56  --bmc1_pre_inst_reach_state             false
% 7.88/1.56  --bmc1_out_unsat_core                   false
% 7.88/1.56  --bmc1_aig_witness_out                  false
% 7.88/1.56  --bmc1_verbose                          false
% 7.88/1.56  --bmc1_dump_clauses_tptp                false
% 7.88/1.56  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.56  --bmc1_dump_file                        -
% 7.88/1.56  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.56  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.56  --bmc1_ucm_extend_mode                  1
% 7.88/1.56  --bmc1_ucm_init_mode                    2
% 7.88/1.56  --bmc1_ucm_cone_mode                    none
% 7.88/1.56  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.56  --bmc1_ucm_relax_model                  4
% 7.88/1.56  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.56  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.56  --bmc1_ucm_layered_model                none
% 7.88/1.56  --bmc1_ucm_max_lemma_size               10
% 7.88/1.56  
% 7.88/1.56  ------ AIG Options
% 7.88/1.56  
% 7.88/1.56  --aig_mode                              false
% 7.88/1.56  
% 7.88/1.56  ------ Instantiation Options
% 7.88/1.56  
% 7.88/1.56  --instantiation_flag                    true
% 7.88/1.56  --inst_sos_flag                         false
% 7.88/1.56  --inst_sos_phase                        true
% 7.88/1.56  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.56  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.56  --inst_lit_sel_side                     num_symb
% 7.88/1.56  --inst_solver_per_active                1400
% 7.88/1.56  --inst_solver_calls_frac                1.
% 7.88/1.56  --inst_passive_queue_type               priority_queues
% 7.88/1.56  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.56  --inst_passive_queues_freq              [25;2]
% 7.88/1.56  --inst_dismatching                      true
% 7.88/1.56  --inst_eager_unprocessed_to_passive     true
% 7.88/1.56  --inst_prop_sim_given                   true
% 7.88/1.56  --inst_prop_sim_new                     false
% 7.88/1.56  --inst_subs_new                         false
% 7.88/1.56  --inst_eq_res_simp                      false
% 7.88/1.56  --inst_subs_given                       false
% 7.88/1.56  --inst_orphan_elimination               true
% 7.88/1.56  --inst_learning_loop_flag               true
% 7.88/1.56  --inst_learning_start                   3000
% 7.88/1.56  --inst_learning_factor                  2
% 7.88/1.56  --inst_start_prop_sim_after_learn       3
% 7.88/1.56  --inst_sel_renew                        solver
% 7.88/1.56  --inst_lit_activity_flag                true
% 7.88/1.56  --inst_restr_to_given                   false
% 7.88/1.56  --inst_activity_threshold               500
% 7.88/1.56  --inst_out_proof                        true
% 7.88/1.56  
% 7.88/1.56  ------ Resolution Options
% 7.88/1.56  
% 7.88/1.56  --resolution_flag                       true
% 7.88/1.56  --res_lit_sel                           adaptive
% 7.88/1.56  --res_lit_sel_side                      none
% 7.88/1.56  --res_ordering                          kbo
% 7.88/1.56  --res_to_prop_solver                    active
% 7.88/1.56  --res_prop_simpl_new                    false
% 7.88/1.56  --res_prop_simpl_given                  true
% 7.88/1.56  --res_passive_queue_type                priority_queues
% 7.88/1.56  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.56  --res_passive_queues_freq               [15;5]
% 7.88/1.56  --res_forward_subs                      full
% 7.88/1.56  --res_backward_subs                     full
% 7.88/1.56  --res_forward_subs_resolution           true
% 7.88/1.56  --res_backward_subs_resolution          true
% 7.88/1.56  --res_orphan_elimination                true
% 7.88/1.56  --res_time_limit                        2.
% 7.88/1.56  --res_out_proof                         true
% 7.88/1.56  
% 7.88/1.56  ------ Superposition Options
% 7.88/1.56  
% 7.88/1.56  --superposition_flag                    true
% 7.88/1.56  --sup_passive_queue_type                priority_queues
% 7.88/1.56  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.56  --sup_passive_queues_freq               [1;4]
% 7.88/1.56  --demod_completeness_check              fast
% 7.88/1.56  --demod_use_ground                      true
% 7.88/1.56  --sup_to_prop_solver                    passive
% 7.88/1.56  --sup_prop_simpl_new                    true
% 7.88/1.56  --sup_prop_simpl_given                  true
% 7.88/1.56  --sup_fun_splitting                     false
% 7.88/1.56  --sup_smt_interval                      50000
% 7.88/1.56  
% 7.88/1.56  ------ Superposition Simplification Setup
% 7.88/1.56  
% 7.88/1.56  --sup_indices_passive                   []
% 7.88/1.56  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.56  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.56  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.56  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.56  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.56  --sup_full_bw                           [BwDemod]
% 7.88/1.56  --sup_immed_triv                        [TrivRules]
% 7.88/1.56  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.56  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.56  --sup_immed_bw_main                     []
% 7.88/1.56  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.56  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.56  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.56  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.56  
% 7.88/1.56  ------ Combination Options
% 7.88/1.56  
% 7.88/1.56  --comb_res_mult                         3
% 7.88/1.56  --comb_sup_mult                         2
% 7.88/1.56  --comb_inst_mult                        10
% 7.88/1.56  
% 7.88/1.56  ------ Debug Options
% 7.88/1.56  
% 7.88/1.56  --dbg_backtrace                         false
% 7.88/1.56  --dbg_dump_prop_clauses                 false
% 7.88/1.56  --dbg_dump_prop_clauses_file            -
% 7.88/1.56  --dbg_out_stat                          false
% 7.88/1.56  ------ Parsing...
% 7.88/1.56  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.88/1.56  
% 7.88/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.88/1.56  
% 7.88/1.56  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.88/1.56  
% 7.88/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.88/1.56  ------ Proving...
% 7.88/1.56  ------ Problem Properties 
% 7.88/1.56  
% 7.88/1.56  
% 7.88/1.56  clauses                                 18
% 7.88/1.56  conjectures                             4
% 7.88/1.56  EPR                                     5
% 7.88/1.56  Horn                                    18
% 7.88/1.56  unary                                   8
% 7.88/1.56  binary                                  7
% 7.88/1.56  lits                                    33
% 7.88/1.56  lits eq                                 11
% 7.88/1.56  fd_pure                                 0
% 7.88/1.56  fd_pseudo                               0
% 7.88/1.56  fd_cond                                 1
% 7.88/1.56  fd_pseudo_cond                          1
% 7.88/1.56  AC symbols                              0
% 7.88/1.56  
% 7.88/1.56  ------ Input Options Time Limit: Unbounded
% 7.88/1.56  
% 7.88/1.56  
% 7.88/1.56  ------ 
% 7.88/1.56  Current options:
% 7.88/1.56  ------ 
% 7.88/1.56  
% 7.88/1.56  ------ Input Options
% 7.88/1.56  
% 7.88/1.56  --out_options                           all
% 7.88/1.56  --tptp_safe_out                         true
% 7.88/1.56  --problem_path                          ""
% 7.88/1.56  --include_path                          ""
% 7.88/1.56  --clausifier                            res/vclausify_rel
% 7.88/1.56  --clausifier_options                    --mode clausify
% 7.88/1.56  --stdin                                 false
% 7.88/1.56  --stats_out                             sel
% 7.88/1.56  
% 7.88/1.56  ------ General Options
% 7.88/1.56  
% 7.88/1.56  --fof                                   false
% 7.88/1.56  --time_out_real                         604.97
% 7.88/1.56  --time_out_virtual                      -1.
% 7.88/1.56  --symbol_type_check                     false
% 7.88/1.56  --clausify_out                          false
% 7.88/1.56  --sig_cnt_out                           false
% 7.88/1.56  --trig_cnt_out                          false
% 7.88/1.56  --trig_cnt_out_tolerance                1.
% 7.88/1.56  --trig_cnt_out_sk_spl                   false
% 7.88/1.56  --abstr_cl_out                          false
% 7.88/1.56  
% 7.88/1.56  ------ Global Options
% 7.88/1.56  
% 7.88/1.56  --schedule                              none
% 7.88/1.56  --add_important_lit                     false
% 7.88/1.56  --prop_solver_per_cl                    1000
% 7.88/1.56  --min_unsat_core                        false
% 7.88/1.56  --soft_assumptions                      false
% 7.88/1.56  --soft_lemma_size                       3
% 7.88/1.56  --prop_impl_unit_size                   0
% 7.88/1.56  --prop_impl_unit                        []
% 7.88/1.56  --share_sel_clauses                     true
% 7.88/1.56  --reset_solvers                         false
% 7.88/1.56  --bc_imp_inh                            [conj_cone]
% 7.88/1.56  --conj_cone_tolerance                   3.
% 7.88/1.56  --extra_neg_conj                        none
% 7.88/1.56  --large_theory_mode                     true
% 7.88/1.56  --prolific_symb_bound                   200
% 7.88/1.56  --lt_threshold                          2000
% 7.88/1.56  --clause_weak_htbl                      true
% 7.88/1.56  --gc_record_bc_elim                     false
% 7.88/1.56  
% 7.88/1.56  ------ Preprocessing Options
% 7.88/1.56  
% 7.88/1.56  --preprocessing_flag                    true
% 7.88/1.56  --time_out_prep_mult                    0.1
% 7.88/1.56  --splitting_mode                        input
% 7.88/1.56  --splitting_grd                         true
% 7.88/1.56  --splitting_cvd                         false
% 7.88/1.56  --splitting_cvd_svl                     false
% 7.88/1.56  --splitting_nvd                         32
% 7.88/1.56  --sub_typing                            true
% 7.88/1.56  --prep_gs_sim                           false
% 7.88/1.56  --prep_unflatten                        true
% 7.88/1.56  --prep_res_sim                          true
% 7.88/1.56  --prep_upred                            true
% 7.88/1.56  --prep_sem_filter                       exhaustive
% 7.88/1.56  --prep_sem_filter_out                   false
% 7.88/1.56  --pred_elim                             false
% 7.88/1.56  --res_sim_input                         true
% 7.88/1.56  --eq_ax_congr_red                       true
% 7.88/1.56  --pure_diseq_elim                       true
% 7.88/1.56  --brand_transform                       false
% 7.88/1.56  --non_eq_to_eq                          false
% 7.88/1.56  --prep_def_merge                        true
% 7.88/1.56  --prep_def_merge_prop_impl              false
% 7.88/1.56  --prep_def_merge_mbd                    true
% 7.88/1.56  --prep_def_merge_tr_red                 false
% 7.88/1.56  --prep_def_merge_tr_cl                  false
% 7.88/1.56  --smt_preprocessing                     true
% 7.88/1.56  --smt_ac_axioms                         fast
% 7.88/1.56  --preprocessed_out                      false
% 7.88/1.56  --preprocessed_stats                    false
% 7.88/1.56  
% 7.88/1.56  ------ Abstraction refinement Options
% 7.88/1.56  
% 7.88/1.56  --abstr_ref                             []
% 7.88/1.56  --abstr_ref_prep                        false
% 7.88/1.56  --abstr_ref_until_sat                   false
% 7.88/1.56  --abstr_ref_sig_restrict                funpre
% 7.88/1.56  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.56  --abstr_ref_under                       []
% 7.88/1.56  
% 7.88/1.56  ------ SAT Options
% 7.88/1.56  
% 7.88/1.56  --sat_mode                              false
% 7.88/1.56  --sat_fm_restart_options                ""
% 7.88/1.56  --sat_gr_def                            false
% 7.88/1.56  --sat_epr_types                         true
% 7.88/1.56  --sat_non_cyclic_types                  false
% 7.88/1.56  --sat_finite_models                     false
% 7.88/1.56  --sat_fm_lemmas                         false
% 7.88/1.56  --sat_fm_prep                           false
% 7.88/1.56  --sat_fm_uc_incr                        true
% 7.88/1.56  --sat_out_model                         small
% 7.88/1.56  --sat_out_clauses                       false
% 7.88/1.56  
% 7.88/1.56  ------ QBF Options
% 7.88/1.56  
% 7.88/1.56  --qbf_mode                              false
% 7.88/1.56  --qbf_elim_univ                         false
% 7.88/1.56  --qbf_dom_inst                          none
% 7.88/1.56  --qbf_dom_pre_inst                      false
% 7.88/1.56  --qbf_sk_in                             false
% 7.88/1.56  --qbf_pred_elim                         true
% 7.88/1.56  --qbf_split                             512
% 7.88/1.56  
% 7.88/1.56  ------ BMC1 Options
% 7.88/1.56  
% 7.88/1.56  --bmc1_incremental                      false
% 7.88/1.56  --bmc1_axioms                           reachable_all
% 7.88/1.56  --bmc1_min_bound                        0
% 7.88/1.56  --bmc1_max_bound                        -1
% 7.88/1.56  --bmc1_max_bound_default                -1
% 7.88/1.56  --bmc1_symbol_reachability              true
% 7.88/1.56  --bmc1_property_lemmas                  false
% 7.88/1.56  --bmc1_k_induction                      false
% 7.88/1.56  --bmc1_non_equiv_states                 false
% 7.88/1.56  --bmc1_deadlock                         false
% 7.88/1.56  --bmc1_ucm                              false
% 7.88/1.56  --bmc1_add_unsat_core                   none
% 7.88/1.56  --bmc1_unsat_core_children              false
% 7.88/1.56  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.56  --bmc1_out_stat                         full
% 7.88/1.56  --bmc1_ground_init                      false
% 7.88/1.56  --bmc1_pre_inst_next_state              false
% 7.88/1.56  --bmc1_pre_inst_state                   false
% 7.88/1.56  --bmc1_pre_inst_reach_state             false
% 7.88/1.56  --bmc1_out_unsat_core                   false
% 7.88/1.56  --bmc1_aig_witness_out                  false
% 7.88/1.56  --bmc1_verbose                          false
% 7.88/1.56  --bmc1_dump_clauses_tptp                false
% 7.88/1.56  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.56  --bmc1_dump_file                        -
% 7.88/1.56  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.56  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.56  --bmc1_ucm_extend_mode                  1
% 7.88/1.56  --bmc1_ucm_init_mode                    2
% 7.88/1.56  --bmc1_ucm_cone_mode                    none
% 7.88/1.56  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.56  --bmc1_ucm_relax_model                  4
% 7.88/1.56  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.56  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.56  --bmc1_ucm_layered_model                none
% 7.88/1.56  --bmc1_ucm_max_lemma_size               10
% 7.88/1.56  
% 7.88/1.56  ------ AIG Options
% 7.88/1.56  
% 7.88/1.56  --aig_mode                              false
% 7.88/1.56  
% 7.88/1.56  ------ Instantiation Options
% 7.88/1.56  
% 7.88/1.56  --instantiation_flag                    true
% 7.88/1.56  --inst_sos_flag                         false
% 7.88/1.56  --inst_sos_phase                        true
% 7.88/1.56  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.56  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.56  --inst_lit_sel_side                     num_symb
% 7.88/1.56  --inst_solver_per_active                1400
% 7.88/1.56  --inst_solver_calls_frac                1.
% 7.88/1.56  --inst_passive_queue_type               priority_queues
% 7.88/1.56  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.56  --inst_passive_queues_freq              [25;2]
% 7.88/1.56  --inst_dismatching                      true
% 7.88/1.56  --inst_eager_unprocessed_to_passive     true
% 7.88/1.56  --inst_prop_sim_given                   true
% 7.88/1.56  --inst_prop_sim_new                     false
% 7.88/1.56  --inst_subs_new                         false
% 7.88/1.56  --inst_eq_res_simp                      false
% 7.88/1.56  --inst_subs_given                       false
% 7.88/1.56  --inst_orphan_elimination               true
% 7.88/1.56  --inst_learning_loop_flag               true
% 7.88/1.56  --inst_learning_start                   3000
% 7.88/1.56  --inst_learning_factor                  2
% 7.88/1.56  --inst_start_prop_sim_after_learn       3
% 7.88/1.56  --inst_sel_renew                        solver
% 7.88/1.56  --inst_lit_activity_flag                true
% 7.88/1.56  --inst_restr_to_given                   false
% 7.88/1.56  --inst_activity_threshold               500
% 7.88/1.56  --inst_out_proof                        true
% 7.88/1.56  
% 7.88/1.56  ------ Resolution Options
% 7.88/1.56  
% 7.88/1.56  --resolution_flag                       true
% 7.88/1.56  --res_lit_sel                           adaptive
% 7.88/1.56  --res_lit_sel_side                      none
% 7.88/1.56  --res_ordering                          kbo
% 7.88/1.56  --res_to_prop_solver                    active
% 7.88/1.56  --res_prop_simpl_new                    false
% 7.88/1.56  --res_prop_simpl_given                  true
% 7.88/1.56  --res_passive_queue_type                priority_queues
% 7.88/1.56  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.56  --res_passive_queues_freq               [15;5]
% 7.88/1.56  --res_forward_subs                      full
% 7.88/1.56  --res_backward_subs                     full
% 7.88/1.56  --res_forward_subs_resolution           true
% 7.88/1.56  --res_backward_subs_resolution          true
% 7.88/1.56  --res_orphan_elimination                true
% 7.88/1.56  --res_time_limit                        2.
% 7.88/1.56  --res_out_proof                         true
% 7.88/1.56  
% 7.88/1.56  ------ Superposition Options
% 7.88/1.56  
% 7.88/1.56  --superposition_flag                    true
% 7.88/1.56  --sup_passive_queue_type                priority_queues
% 7.88/1.56  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.56  --sup_passive_queues_freq               [1;4]
% 7.88/1.56  --demod_completeness_check              fast
% 7.88/1.56  --demod_use_ground                      true
% 7.88/1.56  --sup_to_prop_solver                    passive
% 7.88/1.56  --sup_prop_simpl_new                    true
% 7.88/1.56  --sup_prop_simpl_given                  true
% 7.88/1.56  --sup_fun_splitting                     false
% 7.88/1.56  --sup_smt_interval                      50000
% 7.88/1.56  
% 7.88/1.56  ------ Superposition Simplification Setup
% 7.88/1.56  
% 7.88/1.56  --sup_indices_passive                   []
% 7.88/1.56  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.56  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.56  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.56  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.56  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.56  --sup_full_bw                           [BwDemod]
% 7.88/1.56  --sup_immed_triv                        [TrivRules]
% 7.88/1.56  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.56  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.56  --sup_immed_bw_main                     []
% 7.88/1.56  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.56  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.56  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.56  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.56  
% 7.88/1.56  ------ Combination Options
% 7.88/1.56  
% 7.88/1.56  --comb_res_mult                         3
% 7.88/1.56  --comb_sup_mult                         2
% 7.88/1.56  --comb_inst_mult                        10
% 7.88/1.56  
% 7.88/1.56  ------ Debug Options
% 7.88/1.56  
% 7.88/1.56  --dbg_backtrace                         false
% 7.88/1.56  --dbg_dump_prop_clauses                 false
% 7.88/1.56  --dbg_dump_prop_clauses_file            -
% 7.88/1.56  --dbg_out_stat                          false
% 7.88/1.56  
% 7.88/1.56  
% 7.88/1.56  
% 7.88/1.56  
% 7.88/1.56  ------ Proving...
% 7.88/1.56  
% 7.88/1.56  
% 7.88/1.56  % SZS status Theorem for theBenchmark.p
% 7.88/1.56  
% 7.88/1.56  % SZS output start CNFRefutation for theBenchmark.p
% 7.88/1.56  
% 7.88/1.56  fof(f11,axiom,(
% 7.88/1.56    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f21,plain,(
% 7.88/1.56    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.88/1.56    inference(ennf_transformation,[],[f11])).
% 7.88/1.56  
% 7.88/1.56  fof(f22,plain,(
% 7.88/1.56    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.88/1.56    inference(flattening,[],[f21])).
% 7.88/1.56  
% 7.88/1.56  fof(f43,plain,(
% 7.88/1.56    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.88/1.56    inference(cnf_transformation,[],[f22])).
% 7.88/1.56  
% 7.88/1.56  fof(f5,axiom,(
% 7.88/1.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f37,plain,(
% 7.88/1.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.88/1.56    inference(cnf_transformation,[],[f5])).
% 7.88/1.56  
% 7.88/1.56  fof(f14,conjecture,(
% 7.88/1.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f15,negated_conjecture,(
% 7.88/1.56    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 7.88/1.56    inference(negated_conjecture,[],[f14])).
% 7.88/1.56  
% 7.88/1.56  fof(f25,plain,(
% 7.88/1.56    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 7.88/1.56    inference(ennf_transformation,[],[f15])).
% 7.88/1.56  
% 7.88/1.56  fof(f26,plain,(
% 7.88/1.56    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 7.88/1.56    inference(flattening,[],[f25])).
% 7.88/1.56  
% 7.88/1.56  fof(f29,plain,(
% 7.88/1.56    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 7.88/1.56    introduced(choice_axiom,[])).
% 7.88/1.56  
% 7.88/1.56  fof(f30,plain,(
% 7.88/1.56    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 7.88/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f29])).
% 7.88/1.56  
% 7.88/1.56  fof(f46,plain,(
% 7.88/1.56    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 7.88/1.56    inference(cnf_transformation,[],[f30])).
% 7.88/1.56  
% 7.88/1.56  fof(f6,axiom,(
% 7.88/1.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f38,plain,(
% 7.88/1.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.88/1.56    inference(cnf_transformation,[],[f6])).
% 7.88/1.56  
% 7.88/1.56  fof(f3,axiom,(
% 7.88/1.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f16,plain,(
% 7.88/1.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.88/1.56    inference(ennf_transformation,[],[f3])).
% 7.88/1.56  
% 7.88/1.56  fof(f35,plain,(
% 7.88/1.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.88/1.56    inference(cnf_transformation,[],[f16])).
% 7.88/1.56  
% 7.88/1.56  fof(f2,axiom,(
% 7.88/1.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f28,plain,(
% 7.88/1.56    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.88/1.56    inference(nnf_transformation,[],[f2])).
% 7.88/1.56  
% 7.88/1.56  fof(f34,plain,(
% 7.88/1.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.88/1.56    inference(cnf_transformation,[],[f28])).
% 7.88/1.56  
% 7.88/1.56  fof(f33,plain,(
% 7.88/1.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 7.88/1.56    inference(cnf_transformation,[],[f28])).
% 7.88/1.56  
% 7.88/1.56  fof(f7,axiom,(
% 7.88/1.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f18,plain,(
% 7.88/1.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.88/1.56    inference(ennf_transformation,[],[f7])).
% 7.88/1.56  
% 7.88/1.56  fof(f39,plain,(
% 7.88/1.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.88/1.56    inference(cnf_transformation,[],[f18])).
% 7.88/1.56  
% 7.88/1.56  fof(f12,axiom,(
% 7.88/1.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f44,plain,(
% 7.88/1.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.88/1.56    inference(cnf_transformation,[],[f12])).
% 7.88/1.56  
% 7.88/1.56  fof(f47,plain,(
% 7.88/1.56    r1_xboole_0(sK2,sK0)),
% 7.88/1.56    inference(cnf_transformation,[],[f30])).
% 7.88/1.56  
% 7.88/1.56  fof(f1,axiom,(
% 7.88/1.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f27,plain,(
% 7.88/1.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.88/1.56    inference(nnf_transformation,[],[f1])).
% 7.88/1.56  
% 7.88/1.56  fof(f31,plain,(
% 7.88/1.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.88/1.56    inference(cnf_transformation,[],[f27])).
% 7.88/1.56  
% 7.88/1.56  fof(f9,axiom,(
% 7.88/1.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f41,plain,(
% 7.88/1.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.88/1.56    inference(cnf_transformation,[],[f9])).
% 7.88/1.56  
% 7.88/1.56  fof(f51,plain,(
% 7.88/1.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.88/1.56    inference(definition_unfolding,[],[f31,f41])).
% 7.88/1.56  
% 7.88/1.56  fof(f8,axiom,(
% 7.88/1.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f40,plain,(
% 7.88/1.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.88/1.56    inference(cnf_transformation,[],[f8])).
% 7.88/1.56  
% 7.88/1.56  fof(f52,plain,(
% 7.88/1.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.88/1.56    inference(definition_unfolding,[],[f40,f41])).
% 7.88/1.56  
% 7.88/1.56  fof(f4,axiom,(
% 7.88/1.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.88/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.56  
% 7.88/1.56  fof(f17,plain,(
% 7.88/1.56    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 7.88/1.56    inference(ennf_transformation,[],[f4])).
% 7.88/1.56  
% 7.88/1.56  fof(f36,plain,(
% 7.88/1.56    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 7.88/1.56    inference(cnf_transformation,[],[f17])).
% 7.88/1.56  
% 7.88/1.56  fof(f49,plain,(
% 7.88/1.56    sK1 != sK2),
% 7.88/1.56    inference(cnf_transformation,[],[f30])).
% 7.88/1.56  
% 7.88/1.56  fof(f48,plain,(
% 7.88/1.56    r1_xboole_0(sK3,sK1)),
% 7.88/1.56    inference(cnf_transformation,[],[f30])).
% 7.88/1.56  
% 7.88/1.56  cnf(c_11,plain,
% 7.88/1.56      ( ~ r1_tarski(X0,X1)
% 7.88/1.56      | ~ r1_tarski(X0,X2)
% 7.88/1.56      | ~ r1_xboole_0(X1,X2)
% 7.88/1.56      | k1_xboole_0 = X0 ),
% 7.88/1.56      inference(cnf_transformation,[],[f43]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_3233,plain,
% 7.88/1.56      ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
% 7.88/1.56      | ~ r1_tarski(k4_xboole_0(sK1,sK2),X1)
% 7.88/1.56      | ~ r1_xboole_0(X0,X1)
% 7.88/1.56      | k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_11]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_9096,plain,
% 7.88/1.56      ( ~ r1_tarski(k4_xboole_0(sK1,sK2),X0)
% 7.88/1.56      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
% 7.88/1.56      | ~ r1_xboole_0(X0,sK1)
% 7.88/1.56      | k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_3233]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_31140,plain,
% 7.88/1.56      ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK3)
% 7.88/1.56      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
% 7.88/1.56      | ~ r1_xboole_0(sK3,sK1)
% 7.88/1.56      | k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_9096]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_6,plain,
% 7.88/1.56      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.88/1.56      inference(cnf_transformation,[],[f37]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_685,plain,
% 7.88/1.56      ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_6]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_13260,plain,
% 7.88/1.56      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_685]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_17,negated_conjecture,
% 7.88/1.56      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 7.88/1.56      inference(cnf_transformation,[],[f46]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_7,plain,
% 7.88/1.56      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.88/1.56      inference(cnf_transformation,[],[f38]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_499,plain,
% 7.88/1.56      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.88/1.56      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_1153,plain,
% 7.88/1.56      ( r1_tarski(X0,X0) = iProver_top ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_7,c_499]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_4,plain,
% 7.88/1.56      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.88/1.56      inference(cnf_transformation,[],[f35]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_500,plain,
% 7.88/1.56      ( r1_tarski(X0,X1) != iProver_top
% 7.88/1.56      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 7.88/1.56      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_2,plain,
% 7.88/1.56      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.88/1.56      inference(cnf_transformation,[],[f34]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_502,plain,
% 7.88/1.56      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.88/1.56      | r1_tarski(X0,X1) != iProver_top ),
% 7.88/1.56      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_1756,plain,
% 7.88/1.56      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k1_xboole_0
% 7.88/1.56      | r1_tarski(X0,X2) != iProver_top ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_500,c_502]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_6283,plain,
% 7.88/1.56      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_1153,c_1756]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_6437,plain,
% 7.88/1.56      ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_17,c_6283]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_3,plain,
% 7.88/1.56      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.88/1.56      inference(cnf_transformation,[],[f33]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_501,plain,
% 7.88/1.56      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 7.88/1.56      | r1_tarski(X0,X1) = iProver_top ),
% 7.88/1.56      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_6890,plain,
% 7.88/1.56      ( r1_tarski(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_6437,c_501]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_8,plain,
% 7.88/1.56      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.88/1.56      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.88/1.56      inference(cnf_transformation,[],[f39]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_498,plain,
% 7.88/1.56      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.88/1.56      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 7.88/1.56      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_7183,plain,
% 7.88/1.56      ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_6890,c_498]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_7219,plain,
% 7.88/1.56      ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) ),
% 7.88/1.56      inference(predicate_to_equality_rev,[status(thm)],[c_7183]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_12,plain,
% 7.88/1.56      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.88/1.56      inference(cnf_transformation,[],[f44]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_495,plain,
% 7.88/1.56      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.88/1.56      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_2535,plain,
% 7.88/1.56      ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
% 7.88/1.56      | r1_tarski(k4_xboole_0(X0,sK0),sK1) = iProver_top ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_17,c_498]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_2772,plain,
% 7.88/1.56      ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_495,c_2535]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_16,negated_conjecture,
% 7.88/1.56      ( r1_xboole_0(sK2,sK0) ),
% 7.88/1.56      inference(cnf_transformation,[],[f47]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_492,plain,
% 7.88/1.56      ( r1_xboole_0(sK2,sK0) = iProver_top ),
% 7.88/1.56      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_1,plain,
% 7.88/1.56      ( ~ r1_xboole_0(X0,X1)
% 7.88/1.56      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.88/1.56      inference(cnf_transformation,[],[f51]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_503,plain,
% 7.88/1.56      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.88/1.56      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.88/1.56      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_1783,plain,
% 7.88/1.56      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_492,c_503]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_9,plain,
% 7.88/1.56      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.88/1.56      inference(cnf_transformation,[],[f52]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_5202,plain,
% 7.88/1.56      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 7.88/1.56      inference(superposition,[status(thm)],[c_1783,c_9]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_5204,plain,
% 7.88/1.56      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 7.88/1.56      inference(demodulation,[status(thm)],[c_5202,c_7]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_5901,plain,
% 7.88/1.56      ( r1_tarski(sK2,sK1) = iProver_top ),
% 7.88/1.56      inference(light_normalisation,[status(thm)],[c_2772,c_5204]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_824,plain,
% 7.88/1.56      ( ~ r1_tarski(X0,sK1) | k4_xboole_0(X0,sK1) = k1_xboole_0 ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_2]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_5423,plain,
% 7.88/1.56      ( ~ r1_tarski(sK2,sK1) | k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_824]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_5427,plain,
% 7.88/1.56      ( k4_xboole_0(sK2,sK1) = k1_xboole_0
% 7.88/1.56      | r1_tarski(sK2,sK1) != iProver_top ),
% 7.88/1.56      inference(predicate_to_equality,[status(thm)],[c_5423]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_171,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_819,plain,
% 7.88/1.56      ( X0 != X1
% 7.88/1.56      | k4_xboole_0(sK1,sK2) != X1
% 7.88/1.56      | k4_xboole_0(sK1,sK2) = X0 ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_171]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_1514,plain,
% 7.88/1.56      ( X0 != k4_xboole_0(sK1,sK2)
% 7.88/1.56      | k4_xboole_0(sK1,sK2) = X0
% 7.88/1.56      | k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_819]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_1515,plain,
% 7.88/1.56      ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)
% 7.88/1.56      | k4_xboole_0(sK1,sK2) = k1_xboole_0
% 7.88/1.56      | k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_1514]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_170,plain,( X0 = X0 ),theory(equality) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_818,plain,
% 7.88/1.56      ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_170]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_672,plain,
% 7.88/1.56      ( k4_xboole_0(sK2,sK1) != X0
% 7.88/1.56      | k4_xboole_0(sK1,sK2) != X0
% 7.88/1.56      | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_171]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_673,plain,
% 7.88/1.56      ( k4_xboole_0(sK2,sK1) != k1_xboole_0
% 7.88/1.56      | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1)
% 7.88/1.56      | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_672]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_5,plain,
% 7.88/1.56      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 7.88/1.56      inference(cnf_transformation,[],[f36]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_631,plain,
% 7.88/1.56      ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK2,sK1) | sK1 = sK2 ),
% 7.88/1.56      inference(instantiation,[status(thm)],[c_5]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_14,negated_conjecture,
% 7.88/1.56      ( sK1 != sK2 ),
% 7.88/1.56      inference(cnf_transformation,[],[f49]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(c_15,negated_conjecture,
% 7.88/1.56      ( r1_xboole_0(sK3,sK1) ),
% 7.88/1.56      inference(cnf_transformation,[],[f48]) ).
% 7.88/1.56  
% 7.88/1.56  cnf(contradiction,plain,
% 7.88/1.56      ( $false ),
% 7.88/1.56      inference(minisat,
% 7.88/1.56                [status(thm)],
% 7.88/1.56                [c_31140,c_13260,c_7219,c_5901,c_5427,c_1515,c_818,c_673,
% 7.88/1.56                 c_631,c_14,c_15]) ).
% 7.88/1.56  
% 7.88/1.56  
% 7.88/1.56  % SZS output end CNFRefutation for theBenchmark.p
% 7.88/1.56  
% 7.88/1.56  ------                               Statistics
% 7.88/1.56  
% 7.88/1.56  ------ Selected
% 7.88/1.56  
% 7.88/1.56  total_time:                             0.777
% 7.88/1.56  
%------------------------------------------------------------------------------
