%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:29 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 293 expanded)
%              Number of clauses        :   60 ( 109 expanded)
%              Number of leaves         :   16 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  223 ( 825 expanded)
%              Number of equality atoms :  113 ( 259 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k1_xboole_0 != sK3
      & r1_xboole_0(sK4,sK5)
      & r1_tarski(sK3,sK5)
      & r1_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k1_xboole_0 != sK3
    & r1_xboole_0(sK4,sK5)
    & r1_tarski(sK3,sK5)
    & r1_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f27])).

fof(f43,plain,(
    r1_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f23])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    r1_tarski(sK3,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK2(X0,X1,X2),X0)
        & r1_tarski(sK2(X0,X1,X2),X2)
        & r1_tarski(sK2(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK2(X0,X1,X2),X0)
        & r1_tarski(sK2(X0,X1,X2),X2)
        & r1_tarski(sK2(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK2(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(sK2(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f41,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_xboole_0(X0,X1)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_383,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_391,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1107,plain,
    ( r1_xboole_0(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_383,c_391])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_388,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_390,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1480,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_388,c_390])).

cnf(c_1666,plain,
    ( k3_xboole_0(sK5,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1107,c_1480])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK3,sK5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_382,plain,
    ( r1_tarski(sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(sK2(X0,X2,X1),X2)
    | k3_xboole_0(X2,X1) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_385,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(sK2(X2,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(sK2(X0,X2,X1),X0)
    | k3_xboole_0(X2,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_387,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(sK2(X2,X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2053,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_385,c_387])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_384,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_585,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_384])).

cnf(c_13746,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k3_xboole_0(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2053,c_585])).

cnf(c_13747,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_13746])).

cnf(c_13753,plain,
    ( k3_xboole_0(sK3,sK5) = sK3 ),
    inference(superposition,[status(thm)],[c_382,c_13747])).

cnf(c_5,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13871,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK5,X0)) = k3_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_13753,c_5])).

cnf(c_14385,plain,
    ( k3_xboole_0(sK3,sK4) = k3_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1666,c_13871])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_381,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13754,plain,
    ( k3_xboole_0(sK3,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_381,c_13747])).

cnf(c_14447,plain,
    ( k3_xboole_0(sK3,k1_xboole_0) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_14385,c_13754])).

cnf(c_1665,plain,
    ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_383,c_1480])).

cnf(c_1481,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3))) != iProver_top
    | r1_xboole_0(k3_xboole_0(X1,X2),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_390])).

cnf(c_11702,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top
    | r1_xboole_0(k3_xboole_0(X1,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1481])).

cnf(c_13110,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0
    | r1_xboole_0(k3_xboole_0(X0,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_388,c_11702])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_389,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1460,plain,
    ( r2_hidden(sK0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_389])).

cnf(c_6711,plain,
    ( r2_hidden(sK0(k3_xboole_0(X0,sK4),sK5),k3_xboole_0(X0,k1_xboole_0)) = iProver_top
    | r1_xboole_0(k3_xboole_0(X0,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1460])).

cnf(c_7923,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k3_xboole_0(X0,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6711,c_390])).

cnf(c_11,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_807,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_11,c_4])).

cnf(c_988,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_807])).

cnf(c_1461,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_389])).

cnf(c_1732,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_390])).

cnf(c_18,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1813,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1732,c_18])).

cnf(c_9349,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1461,c_1813])).

cnf(c_9354,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9349,c_391])).

cnf(c_13170,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13110,c_7923,c_9354])).

cnf(c_14448,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14447,c_13170])).

cnf(c_165,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_493,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_494,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_164,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_179,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14448,c_494,c_179,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.65/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/1.00  
% 3.65/1.00  ------  iProver source info
% 3.65/1.00  
% 3.65/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.65/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/1.00  git: non_committed_changes: false
% 3.65/1.00  git: last_make_outside_of_git: false
% 3.65/1.00  
% 3.65/1.00  ------ 
% 3.65/1.00  
% 3.65/1.00  ------ Input Options
% 3.65/1.00  
% 3.65/1.00  --out_options                           all
% 3.65/1.00  --tptp_safe_out                         true
% 3.65/1.00  --problem_path                          ""
% 3.65/1.00  --include_path                          ""
% 3.65/1.00  --clausifier                            res/vclausify_rel
% 3.65/1.00  --clausifier_options                    --mode clausify
% 3.65/1.00  --stdin                                 false
% 3.65/1.00  --stats_out                             all
% 3.65/1.00  
% 3.65/1.00  ------ General Options
% 3.65/1.00  
% 3.65/1.00  --fof                                   false
% 3.65/1.00  --time_out_real                         305.
% 3.65/1.00  --time_out_virtual                      -1.
% 3.65/1.00  --symbol_type_check                     false
% 3.65/1.00  --clausify_out                          false
% 3.65/1.00  --sig_cnt_out                           false
% 3.65/1.00  --trig_cnt_out                          false
% 3.65/1.00  --trig_cnt_out_tolerance                1.
% 3.65/1.00  --trig_cnt_out_sk_spl                   false
% 3.65/1.00  --abstr_cl_out                          false
% 3.65/1.00  
% 3.65/1.00  ------ Global Options
% 3.65/1.00  
% 3.65/1.00  --schedule                              default
% 3.65/1.00  --add_important_lit                     false
% 3.65/1.00  --prop_solver_per_cl                    1000
% 3.65/1.00  --min_unsat_core                        false
% 3.65/1.00  --soft_assumptions                      false
% 3.65/1.00  --soft_lemma_size                       3
% 3.65/1.00  --prop_impl_unit_size                   0
% 3.65/1.00  --prop_impl_unit                        []
% 3.65/1.00  --share_sel_clauses                     true
% 3.65/1.00  --reset_solvers                         false
% 3.65/1.00  --bc_imp_inh                            [conj_cone]
% 3.65/1.00  --conj_cone_tolerance                   3.
% 3.65/1.00  --extra_neg_conj                        none
% 3.65/1.00  --large_theory_mode                     true
% 3.65/1.00  --prolific_symb_bound                   200
% 3.65/1.00  --lt_threshold                          2000
% 3.65/1.00  --clause_weak_htbl                      true
% 3.65/1.00  --gc_record_bc_elim                     false
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing Options
% 3.65/1.00  
% 3.65/1.00  --preprocessing_flag                    true
% 3.65/1.00  --time_out_prep_mult                    0.1
% 3.65/1.00  --splitting_mode                        input
% 3.65/1.00  --splitting_grd                         true
% 3.65/1.00  --splitting_cvd                         false
% 3.65/1.00  --splitting_cvd_svl                     false
% 3.65/1.00  --splitting_nvd                         32
% 3.65/1.00  --sub_typing                            true
% 3.65/1.00  --prep_gs_sim                           true
% 3.65/1.00  --prep_unflatten                        true
% 3.65/1.00  --prep_res_sim                          true
% 3.65/1.00  --prep_upred                            true
% 3.65/1.00  --prep_sem_filter                       exhaustive
% 3.65/1.00  --prep_sem_filter_out                   false
% 3.65/1.00  --pred_elim                             true
% 3.65/1.00  --res_sim_input                         true
% 3.65/1.00  --eq_ax_congr_red                       true
% 3.65/1.00  --pure_diseq_elim                       true
% 3.65/1.00  --brand_transform                       false
% 3.65/1.00  --non_eq_to_eq                          false
% 3.65/1.00  --prep_def_merge                        true
% 3.65/1.00  --prep_def_merge_prop_impl              false
% 3.65/1.00  --prep_def_merge_mbd                    true
% 3.65/1.00  --prep_def_merge_tr_red                 false
% 3.65/1.00  --prep_def_merge_tr_cl                  false
% 3.65/1.00  --smt_preprocessing                     true
% 3.65/1.00  --smt_ac_axioms                         fast
% 3.65/1.00  --preprocessed_out                      false
% 3.65/1.00  --preprocessed_stats                    false
% 3.65/1.00  
% 3.65/1.00  ------ Abstraction refinement Options
% 3.65/1.00  
% 3.65/1.00  --abstr_ref                             []
% 3.65/1.00  --abstr_ref_prep                        false
% 3.65/1.00  --abstr_ref_until_sat                   false
% 3.65/1.00  --abstr_ref_sig_restrict                funpre
% 3.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.00  --abstr_ref_under                       []
% 3.65/1.00  
% 3.65/1.00  ------ SAT Options
% 3.65/1.00  
% 3.65/1.00  --sat_mode                              false
% 3.65/1.00  --sat_fm_restart_options                ""
% 3.65/1.00  --sat_gr_def                            false
% 3.65/1.00  --sat_epr_types                         true
% 3.65/1.00  --sat_non_cyclic_types                  false
% 3.65/1.00  --sat_finite_models                     false
% 3.65/1.00  --sat_fm_lemmas                         false
% 3.65/1.00  --sat_fm_prep                           false
% 3.65/1.00  --sat_fm_uc_incr                        true
% 3.65/1.00  --sat_out_model                         small
% 3.65/1.00  --sat_out_clauses                       false
% 3.65/1.00  
% 3.65/1.00  ------ QBF Options
% 3.65/1.00  
% 3.65/1.00  --qbf_mode                              false
% 3.65/1.00  --qbf_elim_univ                         false
% 3.65/1.00  --qbf_dom_inst                          none
% 3.65/1.00  --qbf_dom_pre_inst                      false
% 3.65/1.00  --qbf_sk_in                             false
% 3.65/1.00  --qbf_pred_elim                         true
% 3.65/1.00  --qbf_split                             512
% 3.65/1.00  
% 3.65/1.00  ------ BMC1 Options
% 3.65/1.00  
% 3.65/1.00  --bmc1_incremental                      false
% 3.65/1.00  --bmc1_axioms                           reachable_all
% 3.65/1.00  --bmc1_min_bound                        0
% 3.65/1.00  --bmc1_max_bound                        -1
% 3.65/1.00  --bmc1_max_bound_default                -1
% 3.65/1.00  --bmc1_symbol_reachability              true
% 3.65/1.00  --bmc1_property_lemmas                  false
% 3.65/1.00  --bmc1_k_induction                      false
% 3.65/1.00  --bmc1_non_equiv_states                 false
% 3.65/1.00  --bmc1_deadlock                         false
% 3.65/1.00  --bmc1_ucm                              false
% 3.65/1.00  --bmc1_add_unsat_core                   none
% 3.65/1.00  --bmc1_unsat_core_children              false
% 3.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.00  --bmc1_out_stat                         full
% 3.65/1.00  --bmc1_ground_init                      false
% 3.65/1.00  --bmc1_pre_inst_next_state              false
% 3.65/1.00  --bmc1_pre_inst_state                   false
% 3.65/1.00  --bmc1_pre_inst_reach_state             false
% 3.65/1.00  --bmc1_out_unsat_core                   false
% 3.65/1.00  --bmc1_aig_witness_out                  false
% 3.65/1.00  --bmc1_verbose                          false
% 3.65/1.00  --bmc1_dump_clauses_tptp                false
% 3.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.00  --bmc1_dump_file                        -
% 3.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.00  --bmc1_ucm_extend_mode                  1
% 3.65/1.00  --bmc1_ucm_init_mode                    2
% 3.65/1.00  --bmc1_ucm_cone_mode                    none
% 3.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.00  --bmc1_ucm_relax_model                  4
% 3.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.00  --bmc1_ucm_layered_model                none
% 3.65/1.00  --bmc1_ucm_max_lemma_size               10
% 3.65/1.00  
% 3.65/1.00  ------ AIG Options
% 3.65/1.00  
% 3.65/1.00  --aig_mode                              false
% 3.65/1.00  
% 3.65/1.00  ------ Instantiation Options
% 3.65/1.00  
% 3.65/1.00  --instantiation_flag                    true
% 3.65/1.00  --inst_sos_flag                         false
% 3.65/1.00  --inst_sos_phase                        true
% 3.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel_side                     num_symb
% 3.65/1.00  --inst_solver_per_active                1400
% 3.65/1.00  --inst_solver_calls_frac                1.
% 3.65/1.00  --inst_passive_queue_type               priority_queues
% 3.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.00  --inst_passive_queues_freq              [25;2]
% 3.65/1.00  --inst_dismatching                      true
% 3.65/1.00  --inst_eager_unprocessed_to_passive     true
% 3.65/1.00  --inst_prop_sim_given                   true
% 3.65/1.00  --inst_prop_sim_new                     false
% 3.65/1.00  --inst_subs_new                         false
% 3.65/1.00  --inst_eq_res_simp                      false
% 3.65/1.00  --inst_subs_given                       false
% 3.65/1.00  --inst_orphan_elimination               true
% 3.65/1.00  --inst_learning_loop_flag               true
% 3.65/1.00  --inst_learning_start                   3000
% 3.65/1.00  --inst_learning_factor                  2
% 3.65/1.00  --inst_start_prop_sim_after_learn       3
% 3.65/1.00  --inst_sel_renew                        solver
% 3.65/1.00  --inst_lit_activity_flag                true
% 3.65/1.00  --inst_restr_to_given                   false
% 3.65/1.00  --inst_activity_threshold               500
% 3.65/1.00  --inst_out_proof                        true
% 3.65/1.00  
% 3.65/1.00  ------ Resolution Options
% 3.65/1.00  
% 3.65/1.00  --resolution_flag                       true
% 3.65/1.00  --res_lit_sel                           adaptive
% 3.65/1.00  --res_lit_sel_side                      none
% 3.65/1.00  --res_ordering                          kbo
% 3.65/1.00  --res_to_prop_solver                    active
% 3.65/1.00  --res_prop_simpl_new                    false
% 3.65/1.00  --res_prop_simpl_given                  true
% 3.65/1.00  --res_passive_queue_type                priority_queues
% 3.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.00  --res_passive_queues_freq               [15;5]
% 3.65/1.00  --res_forward_subs                      full
% 3.65/1.00  --res_backward_subs                     full
% 3.65/1.00  --res_forward_subs_resolution           true
% 3.65/1.00  --res_backward_subs_resolution          true
% 3.65/1.00  --res_orphan_elimination                true
% 3.65/1.00  --res_time_limit                        2.
% 3.65/1.00  --res_out_proof                         true
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Options
% 3.65/1.00  
% 3.65/1.00  --superposition_flag                    true
% 3.65/1.00  --sup_passive_queue_type                priority_queues
% 3.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.00  --demod_completeness_check              fast
% 3.65/1.00  --demod_use_ground                      true
% 3.65/1.00  --sup_to_prop_solver                    passive
% 3.65/1.00  --sup_prop_simpl_new                    true
% 3.65/1.00  --sup_prop_simpl_given                  true
% 3.65/1.00  --sup_fun_splitting                     false
% 3.65/1.00  --sup_smt_interval                      50000
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Simplification Setup
% 3.65/1.00  
% 3.65/1.00  --sup_indices_passive                   []
% 3.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.00  --sup_full_bw                           [BwDemod]
% 3.65/1.00  --sup_immed_triv                        [TrivRules]
% 3.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.00  --sup_immed_bw_main                     []
% 3.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/1.00  
% 3.65/1.00  ------ Combination Options
% 3.65/1.00  
% 3.65/1.00  --comb_res_mult                         3
% 3.65/1.00  --comb_sup_mult                         2
% 3.65/1.00  --comb_inst_mult                        10
% 3.65/1.00  
% 3.65/1.00  ------ Debug Options
% 3.65/1.00  
% 3.65/1.00  --dbg_backtrace                         false
% 3.65/1.00  --dbg_dump_prop_clauses                 false
% 3.65/1.00  --dbg_dump_prop_clauses_file            -
% 3.65/1.00  --dbg_out_stat                          false
% 3.65/1.00  ------ Parsing...
% 3.65/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  ------ Proving...
% 3.65/1.00  ------ Problem Properties 
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  clauses                                 16
% 3.65/1.00  conjectures                             4
% 3.65/1.00  EPR                                     5
% 3.65/1.00  Horn                                    12
% 3.65/1.00  unary                                   8
% 3.65/1.00  binary                                  5
% 3.65/1.00  lits                                    30
% 3.65/1.00  lits eq                                 10
% 3.65/1.00  fd_pure                                 0
% 3.65/1.00  fd_pseudo                               0
% 3.65/1.00  fd_cond                                 2
% 3.65/1.00  fd_pseudo_cond                          3
% 3.65/1.00  AC symbols                              0
% 3.65/1.00  
% 3.65/1.00  ------ Schedule dynamic 5 is on 
% 3.65/1.00  
% 3.65/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ 
% 3.65/1.00  Current options:
% 3.65/1.00  ------ 
% 3.65/1.00  
% 3.65/1.00  ------ Input Options
% 3.65/1.00  
% 3.65/1.00  --out_options                           all
% 3.65/1.00  --tptp_safe_out                         true
% 3.65/1.00  --problem_path                          ""
% 3.65/1.00  --include_path                          ""
% 3.65/1.00  --clausifier                            res/vclausify_rel
% 3.65/1.00  --clausifier_options                    --mode clausify
% 3.65/1.00  --stdin                                 false
% 3.65/1.00  --stats_out                             all
% 3.65/1.00  
% 3.65/1.00  ------ General Options
% 3.65/1.00  
% 3.65/1.00  --fof                                   false
% 3.65/1.00  --time_out_real                         305.
% 3.65/1.00  --time_out_virtual                      -1.
% 3.65/1.00  --symbol_type_check                     false
% 3.65/1.00  --clausify_out                          false
% 3.65/1.00  --sig_cnt_out                           false
% 3.65/1.00  --trig_cnt_out                          false
% 3.65/1.00  --trig_cnt_out_tolerance                1.
% 3.65/1.00  --trig_cnt_out_sk_spl                   false
% 3.65/1.00  --abstr_cl_out                          false
% 3.65/1.00  
% 3.65/1.00  ------ Global Options
% 3.65/1.00  
% 3.65/1.00  --schedule                              default
% 3.65/1.00  --add_important_lit                     false
% 3.65/1.00  --prop_solver_per_cl                    1000
% 3.65/1.00  --min_unsat_core                        false
% 3.65/1.00  --soft_assumptions                      false
% 3.65/1.00  --soft_lemma_size                       3
% 3.65/1.00  --prop_impl_unit_size                   0
% 3.65/1.00  --prop_impl_unit                        []
% 3.65/1.00  --share_sel_clauses                     true
% 3.65/1.00  --reset_solvers                         false
% 3.65/1.00  --bc_imp_inh                            [conj_cone]
% 3.65/1.00  --conj_cone_tolerance                   3.
% 3.65/1.00  --extra_neg_conj                        none
% 3.65/1.00  --large_theory_mode                     true
% 3.65/1.00  --prolific_symb_bound                   200
% 3.65/1.00  --lt_threshold                          2000
% 3.65/1.00  --clause_weak_htbl                      true
% 3.65/1.00  --gc_record_bc_elim                     false
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing Options
% 3.65/1.00  
% 3.65/1.00  --preprocessing_flag                    true
% 3.65/1.00  --time_out_prep_mult                    0.1
% 3.65/1.00  --splitting_mode                        input
% 3.65/1.00  --splitting_grd                         true
% 3.65/1.00  --splitting_cvd                         false
% 3.65/1.00  --splitting_cvd_svl                     false
% 3.65/1.00  --splitting_nvd                         32
% 3.65/1.00  --sub_typing                            true
% 3.65/1.00  --prep_gs_sim                           true
% 3.65/1.00  --prep_unflatten                        true
% 3.65/1.00  --prep_res_sim                          true
% 3.65/1.00  --prep_upred                            true
% 3.65/1.00  --prep_sem_filter                       exhaustive
% 3.65/1.00  --prep_sem_filter_out                   false
% 3.65/1.00  --pred_elim                             true
% 3.65/1.00  --res_sim_input                         true
% 3.65/1.00  --eq_ax_congr_red                       true
% 3.65/1.00  --pure_diseq_elim                       true
% 3.65/1.00  --brand_transform                       false
% 3.65/1.00  --non_eq_to_eq                          false
% 3.65/1.00  --prep_def_merge                        true
% 3.65/1.00  --prep_def_merge_prop_impl              false
% 3.65/1.00  --prep_def_merge_mbd                    true
% 3.65/1.00  --prep_def_merge_tr_red                 false
% 3.65/1.00  --prep_def_merge_tr_cl                  false
% 3.65/1.00  --smt_preprocessing                     true
% 3.65/1.00  --smt_ac_axioms                         fast
% 3.65/1.00  --preprocessed_out                      false
% 3.65/1.00  --preprocessed_stats                    false
% 3.65/1.00  
% 3.65/1.00  ------ Abstraction refinement Options
% 3.65/1.00  
% 3.65/1.00  --abstr_ref                             []
% 3.65/1.00  --abstr_ref_prep                        false
% 3.65/1.00  --abstr_ref_until_sat                   false
% 3.65/1.00  --abstr_ref_sig_restrict                funpre
% 3.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.00  --abstr_ref_under                       []
% 3.65/1.00  
% 3.65/1.00  ------ SAT Options
% 3.65/1.00  
% 3.65/1.00  --sat_mode                              false
% 3.65/1.00  --sat_fm_restart_options                ""
% 3.65/1.00  --sat_gr_def                            false
% 3.65/1.00  --sat_epr_types                         true
% 3.65/1.00  --sat_non_cyclic_types                  false
% 3.65/1.00  --sat_finite_models                     false
% 3.65/1.00  --sat_fm_lemmas                         false
% 3.65/1.00  --sat_fm_prep                           false
% 3.65/1.00  --sat_fm_uc_incr                        true
% 3.65/1.00  --sat_out_model                         small
% 3.65/1.00  --sat_out_clauses                       false
% 3.65/1.00  
% 3.65/1.00  ------ QBF Options
% 3.65/1.00  
% 3.65/1.00  --qbf_mode                              false
% 3.65/1.00  --qbf_elim_univ                         false
% 3.65/1.00  --qbf_dom_inst                          none
% 3.65/1.00  --qbf_dom_pre_inst                      false
% 3.65/1.00  --qbf_sk_in                             false
% 3.65/1.00  --qbf_pred_elim                         true
% 3.65/1.00  --qbf_split                             512
% 3.65/1.00  
% 3.65/1.00  ------ BMC1 Options
% 3.65/1.00  
% 3.65/1.00  --bmc1_incremental                      false
% 3.65/1.00  --bmc1_axioms                           reachable_all
% 3.65/1.00  --bmc1_min_bound                        0
% 3.65/1.00  --bmc1_max_bound                        -1
% 3.65/1.00  --bmc1_max_bound_default                -1
% 3.65/1.00  --bmc1_symbol_reachability              true
% 3.65/1.00  --bmc1_property_lemmas                  false
% 3.65/1.00  --bmc1_k_induction                      false
% 3.65/1.00  --bmc1_non_equiv_states                 false
% 3.65/1.00  --bmc1_deadlock                         false
% 3.65/1.00  --bmc1_ucm                              false
% 3.65/1.00  --bmc1_add_unsat_core                   none
% 3.65/1.00  --bmc1_unsat_core_children              false
% 3.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.00  --bmc1_out_stat                         full
% 3.65/1.00  --bmc1_ground_init                      false
% 3.65/1.00  --bmc1_pre_inst_next_state              false
% 3.65/1.00  --bmc1_pre_inst_state                   false
% 3.65/1.00  --bmc1_pre_inst_reach_state             false
% 3.65/1.00  --bmc1_out_unsat_core                   false
% 3.65/1.00  --bmc1_aig_witness_out                  false
% 3.65/1.00  --bmc1_verbose                          false
% 3.65/1.00  --bmc1_dump_clauses_tptp                false
% 3.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.00  --bmc1_dump_file                        -
% 3.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.00  --bmc1_ucm_extend_mode                  1
% 3.65/1.00  --bmc1_ucm_init_mode                    2
% 3.65/1.00  --bmc1_ucm_cone_mode                    none
% 3.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.00  --bmc1_ucm_relax_model                  4
% 3.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.00  --bmc1_ucm_layered_model                none
% 3.65/1.00  --bmc1_ucm_max_lemma_size               10
% 3.65/1.00  
% 3.65/1.00  ------ AIG Options
% 3.65/1.00  
% 3.65/1.00  --aig_mode                              false
% 3.65/1.00  
% 3.65/1.00  ------ Instantiation Options
% 3.65/1.00  
% 3.65/1.00  --instantiation_flag                    true
% 3.65/1.00  --inst_sos_flag                         false
% 3.65/1.00  --inst_sos_phase                        true
% 3.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel_side                     none
% 3.65/1.00  --inst_solver_per_active                1400
% 3.65/1.00  --inst_solver_calls_frac                1.
% 3.65/1.00  --inst_passive_queue_type               priority_queues
% 3.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.00  --inst_passive_queues_freq              [25;2]
% 3.65/1.00  --inst_dismatching                      true
% 3.65/1.00  --inst_eager_unprocessed_to_passive     true
% 3.65/1.00  --inst_prop_sim_given                   true
% 3.65/1.00  --inst_prop_sim_new                     false
% 3.65/1.00  --inst_subs_new                         false
% 3.65/1.00  --inst_eq_res_simp                      false
% 3.65/1.00  --inst_subs_given                       false
% 3.65/1.00  --inst_orphan_elimination               true
% 3.65/1.00  --inst_learning_loop_flag               true
% 3.65/1.00  --inst_learning_start                   3000
% 3.65/1.00  --inst_learning_factor                  2
% 3.65/1.00  --inst_start_prop_sim_after_learn       3
% 3.65/1.00  --inst_sel_renew                        solver
% 3.65/1.00  --inst_lit_activity_flag                true
% 3.65/1.00  --inst_restr_to_given                   false
% 3.65/1.00  --inst_activity_threshold               500
% 3.65/1.00  --inst_out_proof                        true
% 3.65/1.00  
% 3.65/1.00  ------ Resolution Options
% 3.65/1.00  
% 3.65/1.00  --resolution_flag                       false
% 3.65/1.00  --res_lit_sel                           adaptive
% 3.65/1.00  --res_lit_sel_side                      none
% 3.65/1.00  --res_ordering                          kbo
% 3.65/1.00  --res_to_prop_solver                    active
% 3.65/1.00  --res_prop_simpl_new                    false
% 3.65/1.00  --res_prop_simpl_given                  true
% 3.65/1.00  --res_passive_queue_type                priority_queues
% 3.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.00  --res_passive_queues_freq               [15;5]
% 3.65/1.00  --res_forward_subs                      full
% 3.65/1.00  --res_backward_subs                     full
% 3.65/1.00  --res_forward_subs_resolution           true
% 3.65/1.00  --res_backward_subs_resolution          true
% 3.65/1.00  --res_orphan_elimination                true
% 3.65/1.00  --res_time_limit                        2.
% 3.65/1.00  --res_out_proof                         true
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Options
% 3.65/1.00  
% 3.65/1.00  --superposition_flag                    true
% 3.65/1.00  --sup_passive_queue_type                priority_queues
% 3.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.00  --demod_completeness_check              fast
% 3.65/1.00  --demod_use_ground                      true
% 3.65/1.00  --sup_to_prop_solver                    passive
% 3.65/1.00  --sup_prop_simpl_new                    true
% 3.65/1.00  --sup_prop_simpl_given                  true
% 3.65/1.00  --sup_fun_splitting                     false
% 3.65/1.00  --sup_smt_interval                      50000
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Simplification Setup
% 3.65/1.00  
% 3.65/1.00  --sup_indices_passive                   []
% 3.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.00  --sup_full_bw                           [BwDemod]
% 3.65/1.00  --sup_immed_triv                        [TrivRules]
% 3.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.00  --sup_immed_bw_main                     []
% 3.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/1.00  
% 3.65/1.00  ------ Combination Options
% 3.65/1.00  
% 3.65/1.00  --comb_res_mult                         3
% 3.65/1.00  --comb_sup_mult                         2
% 3.65/1.00  --comb_inst_mult                        10
% 3.65/1.00  
% 3.65/1.00  ------ Debug Options
% 3.65/1.00  
% 3.65/1.00  --dbg_backtrace                         false
% 3.65/1.00  --dbg_dump_prop_clauses                 false
% 3.65/1.00  --dbg_dump_prop_clauses_file            -
% 3.65/1.00  --dbg_out_stat                          false
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS status Theorem for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  fof(f10,conjecture,(
% 3.65/1.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f11,negated_conjecture,(
% 3.65/1.00    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 3.65/1.00    inference(negated_conjecture,[],[f10])).
% 3.65/1.00  
% 3.65/1.00  fof(f19,plain,(
% 3.65/1.00    ? [X0,X1,X2] : (k1_xboole_0 != X0 & (r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)))),
% 3.65/1.00    inference(ennf_transformation,[],[f11])).
% 3.65/1.00  
% 3.65/1.00  fof(f20,plain,(
% 3.65/1.00    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1))),
% 3.65/1.00    inference(flattening,[],[f19])).
% 3.65/1.00  
% 3.65/1.00  fof(f27,plain,(
% 3.65/1.00    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => (k1_xboole_0 != sK3 & r1_xboole_0(sK4,sK5) & r1_tarski(sK3,sK5) & r1_tarski(sK3,sK4))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f28,plain,(
% 3.65/1.00    k1_xboole_0 != sK3 & r1_xboole_0(sK4,sK5) & r1_tarski(sK3,sK5) & r1_tarski(sK3,sK4)),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f27])).
% 3.65/1.00  
% 3.65/1.00  fof(f43,plain,(
% 3.65/1.00    r1_xboole_0(sK4,sK5)),
% 3.65/1.00    inference(cnf_transformation,[],[f28])).
% 3.65/1.00  
% 3.65/1.00  fof(f1,axiom,(
% 3.65/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f13,plain,(
% 3.65/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.65/1.00    inference(ennf_transformation,[],[f1])).
% 3.65/1.00  
% 3.65/1.00  fof(f29,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f13])).
% 3.65/1.00  
% 3.65/1.00  fof(f3,axiom,(
% 3.65/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f15,plain,(
% 3.65/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.65/1.00    inference(ennf_transformation,[],[f3])).
% 3.65/1.00  
% 3.65/1.00  fof(f23,plain,(
% 3.65/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f24,plain,(
% 3.65/1.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f23])).
% 3.65/1.00  
% 3.65/1.00  fof(f32,plain,(
% 3.65/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.65/1.00    inference(cnf_transformation,[],[f24])).
% 3.65/1.00  
% 3.65/1.00  fof(f2,axiom,(
% 3.65/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f12,plain,(
% 3.65/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.65/1.00    inference(rectify,[],[f2])).
% 3.65/1.00  
% 3.65/1.00  fof(f14,plain,(
% 3.65/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.65/1.00    inference(ennf_transformation,[],[f12])).
% 3.65/1.00  
% 3.65/1.00  fof(f21,plain,(
% 3.65/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f22,plain,(
% 3.65/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).
% 3.65/1.00  
% 3.65/1.00  fof(f31,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f22])).
% 3.65/1.00  
% 3.65/1.00  fof(f42,plain,(
% 3.65/1.00    r1_tarski(sK3,sK5)),
% 3.65/1.00    inference(cnf_transformation,[],[f28])).
% 3.65/1.00  
% 3.65/1.00  fof(f6,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f17,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.65/1.00    inference(ennf_transformation,[],[f6])).
% 3.65/1.00  
% 3.65/1.00  fof(f18,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.65/1.00    inference(flattening,[],[f17])).
% 3.65/1.00  
% 3.65/1.00  fof(f25,plain,(
% 3.65/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK2(X0,X1,X2),X0) & r1_tarski(sK2(X0,X1,X2),X2) & r1_tarski(sK2(X0,X1,X2),X1)))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f26,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK2(X0,X1,X2),X0) & r1_tarski(sK2(X0,X1,X2),X2) & r1_tarski(sK2(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f25])).
% 3.65/1.00  
% 3.65/1.00  fof(f35,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK2(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f26])).
% 3.65/1.00  
% 3.65/1.00  fof(f37,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | ~r1_tarski(sK2(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f26])).
% 3.65/1.00  
% 3.65/1.00  fof(f8,axiom,(
% 3.65/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f39,plain,(
% 3.65/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.65/1.00    inference(cnf_transformation,[],[f8])).
% 3.65/1.00  
% 3.65/1.00  fof(f7,axiom,(
% 3.65/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f38,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f7])).
% 3.65/1.00  
% 3.65/1.00  fof(f5,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f34,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f5])).
% 3.65/1.00  
% 3.65/1.00  fof(f41,plain,(
% 3.65/1.00    r1_tarski(sK3,sK4)),
% 3.65/1.00    inference(cnf_transformation,[],[f28])).
% 3.65/1.00  
% 3.65/1.00  fof(f30,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f22])).
% 3.65/1.00  
% 3.65/1.00  fof(f9,axiom,(
% 3.65/1.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f40,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.65/1.00    inference(cnf_transformation,[],[f9])).
% 3.65/1.00  
% 3.65/1.00  fof(f4,axiom,(
% 3.65/1.00    ! [X0,X1] : (k1_xboole_0 = k2_xboole_0(X0,X1) => k1_xboole_0 = X0)),
% 3.65/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f16,plain,(
% 3.65/1.00    ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_xboole_0(X0,X1))),
% 3.65/1.00    inference(ennf_transformation,[],[f4])).
% 3.65/1.00  
% 3.65/1.00  fof(f33,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_xboole_0(X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f16])).
% 3.65/1.00  
% 3.65/1.00  fof(f44,plain,(
% 3.65/1.00    k1_xboole_0 != sK3),
% 3.65/1.00    inference(cnf_transformation,[],[f28])).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13,negated_conjecture,
% 3.65/1.00      ( r1_xboole_0(sK4,sK5) ),
% 3.65/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_383,plain,
% 3.65/1.00      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_0,plain,
% 3.65/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_391,plain,
% 3.65/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.65/1.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1107,plain,
% 3.65/1.00      ( r1_xboole_0(sK5,sK4) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_383,c_391]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3,plain,
% 3.65/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_388,plain,
% 3.65/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1,plain,
% 3.65/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.65/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_390,plain,
% 3.65/1.00      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 3.65/1.00      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1480,plain,
% 3.65/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.65/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_388,c_390]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1666,plain,
% 3.65/1.00      ( k3_xboole_0(sK5,sK4) = k1_xboole_0 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1107,c_1480]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14,negated_conjecture,
% 3.65/1.00      ( r1_tarski(sK3,sK5) ),
% 3.65/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_382,plain,
% 3.65/1.00      ( r1_tarski(sK3,sK5) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8,plain,
% 3.65/1.00      ( ~ r1_tarski(X0,X1)
% 3.65/1.00      | ~ r1_tarski(X0,X2)
% 3.65/1.00      | r1_tarski(sK2(X0,X2,X1),X2)
% 3.65/1.00      | k3_xboole_0(X2,X1) = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_385,plain,
% 3.65/1.00      ( k3_xboole_0(X0,X1) = X2
% 3.65/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.65/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.65/1.00      | r1_tarski(sK2(X2,X0,X1),X0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6,plain,
% 3.65/1.00      ( ~ r1_tarski(X0,X1)
% 3.65/1.00      | ~ r1_tarski(X0,X2)
% 3.65/1.00      | ~ r1_tarski(sK2(X0,X2,X1),X0)
% 3.65/1.00      | k3_xboole_0(X2,X1) = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_387,plain,
% 3.65/1.00      ( k3_xboole_0(X0,X1) = X2
% 3.65/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.65/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.65/1.00      | r1_tarski(sK2(X2,X0,X1),X2) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2053,plain,
% 3.65/1.00      ( k3_xboole_0(X0,X1) = X0
% 3.65/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.65/1.00      | r1_tarski(X0,X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_385,c_387]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_10,plain,
% 3.65/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9,plain,
% 3.65/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_384,plain,
% 3.65/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_585,plain,
% 3.65/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_10,c_384]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13746,plain,
% 3.65/1.00      ( r1_tarski(X0,X1) != iProver_top | k3_xboole_0(X0,X1) = X0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_2053,c_585]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13747,plain,
% 3.65/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_13746]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13753,plain,
% 3.65/1.00      ( k3_xboole_0(sK3,sK5) = sK3 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_382,c_13747]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5,plain,
% 3.65/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13871,plain,
% 3.65/1.00      ( k3_xboole_0(sK3,k3_xboole_0(sK5,X0)) = k3_xboole_0(sK3,X0) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_13753,c_5]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14385,plain,
% 3.65/1.00      ( k3_xboole_0(sK3,sK4) = k3_xboole_0(sK3,k1_xboole_0) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1666,c_13871]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_15,negated_conjecture,
% 3.65/1.00      ( r1_tarski(sK3,sK4) ),
% 3.65/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_381,plain,
% 3.65/1.00      ( r1_tarski(sK3,sK4) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13754,plain,
% 3.65/1.00      ( k3_xboole_0(sK3,sK4) = sK3 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_381,c_13747]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14447,plain,
% 3.65/1.00      ( k3_xboole_0(sK3,k1_xboole_0) = sK3 ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_14385,c_13754]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1665,plain,
% 3.65/1.00      ( k3_xboole_0(sK4,sK5) = k1_xboole_0 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_383,c_1480]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1481,plain,
% 3.65/1.00      ( r2_hidden(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3))) != iProver_top
% 3.65/1.00      | r1_xboole_0(k3_xboole_0(X1,X2),X3) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_5,c_390]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11702,plain,
% 3.65/1.00      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top
% 3.65/1.00      | r1_xboole_0(k3_xboole_0(X1,sK4),sK5) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1665,c_1481]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13110,plain,
% 3.65/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0
% 3.65/1.00      | r1_xboole_0(k3_xboole_0(X0,sK4),sK5) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_388,c_11702]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2,plain,
% 3.65/1.00      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_389,plain,
% 3.65/1.00      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
% 3.65/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1460,plain,
% 3.65/1.00      ( r2_hidden(sK0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = iProver_top
% 3.65/1.00      | r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_5,c_389]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6711,plain,
% 3.65/1.00      ( r2_hidden(sK0(k3_xboole_0(X0,sK4),sK5),k3_xboole_0(X0,k1_xboole_0)) = iProver_top
% 3.65/1.00      | r1_xboole_0(k3_xboole_0(X0,sK4),sK5) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1665,c_1460]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7923,plain,
% 3.65/1.00      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 3.65/1.00      | r1_xboole_0(k3_xboole_0(X0,sK4),sK5) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_6711,c_390]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11,plain,
% 3.65/1.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4,plain,
% 3.65/1.00      ( k2_xboole_0(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_807,plain,
% 3.65/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_11,c_4]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_988,plain,
% 3.65/1.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.65/1.00      inference(equality_resolution,[status(thm)],[c_807]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1461,plain,
% 3.65/1.00      ( r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.65/1.00      | r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_988,c_389]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1732,plain,
% 3.65/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.65/1.00      | r1_xboole_0(sK4,sK5) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1665,c_390]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_18,plain,
% 3.65/1.00      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1813,plain,
% 3.65/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_1732,c_18]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9349,plain,
% 3.65/1.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.65/1.00      inference(forward_subsumption_resolution,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_1461,c_1813]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9354,plain,
% 3.65/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_9349,c_391]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13170,plain,
% 3.65/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_13110,c_7923,c_9354]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14448,plain,
% 3.65/1.00      ( sK3 = k1_xboole_0 ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_14447,c_13170]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_165,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_493,plain,
% 3.65/1.00      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_165]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_494,plain,
% 3.65/1.00      ( sK3 != k1_xboole_0
% 3.65/1.00      | k1_xboole_0 = sK3
% 3.65/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_493]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_164,plain,( X0 = X0 ),theory(equality) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_179,plain,
% 3.65/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_164]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_12,negated_conjecture,
% 3.65/1.00      ( k1_xboole_0 != sK3 ),
% 3.65/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(contradiction,plain,
% 3.65/1.00      ( $false ),
% 3.65/1.00      inference(minisat,[status(thm)],[c_14448,c_494,c_179,c_12]) ).
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  ------                               Statistics
% 3.65/1.00  
% 3.65/1.00  ------ General
% 3.65/1.00  
% 3.65/1.00  abstr_ref_over_cycles:                  0
% 3.65/1.00  abstr_ref_under_cycles:                 0
% 3.65/1.00  gc_basic_clause_elim:                   0
% 3.65/1.00  forced_gc_time:                         0
% 3.65/1.00  parsing_time:                           0.015
% 3.65/1.00  unif_index_cands_time:                  0.
% 3.65/1.00  unif_index_add_time:                    0.
% 3.65/1.00  orderings_time:                         0.
% 3.65/1.00  out_proof_time:                         0.009
% 3.65/1.00  total_time:                             0.41
% 3.65/1.00  num_of_symbols:                         44
% 3.65/1.00  num_of_terms:                           16081
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing
% 3.65/1.00  
% 3.65/1.00  num_of_splits:                          0
% 3.65/1.00  num_of_split_atoms:                     0
% 3.65/1.00  num_of_reused_defs:                     0
% 3.65/1.00  num_eq_ax_congr_red:                    14
% 3.65/1.00  num_of_sem_filtered_clauses:            1
% 3.65/1.00  num_of_subtypes:                        0
% 3.65/1.00  monotx_restored_types:                  0
% 3.65/1.00  sat_num_of_epr_types:                   0
% 3.65/1.00  sat_num_of_non_cyclic_types:            0
% 3.65/1.00  sat_guarded_non_collapsed_types:        0
% 3.65/1.00  num_pure_diseq_elim:                    0
% 3.65/1.00  simp_replaced_by:                       0
% 3.65/1.00  res_preprocessed:                       65
% 3.65/1.00  prep_upred:                             0
% 3.65/1.00  prep_unflattend:                        3
% 3.65/1.00  smt_new_axioms:                         0
% 3.65/1.00  pred_elim_cands:                        3
% 3.65/1.00  pred_elim:                              0
% 3.65/1.00  pred_elim_cl:                           0
% 3.65/1.00  pred_elim_cycles:                       1
% 3.65/1.00  merged_defs:                            0
% 3.65/1.00  merged_defs_ncl:                        0
% 3.65/1.00  bin_hyper_res:                          0
% 3.65/1.00  prep_cycles:                            3
% 3.65/1.00  pred_elim_time:                         0.
% 3.65/1.00  splitting_time:                         0.
% 3.65/1.00  sem_filter_time:                        0.
% 3.65/1.00  monotx_time:                            0.
% 3.65/1.00  subtype_inf_time:                       0.
% 3.65/1.00  
% 3.65/1.00  ------ Problem properties
% 3.65/1.00  
% 3.65/1.00  clauses:                                16
% 3.65/1.00  conjectures:                            4
% 3.65/1.00  epr:                                    5
% 3.65/1.00  horn:                                   12
% 3.65/1.00  ground:                                 4
% 3.65/1.00  unary:                                  8
% 3.65/1.00  binary:                                 5
% 3.65/1.00  lits:                                   30
% 3.65/1.00  lits_eq:                                10
% 3.65/1.00  fd_pure:                                0
% 3.65/1.00  fd_pseudo:                              0
% 3.65/1.00  fd_cond:                                2
% 3.65/1.00  fd_pseudo_cond:                         3
% 3.65/1.00  ac_symbols:                             0
% 3.65/1.00  
% 3.65/1.00  ------ Propositional Solver
% 3.65/1.00  
% 3.65/1.00  prop_solver_calls:                      27
% 3.65/1.00  prop_fast_solver_calls:                 534
% 3.65/1.00  smt_solver_calls:                       0
% 3.65/1.00  smt_fast_solver_calls:                  0
% 3.65/1.00  prop_num_of_clauses:                    4494
% 3.65/1.00  prop_preprocess_simplified:             5412
% 3.65/1.00  prop_fo_subsumed:                       4
% 3.65/1.00  prop_solver_time:                       0.
% 3.65/1.00  smt_solver_time:                        0.
% 3.65/1.00  smt_fast_solver_time:                   0.
% 3.65/1.00  prop_fast_solver_time:                  0.
% 3.65/1.00  prop_unsat_core_time:                   0.
% 3.65/1.00  
% 3.65/1.00  ------ QBF
% 3.65/1.00  
% 3.65/1.00  qbf_q_res:                              0
% 3.65/1.00  qbf_num_tautologies:                    0
% 3.65/1.00  qbf_prep_cycles:                        0
% 3.65/1.00  
% 3.65/1.00  ------ BMC1
% 3.65/1.00  
% 3.65/1.00  bmc1_current_bound:                     -1
% 3.65/1.00  bmc1_last_solved_bound:                 -1
% 3.65/1.00  bmc1_unsat_core_size:                   -1
% 3.65/1.00  bmc1_unsat_core_parents_size:           -1
% 3.65/1.00  bmc1_merge_next_fun:                    0
% 3.65/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.65/1.00  
% 3.65/1.00  ------ Instantiation
% 3.65/1.00  
% 3.65/1.00  inst_num_of_clauses:                    953
% 3.65/1.00  inst_num_in_passive:                    414
% 3.65/1.00  inst_num_in_active:                     512
% 3.65/1.00  inst_num_in_unprocessed:                27
% 3.65/1.00  inst_num_of_loops:                      650
% 3.65/1.00  inst_num_of_learning_restarts:          0
% 3.65/1.00  inst_num_moves_active_passive:          134
% 3.65/1.00  inst_lit_activity:                      0
% 3.65/1.00  inst_lit_activity_moves:                0
% 3.65/1.00  inst_num_tautologies:                   0
% 3.65/1.00  inst_num_prop_implied:                  0
% 3.65/1.00  inst_num_existing_simplified:           0
% 3.65/1.00  inst_num_eq_res_simplified:             0
% 3.65/1.00  inst_num_child_elim:                    0
% 3.65/1.00  inst_num_of_dismatching_blockings:      215
% 3.65/1.00  inst_num_of_non_proper_insts:           882
% 3.65/1.00  inst_num_of_duplicates:                 0
% 3.65/1.00  inst_inst_num_from_inst_to_res:         0
% 3.65/1.00  inst_dismatching_checking_time:         0.
% 3.65/1.00  
% 3.65/1.00  ------ Resolution
% 3.65/1.00  
% 3.65/1.00  res_num_of_clauses:                     0
% 3.65/1.00  res_num_in_passive:                     0
% 3.65/1.00  res_num_in_active:                      0
% 3.65/1.00  res_num_of_loops:                       68
% 3.65/1.00  res_forward_subset_subsumed:            42
% 3.65/1.00  res_backward_subset_subsumed:           8
% 3.65/1.00  res_forward_subsumed:                   0
% 3.65/1.00  res_backward_subsumed:                  0
% 3.65/1.00  res_forward_subsumption_resolution:     0
% 3.65/1.00  res_backward_subsumption_resolution:    0
% 3.65/1.00  res_clause_to_clause_subsumption:       3870
% 3.65/1.00  res_orphan_elimination:                 0
% 3.65/1.00  res_tautology_del:                      86
% 3.65/1.00  res_num_eq_res_simplified:              0
% 3.65/1.00  res_num_sel_changes:                    0
% 3.65/1.00  res_moves_from_active_to_pass:          0
% 3.65/1.00  
% 3.65/1.00  ------ Superposition
% 3.65/1.00  
% 3.65/1.00  sup_time_total:                         0.
% 3.65/1.00  sup_time_generating:                    0.
% 3.65/1.00  sup_time_sim_full:                      0.
% 3.65/1.00  sup_time_sim_immed:                     0.
% 3.65/1.00  
% 3.65/1.00  sup_num_of_clauses:                     1044
% 3.65/1.00  sup_num_in_active:                      102
% 3.65/1.00  sup_num_in_passive:                     942
% 3.65/1.00  sup_num_of_loops:                       128
% 3.65/1.00  sup_fw_superposition:                   627
% 3.65/1.00  sup_bw_superposition:                   1589
% 3.65/1.00  sup_immediate_simplified:               1515
% 3.65/1.00  sup_given_eliminated:                   2
% 3.65/1.00  comparisons_done:                       0
% 3.65/1.00  comparisons_avoided:                    0
% 3.65/1.00  
% 3.65/1.00  ------ Simplifications
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  sim_fw_subset_subsumed:                 107
% 3.65/1.00  sim_bw_subset_subsumed:                 3
% 3.65/1.00  sim_fw_subsumed:                        155
% 3.65/1.00  sim_bw_subsumed:                        3
% 3.65/1.00  sim_fw_subsumption_res:                 2
% 3.65/1.00  sim_bw_subsumption_res:                 0
% 3.65/1.00  sim_tautology_del:                      51
% 3.65/1.00  sim_eq_tautology_del:                   252
% 3.65/1.00  sim_eq_res_simp:                        4
% 3.65/1.00  sim_fw_demodulated:                     612
% 3.65/1.00  sim_bw_demodulated:                     37
% 3.65/1.00  sim_light_normalised:                   820
% 3.65/1.00  sim_joinable_taut:                      0
% 3.65/1.00  sim_joinable_simp:                      0
% 3.65/1.00  sim_ac_normalised:                      0
% 3.65/1.00  sim_smt_subsumption:                    0
% 3.65/1.00  
%------------------------------------------------------------------------------
