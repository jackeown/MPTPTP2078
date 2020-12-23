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
% DateTime   : Thu Dec  3 11:41:44 EST 2020

% Result     : Theorem 8.07s
% Output     : CNFRefutation 8.07s
% Verified   : 
% Statistics : Number of formulae       :  128 (35567 expanded)
%              Number of clauses        :   83 (13596 expanded)
%              Number of leaves         :   15 (7725 expanded)
%              Depth                    :   36
%              Number of atoms          :  396 (90958 expanded)
%              Number of equality atoms :  245 (57475 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f25])).

fof(f42,plain,(
    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f42,f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f23])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_578,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,plain,
    ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_927,plain,
    ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
    | k1_tarski(X0) = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_13,c_12])).

cnf(c_14,negated_conjecture,
    ( k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1134,plain,
    ( k3_xboole_0(sK2,k1_setfam_1(k1_tarski(sK3))) != k3_xboole_0(sK2,sK3)
    | k1_tarski(sK3) = k1_xboole_0
    | k1_tarski(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_927,c_14])).

cnf(c_1138,plain,
    ( k3_xboole_0(sK2,sK3) != k3_xboole_0(sK2,sK3)
    | k1_tarski(sK3) = k1_xboole_0
    | k1_tarski(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1134,c_13])).

cnf(c_1139,plain,
    ( k1_tarski(sK3) = k1_xboole_0
    | k1_tarski(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1138])).

cnf(c_10,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_569,plain,
    ( X0 = X1
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1241,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | r1_xboole_0(k1_tarski(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_569])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_572,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1530,plain,
    ( k3_xboole_0(k1_tarski(X0),k1_xboole_0) = k1_xboole_0
    | k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0 ),
    inference(superposition,[status(thm)],[c_1241,c_572])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_574,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1662,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | r2_hidden(X1,k1_tarski(X0)) = iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_574])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_571,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1659,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | r1_xboole_0(k1_tarski(X0),k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_571])).

cnf(c_2407,plain,
    ( sK3 = X0
    | k1_tarski(sK2) = k1_xboole_0
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1662,c_1241,c_1659])).

cnf(c_2408,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2407])).

cnf(c_2416,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = X1
    | k1_tarski(sK2) = k1_xboole_0
    | sK3 = X2
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_2408])).

cnf(c_2475,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0
    | k1_tarski(sK2) = k1_xboole_0
    | sK3 = X1
    | sK3 = X2 ),
    inference(superposition,[status(thm)],[c_2416,c_2408])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | k3_xboole_0(X1,k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_568,plain,
    ( k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1245,plain,
    ( k3_xboole_0(X0,k1_xboole_0) != k1_tarski(sK3)
    | k1_tarski(sK2) = k1_xboole_0
    | r2_hidden(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_568])).

cnf(c_3367,plain,
    ( k1_tarski(sK3) != k1_xboole_0
    | k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | sK3 = X1
    | r2_hidden(sK3,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2475,c_1245])).

cnf(c_3679,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | sK3 = X1
    | r2_hidden(sK3,X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3367,c_1139])).

cnf(c_3695,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | sK3 = X1
    | sK3 = X2 ),
    inference(superposition,[status(thm)],[c_3679,c_2408])).

cnf(c_3993,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | sK3 = X1
    | sK3 != k1_xboole_0 ),
    inference(equality_factoring,[status(thm)],[c_3695])).

cnf(c_4000,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | sK3 = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3993,c_3695])).

cnf(c_4417,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0
    | sK3 != k1_xboole_0 ),
    inference(equality_factoring,[status(thm)],[c_4000])).

cnf(c_4422,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4417,c_4000])).

cnf(c_5962,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(equality_factoring,[status(thm)],[c_4422])).

cnf(c_5965,plain,
    ( k1_tarski(sK2) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5962,c_4422])).

cnf(c_923,plain,
    ( X0 = X1
    | k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_569,c_572])).

cnf(c_14821,plain,
    ( k3_xboole_0(k1_tarski(X0),k1_xboole_0) = k1_xboole_0
    | sK2 = X0 ),
    inference(superposition,[status(thm)],[c_5965,c_923])).

cnf(c_1132,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(k2_xboole_0(k1_tarski(X0),X1),X2)) = k3_xboole_0(k3_xboole_0(X0,k1_setfam_1(X1)),k1_setfam_1(X2))
    | k1_tarski(X0) = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_927,c_12])).

cnf(c_6056,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k1_setfam_1(X2))
    | k1_tarski(X0) = k1_xboole_0
    | k1_tarski(X1) = k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_13,c_1132])).

cnf(c_928,plain,
    ( k1_setfam_1(k2_xboole_0(X0,k1_tarski(X1))) = k3_xboole_0(k1_setfam_1(X0),X1)
    | k1_tarski(X1) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_13,c_12])).

cnf(c_9239,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
    | k3_xboole_0(k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),X2) = k3_xboole_0(k3_xboole_0(X0,X1),k1_setfam_1(k1_tarski(X2)))
    | k1_tarski(X0) = k1_xboole_0
    | k1_tarski(X1) = k1_xboole_0
    | k1_tarski(X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6056,c_928])).

cnf(c_9363,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
    | k3_xboole_0(k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),X2) = k3_xboole_0(k3_xboole_0(X0,X1),X2)
    | k1_tarski(X0) = k1_xboole_0
    | k1_tarski(X1) = k1_xboole_0
    | k1_tarski(X2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9239,c_13])).

cnf(c_14824,plain,
    ( k3_xboole_0(X0,k1_xboole_0) != k1_tarski(sK2)
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5965,c_568])).

cnf(c_14833,plain,
    ( k3_xboole_0(X0,k1_xboole_0) != k1_xboole_0
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14824,c_5965])).

cnf(c_21475,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
    | k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) != k1_xboole_0
    | k1_tarski(X0) = k1_xboole_0
    | k1_tarski(X1) = k1_xboole_0
    | k1_tarski(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK2,k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9363,c_14833])).

cnf(c_44585,plain,
    ( k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_tarski(k1_tarski(X0)) = k1_xboole_0
    | k1_tarski(k1_xboole_0) = k1_xboole_0
    | sK2 = X0
    | r2_hidden(sK2,k1_setfam_1(k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14821,c_21475])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_43,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_47,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_45084,plain,
    ( k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_tarski(k1_tarski(X0)) = k1_xboole_0
    | k1_tarski(k1_xboole_0) = k1_xboole_0
    | sK2 = X0
    | r2_hidden(sK2,k1_setfam_1(k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44585,c_43,c_47])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_575,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_931,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r2_hidden(X2,k1_setfam_1(X1)) = iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_xboole_0(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_575])).

cnf(c_45101,plain,
    ( k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_tarski(k1_tarski(X0)) = k1_xboole_0
    | k1_tarski(k1_xboole_0) = k1_xboole_0
    | sK2 = X0
    | r2_hidden(sK2,k1_setfam_1(k1_tarski(k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_45084,c_931])).

cnf(c_45107,plain,
    ( k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_tarski(k1_tarski(X0)) = k1_xboole_0
    | k1_tarski(k1_xboole_0) = k1_xboole_0
    | sK2 = X0
    | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_45101,c_13])).

cnf(c_14865,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14833])).

cnf(c_46138,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45107,c_43,c_47,c_14865])).

cnf(c_14807,plain,
    ( k3_xboole_0(k1_xboole_0,k1_tarski(X0)) = k1_xboole_0
    | sK2 = X0 ),
    inference(superposition,[status(thm)],[c_5965,c_923])).

cnf(c_21588,plain,
    ( sK2 = X0
    | r1_xboole_0(k1_xboole_0,k1_tarski(X0)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14807,c_571])).

cnf(c_14812,plain,
    ( sK2 = X0
    | r1_xboole_0(k1_tarski(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5965,c_569])).

cnf(c_21912,plain,
    ( sK2 = X0
    | r1_xboole_0(k1_tarski(X0),k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14821,c_571])).

cnf(c_22105,plain,
    ( sK2 = X0
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21588,c_14812,c_21912])).

cnf(c_46143,plain,
    ( sK2 = X0 ),
    inference(superposition,[status(thm)],[c_46138,c_22105])).

cnf(c_46144,plain,
    ( sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_46143])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_45157,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,k1_xboole_0)
    | X0 != sK2
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_45164,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_45157])).

cnf(c_14864,plain,
    ( r2_hidden(sK2,X0)
    | k3_xboole_0(X0,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14833])).

cnf(c_14866,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14864])).

cnf(c_250,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1372,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_1373,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_249,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_264,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_40,plain,
    ( r2_hidden(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_33,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_27,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46144,c_45164,c_14866,c_1373,c_264,c_47,c_43,c_40,c_33,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:59:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.07/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/1.49  
% 8.07/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.07/1.49  
% 8.07/1.49  ------  iProver source info
% 8.07/1.49  
% 8.07/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.07/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.07/1.49  git: non_committed_changes: false
% 8.07/1.49  git: last_make_outside_of_git: false
% 8.07/1.49  
% 8.07/1.49  ------ 
% 8.07/1.49  
% 8.07/1.49  ------ Input Options
% 8.07/1.49  
% 8.07/1.49  --out_options                           all
% 8.07/1.49  --tptp_safe_out                         true
% 8.07/1.49  --problem_path                          ""
% 8.07/1.49  --include_path                          ""
% 8.07/1.49  --clausifier                            res/vclausify_rel
% 8.07/1.49  --clausifier_options                    --mode clausify
% 8.07/1.49  --stdin                                 false
% 8.07/1.49  --stats_out                             all
% 8.07/1.49  
% 8.07/1.49  ------ General Options
% 8.07/1.49  
% 8.07/1.49  --fof                                   false
% 8.07/1.49  --time_out_real                         305.
% 8.07/1.49  --time_out_virtual                      -1.
% 8.07/1.49  --symbol_type_check                     false
% 8.07/1.49  --clausify_out                          false
% 8.07/1.49  --sig_cnt_out                           false
% 8.07/1.49  --trig_cnt_out                          false
% 8.07/1.49  --trig_cnt_out_tolerance                1.
% 8.07/1.49  --trig_cnt_out_sk_spl                   false
% 8.07/1.49  --abstr_cl_out                          false
% 8.07/1.49  
% 8.07/1.49  ------ Global Options
% 8.07/1.49  
% 8.07/1.49  --schedule                              default
% 8.07/1.49  --add_important_lit                     false
% 8.07/1.49  --prop_solver_per_cl                    1000
% 8.07/1.49  --min_unsat_core                        false
% 8.07/1.49  --soft_assumptions                      false
% 8.07/1.49  --soft_lemma_size                       3
% 8.07/1.49  --prop_impl_unit_size                   0
% 8.07/1.49  --prop_impl_unit                        []
% 8.07/1.49  --share_sel_clauses                     true
% 8.07/1.49  --reset_solvers                         false
% 8.07/1.49  --bc_imp_inh                            [conj_cone]
% 8.07/1.49  --conj_cone_tolerance                   3.
% 8.07/1.49  --extra_neg_conj                        none
% 8.07/1.49  --large_theory_mode                     true
% 8.07/1.49  --prolific_symb_bound                   200
% 8.07/1.49  --lt_threshold                          2000
% 8.07/1.49  --clause_weak_htbl                      true
% 8.07/1.49  --gc_record_bc_elim                     false
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing Options
% 8.07/1.49  
% 8.07/1.49  --preprocessing_flag                    true
% 8.07/1.49  --time_out_prep_mult                    0.1
% 8.07/1.49  --splitting_mode                        input
% 8.07/1.49  --splitting_grd                         true
% 8.07/1.49  --splitting_cvd                         false
% 8.07/1.49  --splitting_cvd_svl                     false
% 8.07/1.49  --splitting_nvd                         32
% 8.07/1.49  --sub_typing                            true
% 8.07/1.49  --prep_gs_sim                           true
% 8.07/1.49  --prep_unflatten                        true
% 8.07/1.49  --prep_res_sim                          true
% 8.07/1.49  --prep_upred                            true
% 8.07/1.49  --prep_sem_filter                       exhaustive
% 8.07/1.49  --prep_sem_filter_out                   false
% 8.07/1.49  --pred_elim                             true
% 8.07/1.49  --res_sim_input                         true
% 8.07/1.49  --eq_ax_congr_red                       true
% 8.07/1.49  --pure_diseq_elim                       true
% 8.07/1.49  --brand_transform                       false
% 8.07/1.49  --non_eq_to_eq                          false
% 8.07/1.49  --prep_def_merge                        true
% 8.07/1.49  --prep_def_merge_prop_impl              false
% 8.07/1.49  --prep_def_merge_mbd                    true
% 8.07/1.49  --prep_def_merge_tr_red                 false
% 8.07/1.49  --prep_def_merge_tr_cl                  false
% 8.07/1.49  --smt_preprocessing                     true
% 8.07/1.49  --smt_ac_axioms                         fast
% 8.07/1.49  --preprocessed_out                      false
% 8.07/1.49  --preprocessed_stats                    false
% 8.07/1.49  
% 8.07/1.49  ------ Abstraction refinement Options
% 8.07/1.49  
% 8.07/1.49  --abstr_ref                             []
% 8.07/1.49  --abstr_ref_prep                        false
% 8.07/1.49  --abstr_ref_until_sat                   false
% 8.07/1.49  --abstr_ref_sig_restrict                funpre
% 8.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.07/1.49  --abstr_ref_under                       []
% 8.07/1.49  
% 8.07/1.49  ------ SAT Options
% 8.07/1.49  
% 8.07/1.49  --sat_mode                              false
% 8.07/1.49  --sat_fm_restart_options                ""
% 8.07/1.49  --sat_gr_def                            false
% 8.07/1.49  --sat_epr_types                         true
% 8.07/1.49  --sat_non_cyclic_types                  false
% 8.07/1.49  --sat_finite_models                     false
% 8.07/1.49  --sat_fm_lemmas                         false
% 8.07/1.49  --sat_fm_prep                           false
% 8.07/1.49  --sat_fm_uc_incr                        true
% 8.07/1.49  --sat_out_model                         small
% 8.07/1.49  --sat_out_clauses                       false
% 8.07/1.49  
% 8.07/1.49  ------ QBF Options
% 8.07/1.49  
% 8.07/1.49  --qbf_mode                              false
% 8.07/1.49  --qbf_elim_univ                         false
% 8.07/1.49  --qbf_dom_inst                          none
% 8.07/1.49  --qbf_dom_pre_inst                      false
% 8.07/1.49  --qbf_sk_in                             false
% 8.07/1.49  --qbf_pred_elim                         true
% 8.07/1.49  --qbf_split                             512
% 8.07/1.49  
% 8.07/1.49  ------ BMC1 Options
% 8.07/1.49  
% 8.07/1.49  --bmc1_incremental                      false
% 8.07/1.49  --bmc1_axioms                           reachable_all
% 8.07/1.49  --bmc1_min_bound                        0
% 8.07/1.49  --bmc1_max_bound                        -1
% 8.07/1.49  --bmc1_max_bound_default                -1
% 8.07/1.49  --bmc1_symbol_reachability              true
% 8.07/1.49  --bmc1_property_lemmas                  false
% 8.07/1.49  --bmc1_k_induction                      false
% 8.07/1.49  --bmc1_non_equiv_states                 false
% 8.07/1.49  --bmc1_deadlock                         false
% 8.07/1.49  --bmc1_ucm                              false
% 8.07/1.49  --bmc1_add_unsat_core                   none
% 8.07/1.49  --bmc1_unsat_core_children              false
% 8.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.07/1.49  --bmc1_out_stat                         full
% 8.07/1.49  --bmc1_ground_init                      false
% 8.07/1.49  --bmc1_pre_inst_next_state              false
% 8.07/1.49  --bmc1_pre_inst_state                   false
% 8.07/1.49  --bmc1_pre_inst_reach_state             false
% 8.07/1.49  --bmc1_out_unsat_core                   false
% 8.07/1.49  --bmc1_aig_witness_out                  false
% 8.07/1.49  --bmc1_verbose                          false
% 8.07/1.49  --bmc1_dump_clauses_tptp                false
% 8.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.07/1.49  --bmc1_dump_file                        -
% 8.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.07/1.49  --bmc1_ucm_extend_mode                  1
% 8.07/1.49  --bmc1_ucm_init_mode                    2
% 8.07/1.49  --bmc1_ucm_cone_mode                    none
% 8.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.07/1.49  --bmc1_ucm_relax_model                  4
% 8.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.07/1.49  --bmc1_ucm_layered_model                none
% 8.07/1.49  --bmc1_ucm_max_lemma_size               10
% 8.07/1.49  
% 8.07/1.49  ------ AIG Options
% 8.07/1.49  
% 8.07/1.49  --aig_mode                              false
% 8.07/1.49  
% 8.07/1.49  ------ Instantiation Options
% 8.07/1.49  
% 8.07/1.49  --instantiation_flag                    true
% 8.07/1.49  --inst_sos_flag                         false
% 8.07/1.49  --inst_sos_phase                        true
% 8.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.07/1.49  --inst_lit_sel_side                     num_symb
% 8.07/1.49  --inst_solver_per_active                1400
% 8.07/1.49  --inst_solver_calls_frac                1.
% 8.07/1.49  --inst_passive_queue_type               priority_queues
% 8.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.07/1.49  --inst_passive_queues_freq              [25;2]
% 8.07/1.49  --inst_dismatching                      true
% 8.07/1.49  --inst_eager_unprocessed_to_passive     true
% 8.07/1.49  --inst_prop_sim_given                   true
% 8.07/1.49  --inst_prop_sim_new                     false
% 8.07/1.49  --inst_subs_new                         false
% 8.07/1.49  --inst_eq_res_simp                      false
% 8.07/1.49  --inst_subs_given                       false
% 8.07/1.49  --inst_orphan_elimination               true
% 8.07/1.49  --inst_learning_loop_flag               true
% 8.07/1.49  --inst_learning_start                   3000
% 8.07/1.49  --inst_learning_factor                  2
% 8.07/1.49  --inst_start_prop_sim_after_learn       3
% 8.07/1.49  --inst_sel_renew                        solver
% 8.07/1.49  --inst_lit_activity_flag                true
% 8.07/1.49  --inst_restr_to_given                   false
% 8.07/1.49  --inst_activity_threshold               500
% 8.07/1.49  --inst_out_proof                        true
% 8.07/1.49  
% 8.07/1.49  ------ Resolution Options
% 8.07/1.49  
% 8.07/1.49  --resolution_flag                       true
% 8.07/1.49  --res_lit_sel                           adaptive
% 8.07/1.49  --res_lit_sel_side                      none
% 8.07/1.49  --res_ordering                          kbo
% 8.07/1.49  --res_to_prop_solver                    active
% 8.07/1.49  --res_prop_simpl_new                    false
% 8.07/1.49  --res_prop_simpl_given                  true
% 8.07/1.49  --res_passive_queue_type                priority_queues
% 8.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.07/1.49  --res_passive_queues_freq               [15;5]
% 8.07/1.49  --res_forward_subs                      full
% 8.07/1.49  --res_backward_subs                     full
% 8.07/1.49  --res_forward_subs_resolution           true
% 8.07/1.49  --res_backward_subs_resolution          true
% 8.07/1.49  --res_orphan_elimination                true
% 8.07/1.49  --res_time_limit                        2.
% 8.07/1.49  --res_out_proof                         true
% 8.07/1.49  
% 8.07/1.49  ------ Superposition Options
% 8.07/1.49  
% 8.07/1.49  --superposition_flag                    true
% 8.07/1.49  --sup_passive_queue_type                priority_queues
% 8.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.07/1.49  --demod_completeness_check              fast
% 8.07/1.49  --demod_use_ground                      true
% 8.07/1.49  --sup_to_prop_solver                    passive
% 8.07/1.49  --sup_prop_simpl_new                    true
% 8.07/1.49  --sup_prop_simpl_given                  true
% 8.07/1.49  --sup_fun_splitting                     false
% 8.07/1.49  --sup_smt_interval                      50000
% 8.07/1.49  
% 8.07/1.49  ------ Superposition Simplification Setup
% 8.07/1.49  
% 8.07/1.49  --sup_indices_passive                   []
% 8.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_full_bw                           [BwDemod]
% 8.07/1.49  --sup_immed_triv                        [TrivRules]
% 8.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_immed_bw_main                     []
% 8.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.07/1.49  
% 8.07/1.49  ------ Combination Options
% 8.07/1.49  
% 8.07/1.49  --comb_res_mult                         3
% 8.07/1.49  --comb_sup_mult                         2
% 8.07/1.49  --comb_inst_mult                        10
% 8.07/1.49  
% 8.07/1.49  ------ Debug Options
% 8.07/1.49  
% 8.07/1.49  --dbg_backtrace                         false
% 8.07/1.49  --dbg_dump_prop_clauses                 false
% 8.07/1.49  --dbg_dump_prop_clauses_file            -
% 8.07/1.49  --dbg_out_stat                          false
% 8.07/1.49  ------ Parsing...
% 8.07/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.07/1.49  ------ Proving...
% 8.07/1.49  ------ Problem Properties 
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  clauses                                 15
% 8.07/1.49  conjectures                             1
% 8.07/1.49  EPR                                     0
% 8.07/1.49  Horn                                    10
% 8.07/1.49  unary                                   2
% 8.07/1.49  binary                                  8
% 8.07/1.49  lits                                    34
% 8.07/1.49  lits eq                                 12
% 8.07/1.49  fd_pure                                 0
% 8.07/1.49  fd_pseudo                               0
% 8.07/1.49  fd_cond                                 1
% 8.07/1.49  fd_pseudo_cond                          4
% 8.07/1.49  AC symbols                              0
% 8.07/1.49  
% 8.07/1.49  ------ Schedule dynamic 5 is on 
% 8.07/1.49  
% 8.07/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  ------ 
% 8.07/1.49  Current options:
% 8.07/1.49  ------ 
% 8.07/1.49  
% 8.07/1.49  ------ Input Options
% 8.07/1.49  
% 8.07/1.49  --out_options                           all
% 8.07/1.49  --tptp_safe_out                         true
% 8.07/1.49  --problem_path                          ""
% 8.07/1.49  --include_path                          ""
% 8.07/1.49  --clausifier                            res/vclausify_rel
% 8.07/1.49  --clausifier_options                    --mode clausify
% 8.07/1.49  --stdin                                 false
% 8.07/1.49  --stats_out                             all
% 8.07/1.49  
% 8.07/1.49  ------ General Options
% 8.07/1.49  
% 8.07/1.49  --fof                                   false
% 8.07/1.49  --time_out_real                         305.
% 8.07/1.49  --time_out_virtual                      -1.
% 8.07/1.49  --symbol_type_check                     false
% 8.07/1.49  --clausify_out                          false
% 8.07/1.49  --sig_cnt_out                           false
% 8.07/1.49  --trig_cnt_out                          false
% 8.07/1.49  --trig_cnt_out_tolerance                1.
% 8.07/1.49  --trig_cnt_out_sk_spl                   false
% 8.07/1.49  --abstr_cl_out                          false
% 8.07/1.49  
% 8.07/1.49  ------ Global Options
% 8.07/1.49  
% 8.07/1.49  --schedule                              default
% 8.07/1.49  --add_important_lit                     false
% 8.07/1.49  --prop_solver_per_cl                    1000
% 8.07/1.49  --min_unsat_core                        false
% 8.07/1.49  --soft_assumptions                      false
% 8.07/1.49  --soft_lemma_size                       3
% 8.07/1.49  --prop_impl_unit_size                   0
% 8.07/1.49  --prop_impl_unit                        []
% 8.07/1.49  --share_sel_clauses                     true
% 8.07/1.49  --reset_solvers                         false
% 8.07/1.49  --bc_imp_inh                            [conj_cone]
% 8.07/1.49  --conj_cone_tolerance                   3.
% 8.07/1.49  --extra_neg_conj                        none
% 8.07/1.49  --large_theory_mode                     true
% 8.07/1.49  --prolific_symb_bound                   200
% 8.07/1.49  --lt_threshold                          2000
% 8.07/1.49  --clause_weak_htbl                      true
% 8.07/1.49  --gc_record_bc_elim                     false
% 8.07/1.49  
% 8.07/1.49  ------ Preprocessing Options
% 8.07/1.49  
% 8.07/1.49  --preprocessing_flag                    true
% 8.07/1.49  --time_out_prep_mult                    0.1
% 8.07/1.49  --splitting_mode                        input
% 8.07/1.49  --splitting_grd                         true
% 8.07/1.49  --splitting_cvd                         false
% 8.07/1.49  --splitting_cvd_svl                     false
% 8.07/1.49  --splitting_nvd                         32
% 8.07/1.49  --sub_typing                            true
% 8.07/1.49  --prep_gs_sim                           true
% 8.07/1.49  --prep_unflatten                        true
% 8.07/1.49  --prep_res_sim                          true
% 8.07/1.49  --prep_upred                            true
% 8.07/1.49  --prep_sem_filter                       exhaustive
% 8.07/1.49  --prep_sem_filter_out                   false
% 8.07/1.49  --pred_elim                             true
% 8.07/1.49  --res_sim_input                         true
% 8.07/1.49  --eq_ax_congr_red                       true
% 8.07/1.49  --pure_diseq_elim                       true
% 8.07/1.49  --brand_transform                       false
% 8.07/1.49  --non_eq_to_eq                          false
% 8.07/1.49  --prep_def_merge                        true
% 8.07/1.49  --prep_def_merge_prop_impl              false
% 8.07/1.49  --prep_def_merge_mbd                    true
% 8.07/1.49  --prep_def_merge_tr_red                 false
% 8.07/1.49  --prep_def_merge_tr_cl                  false
% 8.07/1.49  --smt_preprocessing                     true
% 8.07/1.49  --smt_ac_axioms                         fast
% 8.07/1.49  --preprocessed_out                      false
% 8.07/1.49  --preprocessed_stats                    false
% 8.07/1.49  
% 8.07/1.49  ------ Abstraction refinement Options
% 8.07/1.49  
% 8.07/1.49  --abstr_ref                             []
% 8.07/1.49  --abstr_ref_prep                        false
% 8.07/1.49  --abstr_ref_until_sat                   false
% 8.07/1.49  --abstr_ref_sig_restrict                funpre
% 8.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.07/1.49  --abstr_ref_under                       []
% 8.07/1.49  
% 8.07/1.49  ------ SAT Options
% 8.07/1.49  
% 8.07/1.49  --sat_mode                              false
% 8.07/1.49  --sat_fm_restart_options                ""
% 8.07/1.49  --sat_gr_def                            false
% 8.07/1.49  --sat_epr_types                         true
% 8.07/1.49  --sat_non_cyclic_types                  false
% 8.07/1.49  --sat_finite_models                     false
% 8.07/1.49  --sat_fm_lemmas                         false
% 8.07/1.49  --sat_fm_prep                           false
% 8.07/1.49  --sat_fm_uc_incr                        true
% 8.07/1.49  --sat_out_model                         small
% 8.07/1.49  --sat_out_clauses                       false
% 8.07/1.49  
% 8.07/1.49  ------ QBF Options
% 8.07/1.49  
% 8.07/1.49  --qbf_mode                              false
% 8.07/1.49  --qbf_elim_univ                         false
% 8.07/1.49  --qbf_dom_inst                          none
% 8.07/1.49  --qbf_dom_pre_inst                      false
% 8.07/1.49  --qbf_sk_in                             false
% 8.07/1.49  --qbf_pred_elim                         true
% 8.07/1.49  --qbf_split                             512
% 8.07/1.49  
% 8.07/1.49  ------ BMC1 Options
% 8.07/1.49  
% 8.07/1.49  --bmc1_incremental                      false
% 8.07/1.49  --bmc1_axioms                           reachable_all
% 8.07/1.49  --bmc1_min_bound                        0
% 8.07/1.49  --bmc1_max_bound                        -1
% 8.07/1.49  --bmc1_max_bound_default                -1
% 8.07/1.49  --bmc1_symbol_reachability              true
% 8.07/1.49  --bmc1_property_lemmas                  false
% 8.07/1.49  --bmc1_k_induction                      false
% 8.07/1.49  --bmc1_non_equiv_states                 false
% 8.07/1.49  --bmc1_deadlock                         false
% 8.07/1.49  --bmc1_ucm                              false
% 8.07/1.49  --bmc1_add_unsat_core                   none
% 8.07/1.49  --bmc1_unsat_core_children              false
% 8.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.07/1.49  --bmc1_out_stat                         full
% 8.07/1.49  --bmc1_ground_init                      false
% 8.07/1.49  --bmc1_pre_inst_next_state              false
% 8.07/1.49  --bmc1_pre_inst_state                   false
% 8.07/1.49  --bmc1_pre_inst_reach_state             false
% 8.07/1.49  --bmc1_out_unsat_core                   false
% 8.07/1.49  --bmc1_aig_witness_out                  false
% 8.07/1.49  --bmc1_verbose                          false
% 8.07/1.49  --bmc1_dump_clauses_tptp                false
% 8.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.07/1.49  --bmc1_dump_file                        -
% 8.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.07/1.49  --bmc1_ucm_extend_mode                  1
% 8.07/1.49  --bmc1_ucm_init_mode                    2
% 8.07/1.49  --bmc1_ucm_cone_mode                    none
% 8.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.07/1.49  --bmc1_ucm_relax_model                  4
% 8.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.07/1.49  --bmc1_ucm_layered_model                none
% 8.07/1.49  --bmc1_ucm_max_lemma_size               10
% 8.07/1.49  
% 8.07/1.49  ------ AIG Options
% 8.07/1.49  
% 8.07/1.49  --aig_mode                              false
% 8.07/1.49  
% 8.07/1.49  ------ Instantiation Options
% 8.07/1.49  
% 8.07/1.49  --instantiation_flag                    true
% 8.07/1.49  --inst_sos_flag                         false
% 8.07/1.49  --inst_sos_phase                        true
% 8.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.07/1.49  --inst_lit_sel_side                     none
% 8.07/1.49  --inst_solver_per_active                1400
% 8.07/1.49  --inst_solver_calls_frac                1.
% 8.07/1.49  --inst_passive_queue_type               priority_queues
% 8.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.07/1.49  --inst_passive_queues_freq              [25;2]
% 8.07/1.49  --inst_dismatching                      true
% 8.07/1.49  --inst_eager_unprocessed_to_passive     true
% 8.07/1.49  --inst_prop_sim_given                   true
% 8.07/1.49  --inst_prop_sim_new                     false
% 8.07/1.49  --inst_subs_new                         false
% 8.07/1.49  --inst_eq_res_simp                      false
% 8.07/1.49  --inst_subs_given                       false
% 8.07/1.49  --inst_orphan_elimination               true
% 8.07/1.49  --inst_learning_loop_flag               true
% 8.07/1.49  --inst_learning_start                   3000
% 8.07/1.49  --inst_learning_factor                  2
% 8.07/1.49  --inst_start_prop_sim_after_learn       3
% 8.07/1.49  --inst_sel_renew                        solver
% 8.07/1.49  --inst_lit_activity_flag                true
% 8.07/1.49  --inst_restr_to_given                   false
% 8.07/1.49  --inst_activity_threshold               500
% 8.07/1.49  --inst_out_proof                        true
% 8.07/1.49  
% 8.07/1.49  ------ Resolution Options
% 8.07/1.49  
% 8.07/1.49  --resolution_flag                       false
% 8.07/1.49  --res_lit_sel                           adaptive
% 8.07/1.49  --res_lit_sel_side                      none
% 8.07/1.49  --res_ordering                          kbo
% 8.07/1.49  --res_to_prop_solver                    active
% 8.07/1.49  --res_prop_simpl_new                    false
% 8.07/1.49  --res_prop_simpl_given                  true
% 8.07/1.49  --res_passive_queue_type                priority_queues
% 8.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.07/1.49  --res_passive_queues_freq               [15;5]
% 8.07/1.49  --res_forward_subs                      full
% 8.07/1.49  --res_backward_subs                     full
% 8.07/1.49  --res_forward_subs_resolution           true
% 8.07/1.49  --res_backward_subs_resolution          true
% 8.07/1.49  --res_orphan_elimination                true
% 8.07/1.49  --res_time_limit                        2.
% 8.07/1.49  --res_out_proof                         true
% 8.07/1.49  
% 8.07/1.49  ------ Superposition Options
% 8.07/1.49  
% 8.07/1.49  --superposition_flag                    true
% 8.07/1.49  --sup_passive_queue_type                priority_queues
% 8.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.07/1.49  --demod_completeness_check              fast
% 8.07/1.49  --demod_use_ground                      true
% 8.07/1.49  --sup_to_prop_solver                    passive
% 8.07/1.49  --sup_prop_simpl_new                    true
% 8.07/1.49  --sup_prop_simpl_given                  true
% 8.07/1.49  --sup_fun_splitting                     false
% 8.07/1.49  --sup_smt_interval                      50000
% 8.07/1.49  
% 8.07/1.49  ------ Superposition Simplification Setup
% 8.07/1.49  
% 8.07/1.49  --sup_indices_passive                   []
% 8.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_full_bw                           [BwDemod]
% 8.07/1.49  --sup_immed_triv                        [TrivRules]
% 8.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_immed_bw_main                     []
% 8.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.07/1.49  
% 8.07/1.49  ------ Combination Options
% 8.07/1.49  
% 8.07/1.49  --comb_res_mult                         3
% 8.07/1.49  --comb_sup_mult                         2
% 8.07/1.49  --comb_inst_mult                        10
% 8.07/1.49  
% 8.07/1.49  ------ Debug Options
% 8.07/1.49  
% 8.07/1.49  --dbg_backtrace                         false
% 8.07/1.49  --dbg_dump_prop_clauses                 false
% 8.07/1.49  --dbg_dump_prop_clauses_file            -
% 8.07/1.49  --dbg_out_stat                          false
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  ------ Proving...
% 8.07/1.49  
% 8.07/1.49  
% 8.07/1.49  % SZS status Theorem for theBenchmark.p
% 8.07/1.49  
% 8.07/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.07/1.49  
% 8.07/1.49  fof(f1,axiom,(
% 8.07/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f17,plain,(
% 8.07/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.07/1.49    inference(nnf_transformation,[],[f1])).
% 8.07/1.49  
% 8.07/1.49  fof(f18,plain,(
% 8.07/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.07/1.49    inference(flattening,[],[f17])).
% 8.07/1.49  
% 8.07/1.49  fof(f19,plain,(
% 8.07/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.07/1.49    inference(rectify,[],[f18])).
% 8.07/1.49  
% 8.07/1.49  fof(f20,plain,(
% 8.07/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 8.07/1.49    introduced(choice_axiom,[])).
% 8.07/1.49  
% 8.07/1.49  fof(f21,plain,(
% 8.07/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 8.07/1.49  
% 8.07/1.49  fof(f31,plain,(
% 8.07/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f21])).
% 8.07/1.49  
% 8.07/1.49  fof(f8,axiom,(
% 8.07/1.49    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f41,plain,(
% 8.07/1.49    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 8.07/1.49    inference(cnf_transformation,[],[f8])).
% 8.07/1.49  
% 8.07/1.49  fof(f7,axiom,(
% 8.07/1.49    ! [X0,X1] : ~(k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f15,plain,(
% 8.07/1.49    ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 8.07/1.49    inference(ennf_transformation,[],[f7])).
% 8.07/1.49  
% 8.07/1.49  fof(f40,plain,(
% 8.07/1.49    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 8.07/1.49    inference(cnf_transformation,[],[f15])).
% 8.07/1.49  
% 8.07/1.49  fof(f9,conjecture,(
% 8.07/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f10,negated_conjecture,(
% 8.07/1.49    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 8.07/1.49    inference(negated_conjecture,[],[f9])).
% 8.07/1.49  
% 8.07/1.49  fof(f16,plain,(
% 8.07/1.49    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 8.07/1.49    inference(ennf_transformation,[],[f10])).
% 8.07/1.49  
% 8.07/1.49  fof(f25,plain,(
% 8.07/1.49    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 8.07/1.49    introduced(choice_axiom,[])).
% 8.07/1.49  
% 8.07/1.49  fof(f26,plain,(
% 8.07/1.49    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 8.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f25])).
% 8.07/1.49  
% 8.07/1.49  fof(f42,plain,(
% 8.07/1.49    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 8.07/1.49    inference(cnf_transformation,[],[f26])).
% 8.07/1.49  
% 8.07/1.49  fof(f4,axiom,(
% 8.07/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f37,plain,(
% 8.07/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 8.07/1.49    inference(cnf_transformation,[],[f4])).
% 8.07/1.49  
% 8.07/1.49  fof(f43,plain,(
% 8.07/1.49    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),
% 8.07/1.49    inference(definition_unfolding,[],[f42,f37])).
% 8.07/1.49  
% 8.07/1.49  fof(f5,axiom,(
% 8.07/1.49    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f13,plain,(
% 8.07/1.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 8.07/1.49    inference(ennf_transformation,[],[f5])).
% 8.07/1.49  
% 8.07/1.49  fof(f38,plain,(
% 8.07/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 8.07/1.49    inference(cnf_transformation,[],[f13])).
% 8.07/1.49  
% 8.07/1.49  fof(f2,axiom,(
% 8.07/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f22,plain,(
% 8.07/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 8.07/1.49    inference(nnf_transformation,[],[f2])).
% 8.07/1.49  
% 8.07/1.49  fof(f33,plain,(
% 8.07/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f22])).
% 8.07/1.49  
% 8.07/1.49  fof(f27,plain,(
% 8.07/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 8.07/1.49    inference(cnf_transformation,[],[f21])).
% 8.07/1.49  
% 8.07/1.49  fof(f46,plain,(
% 8.07/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 8.07/1.49    inference(equality_resolution,[],[f27])).
% 8.07/1.49  
% 8.07/1.49  fof(f3,axiom,(
% 8.07/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f11,plain,(
% 8.07/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 8.07/1.49    inference(rectify,[],[f3])).
% 8.07/1.49  
% 8.07/1.49  fof(f12,plain,(
% 8.07/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 8.07/1.49    inference(ennf_transformation,[],[f11])).
% 8.07/1.49  
% 8.07/1.49  fof(f23,plain,(
% 8.07/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 8.07/1.49    introduced(choice_axiom,[])).
% 8.07/1.49  
% 8.07/1.49  fof(f24,plain,(
% 8.07/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 8.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f23])).
% 8.07/1.49  
% 8.07/1.49  fof(f36,plain,(
% 8.07/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 8.07/1.49    inference(cnf_transformation,[],[f24])).
% 8.07/1.49  
% 8.07/1.49  fof(f6,axiom,(
% 8.07/1.49    ! [X0,X1] : (k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) => r2_hidden(X1,X0))),
% 8.07/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.49  
% 8.07/1.49  fof(f14,plain,(
% 8.07/1.49    ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1))),
% 8.07/1.49    inference(ennf_transformation,[],[f6])).
% 8.07/1.49  
% 8.07/1.49  fof(f39,plain,(
% 8.07/1.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f14])).
% 8.07/1.49  
% 8.07/1.49  fof(f30,plain,(
% 8.07/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f21])).
% 8.07/1.49  
% 8.07/1.49  fof(f32,plain,(
% 8.07/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 8.07/1.49    inference(cnf_transformation,[],[f21])).
% 8.07/1.49  
% 8.07/1.49  fof(f28,plain,(
% 8.07/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 8.07/1.49    inference(cnf_transformation,[],[f21])).
% 8.07/1.49  
% 8.07/1.49  fof(f45,plain,(
% 8.07/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 8.07/1.49    inference(equality_resolution,[],[f28])).
% 8.07/1.49  
% 8.07/1.49  fof(f29,plain,(
% 8.07/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 8.07/1.49    inference(cnf_transformation,[],[f21])).
% 8.07/1.49  
% 8.07/1.49  fof(f44,plain,(
% 8.07/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 8.07/1.49    inference(equality_resolution,[],[f29])).
% 8.07/1.49  
% 8.07/1.49  fof(f34,plain,(
% 8.07/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 8.07/1.49    inference(cnf_transformation,[],[f22])).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1,plain,
% 8.07/1.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 8.07/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 8.07/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 8.07/1.49      inference(cnf_transformation,[],[f31]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_578,plain,
% 8.07/1.49      ( k3_xboole_0(X0,X1) = X2
% 8.07/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 8.07/1.49      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_13,plain,
% 8.07/1.49      ( k1_setfam_1(k1_tarski(X0)) = X0 ),
% 8.07/1.49      inference(cnf_transformation,[],[f41]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_12,plain,
% 8.07/1.49      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
% 8.07/1.49      | k1_xboole_0 = X1
% 8.07/1.49      | k1_xboole_0 = X0 ),
% 8.07/1.49      inference(cnf_transformation,[],[f40]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_927,plain,
% 8.07/1.49      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
% 8.07/1.49      | k1_tarski(X0) = k1_xboole_0
% 8.07/1.49      | k1_xboole_0 = X1 ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_13,c_12]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_14,negated_conjecture,
% 8.07/1.49      ( k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
% 8.07/1.49      inference(cnf_transformation,[],[f43]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1134,plain,
% 8.07/1.49      ( k3_xboole_0(sK2,k1_setfam_1(k1_tarski(sK3))) != k3_xboole_0(sK2,sK3)
% 8.07/1.49      | k1_tarski(sK3) = k1_xboole_0
% 8.07/1.49      | k1_tarski(sK2) = k1_xboole_0 ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_927,c_14]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1138,plain,
% 8.07/1.49      ( k3_xboole_0(sK2,sK3) != k3_xboole_0(sK2,sK3)
% 8.07/1.49      | k1_tarski(sK3) = k1_xboole_0
% 8.07/1.49      | k1_tarski(sK2) = k1_xboole_0 ),
% 8.07/1.49      inference(demodulation,[status(thm)],[c_1134,c_13]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1139,plain,
% 8.07/1.49      ( k1_tarski(sK3) = k1_xboole_0 | k1_tarski(sK2) = k1_xboole_0 ),
% 8.07/1.49      inference(equality_resolution_simp,[status(thm)],[c_1138]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_10,plain,
% 8.07/1.49      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X1 = X0 ),
% 8.07/1.49      inference(cnf_transformation,[],[f38]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_569,plain,
% 8.07/1.49      ( X0 = X1
% 8.07/1.49      | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1241,plain,
% 8.07/1.49      ( k1_tarski(sK2) = k1_xboole_0
% 8.07/1.49      | sK3 = X0
% 8.07/1.49      | r1_xboole_0(k1_tarski(X0),k1_xboole_0) = iProver_top ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_1139,c_569]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_7,plain,
% 8.07/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 8.07/1.49      inference(cnf_transformation,[],[f33]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_572,plain,
% 8.07/1.49      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 8.07/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1530,plain,
% 8.07/1.49      ( k3_xboole_0(k1_tarski(X0),k1_xboole_0) = k1_xboole_0
% 8.07/1.49      | k1_tarski(sK2) = k1_xboole_0
% 8.07/1.49      | sK3 = X0 ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_1241,c_572]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_5,plain,
% 8.07/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 8.07/1.49      inference(cnf_transformation,[],[f46]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_574,plain,
% 8.07/1.49      ( r2_hidden(X0,X1) = iProver_top
% 8.07/1.49      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1662,plain,
% 8.07/1.49      ( k1_tarski(sK2) = k1_xboole_0
% 8.07/1.49      | sK3 = X0
% 8.07/1.49      | r2_hidden(X1,k1_tarski(X0)) = iProver_top
% 8.07/1.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_1530,c_574]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_8,plain,
% 8.07/1.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 8.07/1.49      inference(cnf_transformation,[],[f36]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_571,plain,
% 8.07/1.49      ( r1_xboole_0(X0,X1) != iProver_top
% 8.07/1.49      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_1659,plain,
% 8.07/1.49      ( k1_tarski(sK2) = k1_xboole_0
% 8.07/1.49      | sK3 = X0
% 8.07/1.49      | r1_xboole_0(k1_tarski(X0),k1_xboole_0) != iProver_top
% 8.07/1.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_1530,c_571]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_2407,plain,
% 8.07/1.49      ( sK3 = X0
% 8.07/1.49      | k1_tarski(sK2) = k1_xboole_0
% 8.07/1.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 8.07/1.49      inference(global_propositional_subsumption,
% 8.07/1.49                [status(thm)],
% 8.07/1.49                [c_1662,c_1241,c_1659]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_2408,plain,
% 8.07/1.49      ( k1_tarski(sK2) = k1_xboole_0
% 8.07/1.49      | sK3 = X0
% 8.07/1.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 8.07/1.49      inference(renaming,[status(thm)],[c_2407]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_2416,plain,
% 8.07/1.49      ( k3_xboole_0(X0,k1_xboole_0) = X1
% 8.07/1.49      | k1_tarski(sK2) = k1_xboole_0
% 8.07/1.49      | sK3 = X2
% 8.07/1.49      | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_578,c_2408]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_2475,plain,
% 8.07/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0
% 8.07/1.49      | k1_tarski(sK2) = k1_xboole_0
% 8.07/1.49      | sK3 = X1
% 8.07/1.49      | sK3 = X2 ),
% 8.07/1.49      inference(superposition,[status(thm)],[c_2416,c_2408]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_11,plain,
% 8.07/1.49      ( r2_hidden(X0,X1)
% 8.07/1.49      | k3_xboole_0(X1,k1_tarski(X0)) != k1_tarski(X0) ),
% 8.07/1.49      inference(cnf_transformation,[],[f39]) ).
% 8.07/1.49  
% 8.07/1.49  cnf(c_568,plain,
% 8.07/1.49      ( k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)
% 8.07/1.49      | r2_hidden(X1,X0) = iProver_top ),
% 8.07/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_1245,plain,
% 8.07/1.50      ( k3_xboole_0(X0,k1_xboole_0) != k1_tarski(sK3)
% 8.07/1.50      | k1_tarski(sK2) = k1_xboole_0
% 8.07/1.50      | r2_hidden(sK3,X0) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_1139,c_568]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_3367,plain,
% 8.07/1.50      ( k1_tarski(sK3) != k1_xboole_0
% 8.07/1.50      | k1_tarski(sK2) = k1_xboole_0
% 8.07/1.50      | sK3 = X0
% 8.07/1.50      | sK3 = X1
% 8.07/1.50      | r2_hidden(sK3,X2) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_2475,c_1245]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_3679,plain,
% 8.07/1.50      ( k1_tarski(sK2) = k1_xboole_0
% 8.07/1.50      | sK3 = X0
% 8.07/1.50      | sK3 = X1
% 8.07/1.50      | r2_hidden(sK3,X2) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_3367,c_1139]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_3695,plain,
% 8.07/1.50      ( k1_tarski(sK2) = k1_xboole_0 | sK3 = X0 | sK3 = X1 | sK3 = X2 ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_3679,c_2408]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_3993,plain,
% 8.07/1.50      ( k1_tarski(sK2) = k1_xboole_0
% 8.07/1.50      | sK3 = X0
% 8.07/1.50      | sK3 = X1
% 8.07/1.50      | sK3 != k1_xboole_0 ),
% 8.07/1.50      inference(equality_factoring,[status(thm)],[c_3695]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_4000,plain,
% 8.07/1.50      ( k1_tarski(sK2) = k1_xboole_0 | sK3 = X0 | sK3 = X1 ),
% 8.07/1.50      inference(forward_subsumption_resolution,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_3993,c_3695]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_4417,plain,
% 8.07/1.50      ( k1_tarski(sK2) = k1_xboole_0 | sK3 = X0 | sK3 != k1_xboole_0 ),
% 8.07/1.50      inference(equality_factoring,[status(thm)],[c_4000]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_4422,plain,
% 8.07/1.50      ( k1_tarski(sK2) = k1_xboole_0 | sK3 = X0 ),
% 8.07/1.50      inference(forward_subsumption_resolution,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_4417,c_4000]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_5962,plain,
% 8.07/1.50      ( k1_tarski(sK2) = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 8.07/1.50      inference(equality_factoring,[status(thm)],[c_4422]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_5965,plain,
% 8.07/1.50      ( k1_tarski(sK2) = k1_xboole_0 ),
% 8.07/1.50      inference(forward_subsumption_resolution,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_5962,c_4422]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_923,plain,
% 8.07/1.50      ( X0 = X1
% 8.07/1.50      | k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_569,c_572]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14821,plain,
% 8.07/1.50      ( k3_xboole_0(k1_tarski(X0),k1_xboole_0) = k1_xboole_0 | sK2 = X0 ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_5965,c_923]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_1132,plain,
% 8.07/1.50      ( k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
% 8.07/1.50      | k1_setfam_1(k2_xboole_0(k2_xboole_0(k1_tarski(X0),X1),X2)) = k3_xboole_0(k3_xboole_0(X0,k1_setfam_1(X1)),k1_setfam_1(X2))
% 8.07/1.50      | k1_tarski(X0) = k1_xboole_0
% 8.07/1.50      | k1_xboole_0 = X1
% 8.07/1.50      | k1_xboole_0 = X2 ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_927,c_12]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6056,plain,
% 8.07/1.50      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
% 8.07/1.50      | k1_setfam_1(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k1_setfam_1(X2))
% 8.07/1.50      | k1_tarski(X0) = k1_xboole_0
% 8.07/1.50      | k1_tarski(X1) = k1_xboole_0
% 8.07/1.50      | k1_xboole_0 = X2 ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_13,c_1132]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_928,plain,
% 8.07/1.50      ( k1_setfam_1(k2_xboole_0(X0,k1_tarski(X1))) = k3_xboole_0(k1_setfam_1(X0),X1)
% 8.07/1.50      | k1_tarski(X1) = k1_xboole_0
% 8.07/1.50      | k1_xboole_0 = X0 ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_13,c_12]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9239,plain,
% 8.07/1.50      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
% 8.07/1.50      | k3_xboole_0(k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),X2) = k3_xboole_0(k3_xboole_0(X0,X1),k1_setfam_1(k1_tarski(X2)))
% 8.07/1.50      | k1_tarski(X0) = k1_xboole_0
% 8.07/1.50      | k1_tarski(X1) = k1_xboole_0
% 8.07/1.50      | k1_tarski(X2) = k1_xboole_0 ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_6056,c_928]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_9363,plain,
% 8.07/1.50      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
% 8.07/1.50      | k3_xboole_0(k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),X2) = k3_xboole_0(k3_xboole_0(X0,X1),X2)
% 8.07/1.50      | k1_tarski(X0) = k1_xboole_0
% 8.07/1.50      | k1_tarski(X1) = k1_xboole_0
% 8.07/1.50      | k1_tarski(X2) = k1_xboole_0 ),
% 8.07/1.50      inference(demodulation,[status(thm)],[c_9239,c_13]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14824,plain,
% 8.07/1.50      ( k3_xboole_0(X0,k1_xboole_0) != k1_tarski(sK2)
% 8.07/1.50      | r2_hidden(sK2,X0) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_5965,c_568]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14833,plain,
% 8.07/1.50      ( k3_xboole_0(X0,k1_xboole_0) != k1_xboole_0
% 8.07/1.50      | r2_hidden(sK2,X0) = iProver_top ),
% 8.07/1.50      inference(light_normalisation,[status(thm)],[c_14824,c_5965]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21475,plain,
% 8.07/1.50      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
% 8.07/1.50      | k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) != k1_xboole_0
% 8.07/1.50      | k1_tarski(X0) = k1_xboole_0
% 8.07/1.50      | k1_tarski(X1) = k1_xboole_0
% 8.07/1.50      | k1_tarski(k1_xboole_0) = k1_xboole_0
% 8.07/1.50      | r2_hidden(sK2,k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_9363,c_14833]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_44585,plain,
% 8.07/1.50      ( k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)) = k1_xboole_0
% 8.07/1.50      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 8.07/1.50      | k1_tarski(k1_tarski(X0)) = k1_xboole_0
% 8.07/1.50      | k1_tarski(k1_xboole_0) = k1_xboole_0
% 8.07/1.50      | sK2 = X0
% 8.07/1.50      | r2_hidden(sK2,k1_setfam_1(k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)))) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14821,c_21475]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_2,plain,
% 8.07/1.50      ( r2_hidden(sK0(X0,X1,X2),X0)
% 8.07/1.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 8.07/1.50      | k3_xboole_0(X0,X1) = X2 ),
% 8.07/1.50      inference(cnf_transformation,[],[f30]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_43,plain,
% 8.07/1.50      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 8.07/1.50      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_0,plain,
% 8.07/1.50      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 8.07/1.50      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 8.07/1.50      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 8.07/1.50      | k3_xboole_0(X0,X1) = X2 ),
% 8.07/1.50      inference(cnf_transformation,[],[f32]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_47,plain,
% 8.07/1.50      ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 8.07/1.50      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_45084,plain,
% 8.07/1.50      ( k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)) = k1_xboole_0
% 8.07/1.50      | k1_tarski(k1_tarski(X0)) = k1_xboole_0
% 8.07/1.50      | k1_tarski(k1_xboole_0) = k1_xboole_0
% 8.07/1.50      | sK2 = X0
% 8.07/1.50      | r2_hidden(sK2,k1_setfam_1(k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)))) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_44585,c_43,c_47]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_4,plain,
% 8.07/1.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 8.07/1.50      inference(cnf_transformation,[],[f45]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_575,plain,
% 8.07/1.50      ( r2_hidden(X0,X1) = iProver_top
% 8.07/1.50      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 8.07/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_931,plain,
% 8.07/1.50      ( k1_xboole_0 = X0
% 8.07/1.50      | k1_xboole_0 = X1
% 8.07/1.50      | r2_hidden(X2,k1_setfam_1(X1)) = iProver_top
% 8.07/1.50      | r2_hidden(X2,k1_setfam_1(k2_xboole_0(X0,X1))) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_12,c_575]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_45101,plain,
% 8.07/1.50      ( k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)) = k1_xboole_0
% 8.07/1.50      | k1_tarski(k1_tarski(X0)) = k1_xboole_0
% 8.07/1.50      | k1_tarski(k1_xboole_0) = k1_xboole_0
% 8.07/1.50      | sK2 = X0
% 8.07/1.50      | r2_hidden(sK2,k1_setfam_1(k1_tarski(k1_xboole_0))) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_45084,c_931]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_45107,plain,
% 8.07/1.50      ( k2_xboole_0(k1_tarski(k1_tarski(X0)),k1_tarski(k1_xboole_0)) = k1_xboole_0
% 8.07/1.50      | k1_tarski(k1_tarski(X0)) = k1_xboole_0
% 8.07/1.50      | k1_tarski(k1_xboole_0) = k1_xboole_0
% 8.07/1.50      | sK2 = X0
% 8.07/1.50      | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 8.07/1.50      inference(demodulation,[status(thm)],[c_45101,c_13]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14865,plain,
% 8.07/1.50      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 8.07/1.50      | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_14833]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_46138,plain,
% 8.07/1.50      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_45107,c_43,c_47,c_14865]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14807,plain,
% 8.07/1.50      ( k3_xboole_0(k1_xboole_0,k1_tarski(X0)) = k1_xboole_0 | sK2 = X0 ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_5965,c_923]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21588,plain,
% 8.07/1.50      ( sK2 = X0
% 8.07/1.50      | r1_xboole_0(k1_xboole_0,k1_tarski(X0)) != iProver_top
% 8.07/1.50      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14807,c_571]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14812,plain,
% 8.07/1.50      ( sK2 = X0 | r1_xboole_0(k1_tarski(X0),k1_xboole_0) = iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_5965,c_569]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_21912,plain,
% 8.07/1.50      ( sK2 = X0
% 8.07/1.50      | r1_xboole_0(k1_tarski(X0),k1_xboole_0) != iProver_top
% 8.07/1.50      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_14821,c_571]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_22105,plain,
% 8.07/1.50      ( sK2 = X0 | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 8.07/1.50      inference(global_propositional_subsumption,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_21588,c_14812,c_21912]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_46143,plain,
% 8.07/1.50      ( sK2 = X0 ),
% 8.07/1.50      inference(superposition,[status(thm)],[c_46138,c_22105]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_46144,plain,
% 8.07/1.50      ( sK2 = k1_xboole_0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_46143]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_252,plain,
% 8.07/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.07/1.50      theory(equality) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_45157,plain,
% 8.07/1.50      ( r2_hidden(X0,X1)
% 8.07/1.50      | ~ r2_hidden(sK2,k1_xboole_0)
% 8.07/1.50      | X0 != sK2
% 8.07/1.50      | X1 != k1_xboole_0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_252]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_45164,plain,
% 8.07/1.50      ( ~ r2_hidden(sK2,k1_xboole_0)
% 8.07/1.50      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 8.07/1.50      | k1_xboole_0 != sK2
% 8.07/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_45157]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14864,plain,
% 8.07/1.50      ( r2_hidden(sK2,X0) | k3_xboole_0(X0,k1_xboole_0) != k1_xboole_0 ),
% 8.07/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_14833]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_14866,plain,
% 8.07/1.50      ( r2_hidden(sK2,k1_xboole_0)
% 8.07/1.50      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_14864]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_250,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_1372,plain,
% 8.07/1.50      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_250]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_1373,plain,
% 8.07/1.50      ( sK2 != k1_xboole_0
% 8.07/1.50      | k1_xboole_0 = sK2
% 8.07/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_1372]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_249,plain,( X0 = X0 ),theory(equality) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_264,plain,
% 8.07/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_249]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_3,plain,
% 8.07/1.50      ( ~ r2_hidden(X0,X1)
% 8.07/1.50      | ~ r2_hidden(X0,X2)
% 8.07/1.50      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 8.07/1.50      inference(cnf_transformation,[],[f44]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_40,plain,
% 8.07/1.50      ( r2_hidden(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 8.07/1.50      | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_6,plain,
% 8.07/1.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 8.07/1.50      inference(cnf_transformation,[],[f34]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_33,plain,
% 8.07/1.50      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 8.07/1.50      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(c_27,plain,
% 8.07/1.50      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 8.07/1.50      | ~ r2_hidden(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 8.07/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 8.07/1.50  
% 8.07/1.50  cnf(contradiction,plain,
% 8.07/1.50      ( $false ),
% 8.07/1.50      inference(minisat,
% 8.07/1.50                [status(thm)],
% 8.07/1.50                [c_46144,c_45164,c_14866,c_1373,c_264,c_47,c_43,c_40,
% 8.07/1.50                 c_33,c_27]) ).
% 8.07/1.50  
% 8.07/1.50  
% 8.07/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.07/1.50  
% 8.07/1.50  ------                               Statistics
% 8.07/1.50  
% 8.07/1.50  ------ General
% 8.07/1.50  
% 8.07/1.50  abstr_ref_over_cycles:                  0
% 8.07/1.50  abstr_ref_under_cycles:                 0
% 8.07/1.50  gc_basic_clause_elim:                   0
% 8.07/1.50  forced_gc_time:                         0
% 8.07/1.50  parsing_time:                           0.01
% 8.07/1.50  unif_index_cands_time:                  0.
% 8.07/1.50  unif_index_add_time:                    0.
% 8.07/1.50  orderings_time:                         0.
% 8.07/1.50  out_proof_time:                         0.011
% 8.07/1.50  total_time:                             0.934
% 8.07/1.50  num_of_symbols:                         42
% 8.07/1.50  num_of_terms:                           29033
% 8.07/1.50  
% 8.07/1.50  ------ Preprocessing
% 8.07/1.50  
% 8.07/1.50  num_of_splits:                          0
% 8.07/1.50  num_of_split_atoms:                     0
% 8.07/1.50  num_of_reused_defs:                     0
% 8.07/1.50  num_eq_ax_congr_red:                    10
% 8.07/1.50  num_of_sem_filtered_clauses:            1
% 8.07/1.50  num_of_subtypes:                        0
% 8.07/1.50  monotx_restored_types:                  0
% 8.07/1.50  sat_num_of_epr_types:                   0
% 8.07/1.50  sat_num_of_non_cyclic_types:            0
% 8.07/1.50  sat_guarded_non_collapsed_types:        0
% 8.07/1.50  num_pure_diseq_elim:                    0
% 8.07/1.50  simp_replaced_by:                       0
% 8.07/1.50  res_preprocessed:                       62
% 8.07/1.50  prep_upred:                             0
% 8.07/1.50  prep_unflattend:                        4
% 8.07/1.50  smt_new_axioms:                         0
% 8.07/1.50  pred_elim_cands:                        2
% 8.07/1.50  pred_elim:                              0
% 8.07/1.50  pred_elim_cl:                           0
% 8.07/1.50  pred_elim_cycles:                       1
% 8.07/1.50  merged_defs:                            6
% 8.07/1.50  merged_defs_ncl:                        0
% 8.07/1.50  bin_hyper_res:                          6
% 8.07/1.50  prep_cycles:                            3
% 8.07/1.50  pred_elim_time:                         0.001
% 8.07/1.50  splitting_time:                         0.
% 8.07/1.50  sem_filter_time:                        0.
% 8.07/1.50  monotx_time:                            0.
% 8.07/1.50  subtype_inf_time:                       0.
% 8.07/1.50  
% 8.07/1.50  ------ Problem properties
% 8.07/1.50  
% 8.07/1.50  clauses:                                15
% 8.07/1.50  conjectures:                            1
% 8.07/1.50  epr:                                    0
% 8.07/1.50  horn:                                   10
% 8.07/1.50  ground:                                 1
% 8.07/1.50  unary:                                  2
% 8.07/1.50  binary:                                 8
% 8.07/1.50  lits:                                   34
% 8.07/1.50  lits_eq:                                12
% 8.07/1.50  fd_pure:                                0
% 8.07/1.50  fd_pseudo:                              0
% 8.07/1.50  fd_cond:                                1
% 8.07/1.50  fd_pseudo_cond:                         4
% 8.07/1.50  ac_symbols:                             0
% 8.07/1.50  
% 8.07/1.50  ------ Propositional Solver
% 8.07/1.50  
% 8.07/1.50  prop_solver_calls:                      24
% 8.07/1.50  prop_fast_solver_calls:                 1244
% 8.07/1.50  smt_solver_calls:                       0
% 8.07/1.50  smt_fast_solver_calls:                  0
% 8.07/1.50  prop_num_of_clauses:                    6552
% 8.07/1.50  prop_preprocess_simplified:             10888
% 8.07/1.50  prop_fo_subsumed:                       153
% 8.07/1.50  prop_solver_time:                       0.
% 8.07/1.50  smt_solver_time:                        0.
% 8.07/1.50  smt_fast_solver_time:                   0.
% 8.07/1.50  prop_fast_solver_time:                  0.
% 8.07/1.50  prop_unsat_core_time:                   0.
% 8.07/1.50  
% 8.07/1.50  ------ QBF
% 8.07/1.50  
% 8.07/1.50  qbf_q_res:                              0
% 8.07/1.50  qbf_num_tautologies:                    0
% 8.07/1.50  qbf_prep_cycles:                        0
% 8.07/1.50  
% 8.07/1.50  ------ BMC1
% 8.07/1.50  
% 8.07/1.50  bmc1_current_bound:                     -1
% 8.07/1.50  bmc1_last_solved_bound:                 -1
% 8.07/1.50  bmc1_unsat_core_size:                   -1
% 8.07/1.50  bmc1_unsat_core_parents_size:           -1
% 8.07/1.50  bmc1_merge_next_fun:                    0
% 8.07/1.50  bmc1_unsat_core_clauses_time:           0.
% 8.07/1.50  
% 8.07/1.50  ------ Instantiation
% 8.07/1.50  
% 8.07/1.50  inst_num_of_clauses:                    1102
% 8.07/1.50  inst_num_in_passive:                    401
% 8.07/1.50  inst_num_in_active:                     457
% 8.07/1.50  inst_num_in_unprocessed:                245
% 8.07/1.50  inst_num_of_loops:                      700
% 8.07/1.50  inst_num_of_learning_restarts:          0
% 8.07/1.50  inst_num_moves_active_passive:          241
% 8.07/1.50  inst_lit_activity:                      0
% 8.07/1.50  inst_lit_activity_moves:                0
% 8.07/1.50  inst_num_tautologies:                   0
% 8.07/1.50  inst_num_prop_implied:                  0
% 8.07/1.50  inst_num_existing_simplified:           0
% 8.07/1.50  inst_num_eq_res_simplified:             0
% 8.07/1.50  inst_num_child_elim:                    0
% 8.07/1.50  inst_num_of_dismatching_blockings:      450
% 8.07/1.50  inst_num_of_non_proper_insts:           1260
% 8.07/1.50  inst_num_of_duplicates:                 0
% 8.07/1.50  inst_inst_num_from_inst_to_res:         0
% 8.07/1.50  inst_dismatching_checking_time:         0.
% 8.07/1.50  
% 8.07/1.50  ------ Resolution
% 8.07/1.50  
% 8.07/1.50  res_num_of_clauses:                     0
% 8.07/1.50  res_num_in_passive:                     0
% 8.07/1.50  res_num_in_active:                      0
% 8.07/1.50  res_num_of_loops:                       65
% 8.07/1.50  res_forward_subset_subsumed:            94
% 8.07/1.50  res_backward_subset_subsumed:           2
% 8.07/1.50  res_forward_subsumed:                   0
% 8.07/1.50  res_backward_subsumed:                  0
% 8.07/1.50  res_forward_subsumption_resolution:     0
% 8.07/1.50  res_backward_subsumption_resolution:    0
% 8.07/1.50  res_clause_to_clause_subsumption:       19273
% 8.07/1.50  res_orphan_elimination:                 0
% 8.07/1.50  res_tautology_del:                      78
% 8.07/1.50  res_num_eq_res_simplified:              0
% 8.07/1.50  res_num_sel_changes:                    0
% 8.07/1.50  res_moves_from_active_to_pass:          0
% 8.07/1.50  
% 8.07/1.50  ------ Superposition
% 8.07/1.50  
% 8.07/1.50  sup_time_total:                         0.
% 8.07/1.50  sup_time_generating:                    0.
% 8.07/1.50  sup_time_sim_full:                      0.
% 8.07/1.50  sup_time_sim_immed:                     0.
% 8.07/1.50  
% 8.07/1.50  sup_num_of_clauses:                     1987
% 8.07/1.50  sup_num_in_active:                      113
% 8.07/1.50  sup_num_in_passive:                     1874
% 8.07/1.50  sup_num_of_loops:                       139
% 8.07/1.50  sup_fw_superposition:                   1365
% 8.07/1.50  sup_bw_superposition:                   2304
% 8.07/1.50  sup_immediate_simplified:               812
% 8.07/1.50  sup_given_eliminated:                   0
% 8.07/1.50  comparisons_done:                       0
% 8.07/1.50  comparisons_avoided:                    467
% 8.07/1.50  
% 8.07/1.50  ------ Simplifications
% 8.07/1.50  
% 8.07/1.50  
% 8.07/1.50  sim_fw_subset_subsumed:                 387
% 8.07/1.50  sim_bw_subset_subsumed:                 42
% 8.07/1.50  sim_fw_subsumed:                        261
% 8.07/1.50  sim_bw_subsumed:                        6
% 8.07/1.50  sim_fw_subsumption_res:                 32
% 8.07/1.50  sim_bw_subsumption_res:                 0
% 8.07/1.50  sim_tautology_del:                      40
% 8.07/1.50  sim_eq_tautology_del:                   117
% 8.07/1.50  sim_eq_res_simp:                        22
% 8.07/1.50  sim_fw_demodulated:                     159
% 8.07/1.50  sim_bw_demodulated:                     9
% 8.07/1.50  sim_light_normalised:                   52
% 8.07/1.50  sim_joinable_taut:                      0
% 8.07/1.50  sim_joinable_simp:                      0
% 8.07/1.50  sim_ac_normalised:                      0
% 8.07/1.50  sim_smt_subsumption:                    0
% 8.07/1.50  
%------------------------------------------------------------------------------
