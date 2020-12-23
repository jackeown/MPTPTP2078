%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:26 EST 2020

% Result     : Theorem 19.83s
% Output     : CNFRefutation 19.83s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 117 expanded)
%              Number of clauses        :   29 (  30 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  221 ( 314 expanded)
%              Number of equality atoms :   68 ( 105 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k8_relat_1(sK2,sK3)) != sK2
      & r1_tarski(sK2,k2_relat_1(sK3))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k2_relat_1(k8_relat_1(sK2,sK3)) != sK2
    & r1_tarski(sK2,k2_relat_1(sK3))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f28])).

fof(f49,plain,(
    r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f52,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f51,f51])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f39,f51])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f48,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    k2_relat_1(k8_relat_1(sK2,sK3)) != sK2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1726,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1727,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1730,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2326,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_1730])).

cnf(c_2567,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_2326])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_217,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | k2_relat_1(sK3) != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_218,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
    | r1_xboole_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_1722,plain,
    ( r1_xboole_0(k2_relat_1(sK3),X0) != iProver_top
    | r1_xboole_0(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_2730,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(X0,k2_relat_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2567,c_1722])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1724,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2814,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_relat_1(sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_2730,c_1724])).

cnf(c_12,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1952,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_13])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_210,plain,
    ( k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_211,plain,
    ( k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),X0)) = k2_relat_1(k8_relat_1(X0,sK3)) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_1991,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK3))) = k2_relat_1(k8_relat_1(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_1952,c_211])).

cnf(c_2024,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_relat_1(sK3))) = k2_relat_1(k8_relat_1(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_1991,c_13])).

cnf(c_66001,plain,
    ( k2_relat_1(k8_relat_1(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_2814,c_2024])).

cnf(c_15,negated_conjecture,
    ( k2_relat_1(k8_relat_1(sK2,sK3)) != sK2 ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66001,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:07:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.83/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.83/2.99  
% 19.83/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.83/2.99  
% 19.83/2.99  ------  iProver source info
% 19.83/2.99  
% 19.83/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.83/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.83/2.99  git: non_committed_changes: false
% 19.83/2.99  git: last_make_outside_of_git: false
% 19.83/2.99  
% 19.83/2.99  ------ 
% 19.83/2.99  ------ Parsing...
% 19.83/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/2.99  ------ Proving...
% 19.83/2.99  ------ Problem Properties 
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  clauses                                 16
% 19.83/2.99  conjectures                             3
% 19.83/2.99  EPR                                     1
% 19.83/2.99  Horn                                    10
% 19.83/2.99  unary                                   4
% 19.83/2.99  binary                                  7
% 19.83/2.99  lits                                    34
% 19.83/2.99  lits eq                                 9
% 19.83/2.99  fd_pure                                 0
% 19.83/2.99  fd_pseudo                               0
% 19.83/2.99  fd_cond                                 0
% 19.83/2.99  fd_pseudo_cond                          3
% 19.83/2.99  AC symbols                              0
% 19.83/2.99  
% 19.83/2.99  ------ Input Options Time Limit: Unbounded
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 19.83/2.99  Current options:
% 19.83/2.99  ------ 
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ Proving...
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/2.99  
% 19.83/2.99  ------ Proving...
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/2.99  
% 19.83/2.99  ------ Proving...
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/2.99  
% 19.83/2.99  ------ Proving...
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/2.99  
% 19.83/2.99  ------ Proving...
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/2.99  
% 19.83/2.99  ------ Proving...
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.83/2.99  
% 19.83/2.99  ------ Proving...
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  % SZS status Theorem for theBenchmark.p
% 19.83/2.99  
% 19.83/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.83/2.99  
% 19.83/2.99  fof(f2,axiom,(
% 19.83/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f13,plain,(
% 19.83/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.83/2.99    inference(rectify,[],[f2])).
% 19.83/2.99  
% 19.83/2.99  fof(f14,plain,(
% 19.83/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.83/2.99    inference(ennf_transformation,[],[f13])).
% 19.83/2.99  
% 19.83/2.99  fof(f25,plain,(
% 19.83/2.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 19.83/2.99    introduced(choice_axiom,[])).
% 19.83/2.99  
% 19.83/2.99  fof(f26,plain,(
% 19.83/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.83/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f25])).
% 19.83/2.99  
% 19.83/2.99  fof(f36,plain,(
% 19.83/2.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f26])).
% 19.83/2.99  
% 19.83/2.99  fof(f37,plain,(
% 19.83/2.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f26])).
% 19.83/2.99  
% 19.83/2.99  fof(f1,axiom,(
% 19.83/2.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f20,plain,(
% 19.83/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.83/2.99    inference(nnf_transformation,[],[f1])).
% 19.83/2.99  
% 19.83/2.99  fof(f21,plain,(
% 19.83/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.83/2.99    inference(flattening,[],[f20])).
% 19.83/2.99  
% 19.83/2.99  fof(f22,plain,(
% 19.83/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.83/2.99    inference(rectify,[],[f21])).
% 19.83/2.99  
% 19.83/2.99  fof(f23,plain,(
% 19.83/2.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.83/2.99    introduced(choice_axiom,[])).
% 19.83/2.99  
% 19.83/2.99  fof(f24,plain,(
% 19.83/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.83/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 19.83/2.99  
% 19.83/2.99  fof(f31,plain,(
% 19.83/2.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.83/2.99    inference(cnf_transformation,[],[f24])).
% 19.83/2.99  
% 19.83/2.99  fof(f56,plain,(
% 19.83/2.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 19.83/2.99    inference(equality_resolution,[],[f31])).
% 19.83/2.99  
% 19.83/2.99  fof(f4,axiom,(
% 19.83/2.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f15,plain,(
% 19.83/2.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.83/2.99    inference(ennf_transformation,[],[f4])).
% 19.83/2.99  
% 19.83/2.99  fof(f16,plain,(
% 19.83/2.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 19.83/2.99    inference(flattening,[],[f15])).
% 19.83/2.99  
% 19.83/2.99  fof(f40,plain,(
% 19.83/2.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f16])).
% 19.83/2.99  
% 19.83/2.99  fof(f11,conjecture,(
% 19.83/2.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f12,negated_conjecture,(
% 19.83/2.99    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 19.83/2.99    inference(negated_conjecture,[],[f11])).
% 19.83/2.99  
% 19.83/2.99  fof(f18,plain,(
% 19.83/2.99    ? [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 19.83/2.99    inference(ennf_transformation,[],[f12])).
% 19.83/2.99  
% 19.83/2.99  fof(f19,plain,(
% 19.83/2.99    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1))),
% 19.83/2.99    inference(flattening,[],[f18])).
% 19.83/2.99  
% 19.83/2.99  fof(f28,plain,(
% 19.83/2.99    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1)) => (k2_relat_1(k8_relat_1(sK2,sK3)) != sK2 & r1_tarski(sK2,k2_relat_1(sK3)) & v1_relat_1(sK3))),
% 19.83/2.99    introduced(choice_axiom,[])).
% 19.83/2.99  
% 19.83/2.99  fof(f29,plain,(
% 19.83/2.99    k2_relat_1(k8_relat_1(sK2,sK3)) != sK2 & r1_tarski(sK2,k2_relat_1(sK3)) & v1_relat_1(sK3)),
% 19.83/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f28])).
% 19.83/2.99  
% 19.83/2.99  fof(f49,plain,(
% 19.83/2.99    r1_tarski(sK2,k2_relat_1(sK3))),
% 19.83/2.99    inference(cnf_transformation,[],[f29])).
% 19.83/2.99  
% 19.83/2.99  fof(f5,axiom,(
% 19.83/2.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f27,plain,(
% 19.83/2.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 19.83/2.99    inference(nnf_transformation,[],[f5])).
% 19.83/2.99  
% 19.83/2.99  fof(f41,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f27])).
% 19.83/2.99  
% 19.83/2.99  fof(f6,axiom,(
% 19.83/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f43,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f6])).
% 19.83/2.99  
% 19.83/2.99  fof(f7,axiom,(
% 19.83/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f44,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f7])).
% 19.83/2.99  
% 19.83/2.99  fof(f8,axiom,(
% 19.83/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f45,plain,(
% 19.83/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f8])).
% 19.83/2.99  
% 19.83/2.99  fof(f51,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.83/2.99    inference(definition_unfolding,[],[f44,f45])).
% 19.83/2.99  
% 19.83/2.99  fof(f52,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 19.83/2.99    inference(definition_unfolding,[],[f43,f51,f51])).
% 19.83/2.99  
% 19.83/2.99  fof(f9,axiom,(
% 19.83/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f46,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.83/2.99    inference(cnf_transformation,[],[f9])).
% 19.83/2.99  
% 19.83/2.99  fof(f3,axiom,(
% 19.83/2.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f39,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f3])).
% 19.83/2.99  
% 19.83/2.99  fof(f53,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 19.83/2.99    inference(definition_unfolding,[],[f46,f39,f51])).
% 19.83/2.99  
% 19.83/2.99  fof(f10,axiom,(
% 19.83/2.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f17,plain,(
% 19.83/2.99    ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 19.83/2.99    inference(ennf_transformation,[],[f10])).
% 19.83/2.99  
% 19.83/2.99  fof(f47,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f17])).
% 19.83/2.99  
% 19.83/2.99  fof(f54,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 19.83/2.99    inference(definition_unfolding,[],[f47,f39])).
% 19.83/2.99  
% 19.83/2.99  fof(f48,plain,(
% 19.83/2.99    v1_relat_1(sK3)),
% 19.83/2.99    inference(cnf_transformation,[],[f29])).
% 19.83/2.99  
% 19.83/2.99  fof(f50,plain,(
% 19.83/2.99    k2_relat_1(k8_relat_1(sK2,sK3)) != sK2),
% 19.83/2.99    inference(cnf_transformation,[],[f29])).
% 19.83/2.99  
% 19.83/2.99  cnf(c_8,plain,
% 19.83/2.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 19.83/2.99      inference(cnf_transformation,[],[f36]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1726,plain,
% 19.83/2.99      ( r1_xboole_0(X0,X1) = iProver_top
% 19.83/2.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_7,plain,
% 19.83/2.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 19.83/2.99      inference(cnf_transformation,[],[f37]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1727,plain,
% 19.83/2.99      ( r1_xboole_0(X0,X1) = iProver_top
% 19.83/2.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_4,negated_conjecture,
% 19.83/2.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 19.83/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1730,plain,
% 19.83/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.83/2.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2326,plain,
% 19.83/2.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 19.83/2.99      | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_1727,c_1730]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2567,plain,
% 19.83/2.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_1726,c_2326]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_9,plain,
% 19.83/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 19.83/2.99      inference(cnf_transformation,[],[f40]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_16,negated_conjecture,
% 19.83/2.99      ( r1_tarski(sK2,k2_relat_1(sK3)) ),
% 19.83/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_217,plain,
% 19.83/2.99      ( ~ r1_xboole_0(X0,X1)
% 19.83/2.99      | r1_xboole_0(X2,X1)
% 19.83/2.99      | k2_relat_1(sK3) != X0
% 19.83/2.99      | sK2 != X2 ),
% 19.83/2.99      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_218,plain,
% 19.83/2.99      ( ~ r1_xboole_0(k2_relat_1(sK3),X0) | r1_xboole_0(sK2,X0) ),
% 19.83/2.99      inference(unflattening,[status(thm)],[c_217]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1722,plain,
% 19.83/2.99      ( r1_xboole_0(k2_relat_1(sK3),X0) != iProver_top
% 19.83/2.99      | r1_xboole_0(sK2,X0) = iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2730,plain,
% 19.83/2.99      ( r1_xboole_0(sK2,k4_xboole_0(X0,k2_relat_1(sK3))) = iProver_top ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_2567,c_1722]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_11,plain,
% 19.83/2.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 19.83/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1724,plain,
% 19.83/2.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2814,plain,
% 19.83/2.99      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_relat_1(sK3))) = sK2 ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_2730,c_1724]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_12,plain,
% 19.83/2.99      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 19.83/2.99      inference(cnf_transformation,[],[f52]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_13,plain,
% 19.83/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.83/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1952,plain,
% 19.83/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_12,c_13]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_14,plain,
% 19.83/2.99      ( ~ v1_relat_1(X0)
% 19.83/2.99      | k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 19.83/2.99      inference(cnf_transformation,[],[f54]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_17,negated_conjecture,
% 19.83/2.99      ( v1_relat_1(sK3) ),
% 19.83/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_210,plain,
% 19.83/2.99      ( k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
% 19.83/2.99      | sK3 != X0 ),
% 19.83/2.99      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_211,plain,
% 19.83/2.99      ( k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),X0)) = k2_relat_1(k8_relat_1(X0,sK3)) ),
% 19.83/2.99      inference(unflattening,[status(thm)],[c_210]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1991,plain,
% 19.83/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK3))) = k2_relat_1(k8_relat_1(X0,sK3)) ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_1952,c_211]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2024,plain,
% 19.83/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_relat_1(sK3))) = k2_relat_1(k8_relat_1(X0,sK3)) ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_1991,c_13]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_66001,plain,
% 19.83/2.99      ( k2_relat_1(k8_relat_1(sK2,sK3)) = sK2 ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_2814,c_2024]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_15,negated_conjecture,
% 19.83/2.99      ( k2_relat_1(k8_relat_1(sK2,sK3)) != sK2 ),
% 19.83/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(contradiction,plain,
% 19.83/2.99      ( $false ),
% 19.83/2.99      inference(minisat,[status(thm)],[c_66001,c_15]) ).
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.83/2.99  
% 19.83/2.99  ------                               Statistics
% 19.83/2.99  
% 19.83/2.99  ------ Selected
% 19.83/2.99  
% 19.83/2.99  total_time:                             2.148
% 19.83/2.99  
%------------------------------------------------------------------------------
