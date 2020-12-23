%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:55 EST 2020

% Result     : Theorem 19.53s
% Output     : CNFRefutation 19.53s
% Verified   : 
% Statistics : Number of formulae       :  124 (6889 expanded)
%              Number of clauses        :   71 (1680 expanded)
%              Number of leaves         :   11 (1612 expanded)
%              Depth                    :   33
%              Number of atoms          :  354 (20294 expanded)
%              Number of equality atoms :  195 (7745 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) != k9_relat_1(X1,k10_relat_1(X1,X0))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) != k9_relat_1(X1,k10_relat_1(X1,X0))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) != k9_relat_1(X1,k10_relat_1(X1,X0))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k3_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k3_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f22])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    k3_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,k1_relat_1(sK2)))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(definition_unfolding,[],[f39,f41])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_362,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_353,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_357,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_354,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_745,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)))) = k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_354])).

cnf(c_1152,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_353,c_745])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_352,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_355,plain,
    ( k10_relat_1(X0,k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_881,plain,
    ( k10_relat_1(sK2,k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0))) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_352,c_355])).

cnf(c_1153,plain,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1152,c_881])).

cnf(c_13,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1158,plain,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1153,c_13])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_359,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1166,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_359])).

cnf(c_1600,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(sK2,k10_relat_1(sK2,X2))
    | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_362,c_1166])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_358,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2117,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X3))
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_relat_1(sK2,k10_relat_1(sK2,X3))),X3) = iProver_top
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_relat_1(sK2,k10_relat_1(sK2,X3))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_358])).

cnf(c_1594,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = X3
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3),X3) = iProver_top
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_362,c_358])).

cnf(c_1167,plain,
    ( r2_hidden(X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_358])).

cnf(c_1599,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(sK2,k10_relat_1(sK2,X2))
    | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_362,c_1167])).

cnf(c_3328,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X3))
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_relat_1(sK2,k10_relat_1(sK2,X3))),X2) = iProver_top
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_relat_1(sK2,k10_relat_1(sK2,X3))),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_359])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_360,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1165,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_360])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_361,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1466,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(sK2,k10_relat_1(sK2,X2))
    | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_361,c_1167])).

cnf(c_2430,plain,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))),k2_relat_1(sK2)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1466])).

cnf(c_2432,plain,
    ( k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))),k2_relat_1(sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2430])).

cnf(c_2435,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2432,c_1158])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_363,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2626,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))),k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_363])).

cnf(c_2631,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X1) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),k9_relat_1(sK2,k10_relat_1(sK2,X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2626,c_1158])).

cnf(c_2651,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X1) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1165,c_2631])).

cnf(c_2889,plain,
    ( r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X1) != iProver_top
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2651,c_2435])).

cnf(c_2890,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X1) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2889])).

cnf(c_2902,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k9_relat_1(sK2,k10_relat_1(sK2,X2))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k9_relat_1(sK2,k10_relat_1(sK2,X2))),X1) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k9_relat_1(sK2,k10_relat_1(sK2,X2))),X0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k9_relat_1(sK2,k10_relat_1(sK2,X2))),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_360,c_2890])).

cnf(c_61705,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X1) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3328,c_2902])).

cnf(c_61932,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X1) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_61705,c_2902])).

cnf(c_1601,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
    | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_362])).

cnf(c_1603,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
    | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1601])).

cnf(c_9617,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_359])).

cnf(c_9680,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9617,c_363])).

cnf(c_9881,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9680,c_1603])).

cnf(c_9930,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_9881,c_1158])).

cnf(c_61933,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X1) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_61932,c_1158,c_9930])).

cnf(c_63597,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),k9_relat_1(sK2,k10_relat_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_61933])).

cnf(c_1162,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))) = k10_relat_1(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_1158,c_881])).

cnf(c_63618,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_relat_1(sK2)))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X1,X1,X1,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),k9_relat_1(sK2,k10_relat_1(sK2,X0))) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X1,X1,X1,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))))),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_61933])).

cnf(c_63622,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_63618,c_1162])).

cnf(c_63672,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_63597,c_63622])).

cnf(c_63673,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_63672,c_1158,c_9930])).

cnf(c_63730,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2117,c_63673])).

cnf(c_63760,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
    | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_63730,c_63673])).

cnf(c_63761,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_63760,c_1158,c_9930])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_356,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_585,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_352,c_356])).

cnf(c_10,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,k1_relat_1(sK2)))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_587,plain,
    ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k2_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_585,c_10])).

cnf(c_63999,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_63761,c_587])).

cnf(c_64005,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_63999])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:12:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.53/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.53/2.99  
% 19.53/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.53/2.99  
% 19.53/2.99  ------  iProver source info
% 19.53/2.99  
% 19.53/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.53/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.53/2.99  git: non_committed_changes: false
% 19.53/2.99  git: last_make_outside_of_git: false
% 19.53/2.99  
% 19.53/2.99  ------ 
% 19.53/2.99  ------ Parsing...
% 19.53/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.53/2.99  
% 19.53/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.53/2.99  
% 19.53/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.53/2.99  
% 19.53/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.53/2.99  ------ Proving...
% 19.53/2.99  ------ Problem Properties 
% 19.53/2.99  
% 19.53/2.99  
% 19.53/2.99  clauses                                 13
% 19.53/2.99  conjectures                             3
% 19.53/2.99  EPR                                     2
% 19.53/2.99  Horn                                    11
% 19.53/2.99  unary                                   4
% 19.53/2.99  binary                                  4
% 19.53/2.99  lits                                    29
% 19.53/2.99  lits eq                                 7
% 19.53/2.99  fd_pure                                 0
% 19.53/2.99  fd_pseudo                               0
% 19.53/2.99  fd_cond                                 0
% 19.53/2.99  fd_pseudo_cond                          3
% 19.53/2.99  AC symbols                              0
% 19.53/2.99  
% 19.53/2.99  ------ Input Options Time Limit: Unbounded
% 19.53/2.99  
% 19.53/2.99  
% 19.53/2.99  ------ 
% 19.53/2.99  Current options:
% 19.53/2.99  ------ 
% 19.53/2.99  
% 19.53/2.99  
% 19.53/2.99  
% 19.53/2.99  
% 19.53/2.99  ------ Proving...
% 19.53/2.99  
% 19.53/2.99  
% 19.53/2.99  % SZS status Theorem for theBenchmark.p
% 19.53/2.99  
% 19.53/2.99   Resolution empty clause
% 19.53/2.99  
% 19.53/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.53/2.99  
% 19.53/2.99  fof(f1,axiom,(
% 19.53/2.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.53/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.53/2.99  
% 19.53/2.99  fof(f17,plain,(
% 19.53/2.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.53/2.99    inference(nnf_transformation,[],[f1])).
% 19.53/2.99  
% 19.53/2.99  fof(f18,plain,(
% 19.53/2.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.53/2.99    inference(flattening,[],[f17])).
% 19.53/2.99  
% 19.53/2.99  fof(f19,plain,(
% 19.53/2.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.53/2.99    inference(rectify,[],[f18])).
% 19.53/2.99  
% 19.53/2.99  fof(f20,plain,(
% 19.53/2.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.53/2.99    introduced(choice_axiom,[])).
% 19.53/2.99  
% 19.53/2.99  fof(f21,plain,(
% 19.53/2.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 19.53/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 19.53/2.99  
% 19.53/2.99  fof(f28,plain,(
% 19.53/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.53/2.99    inference(cnf_transformation,[],[f21])).
% 19.53/2.99  
% 19.53/2.99  fof(f5,axiom,(
% 19.53/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.53/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.53/2.99  
% 19.53/2.99  fof(f33,plain,(
% 19.53/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.53/2.99    inference(cnf_transformation,[],[f5])).
% 19.53/2.99  
% 19.53/2.99  fof(f3,axiom,(
% 19.53/2.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.53/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.53/2.99  
% 19.53/2.99  fof(f31,plain,(
% 19.53/2.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.53/2.99    inference(cnf_transformation,[],[f3])).
% 19.53/2.99  
% 19.53/2.99  fof(f4,axiom,(
% 19.53/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.53/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.53/2.99  
% 19.53/2.99  fof(f32,plain,(
% 19.53/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.53/2.99    inference(cnf_transformation,[],[f4])).
% 19.53/2.99  
% 19.53/2.99  fof(f40,plain,(
% 19.53/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.53/2.99    inference(definition_unfolding,[],[f31,f32])).
% 19.53/2.99  
% 19.53/2.99  fof(f41,plain,(
% 19.53/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 19.53/2.99    inference(definition_unfolding,[],[f33,f40])).
% 19.53/2.99  
% 19.53/2.99  fof(f43,plain,(
% 19.53/2.99    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.53/2.99    inference(definition_unfolding,[],[f28,f41])).
% 19.53/2.99  
% 19.53/2.99  fof(f9,conjecture,(
% 19.53/2.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 19.53/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.53/2.99  
% 19.53/2.99  fof(f10,negated_conjecture,(
% 19.53/2.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 19.53/2.99    inference(negated_conjecture,[],[f9])).
% 19.53/2.99  
% 19.53/2.99  fof(f15,plain,(
% 19.53/2.99    ? [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) != k9_relat_1(X1,k10_relat_1(X1,X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 19.53/2.99    inference(ennf_transformation,[],[f10])).
% 19.53/2.99  
% 19.53/2.99  fof(f16,plain,(
% 19.53/2.99    ? [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) != k9_relat_1(X1,k10_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 19.53/2.99    inference(flattening,[],[f15])).
% 19.53/2.99  
% 19.53/2.99  fof(f22,plain,(
% 19.53/2.99    ? [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) != k9_relat_1(X1,k10_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k3_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 19.53/2.99    introduced(choice_axiom,[])).
% 19.53/2.99  
% 19.53/2.99  fof(f23,plain,(
% 19.53/2.99    k3_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 19.53/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f22])).
% 19.53/2.99  
% 19.53/2.99  fof(f38,plain,(
% 19.53/2.99    v1_funct_1(sK2)),
% 19.53/2.99    inference(cnf_transformation,[],[f23])).
% 19.53/2.99  
% 19.53/2.99  fof(f2,axiom,(
% 19.53/2.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.53/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.53/2.99  
% 19.53/2.99  fof(f30,plain,(
% 19.53/2.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.53/2.99    inference(cnf_transformation,[],[f2])).
% 19.53/2.99  
% 19.53/2.99  fof(f48,plain,(
% 19.53/2.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 19.53/2.99    inference(definition_unfolding,[],[f30,f41])).
% 19.53/2.99  
% 19.53/2.99  fof(f8,axiom,(
% 19.53/2.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 19.53/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.53/2.99  
% 19.53/2.99  fof(f13,plain,(
% 19.53/2.99    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.53/2.99    inference(ennf_transformation,[],[f8])).
% 19.53/2.99  
% 19.53/2.99  fof(f14,plain,(
% 19.53/2.99    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.53/2.99    inference(flattening,[],[f13])).
% 19.53/2.99  
% 19.53/2.99  fof(f36,plain,(
% 19.53/2.99    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.53/2.99    inference(cnf_transformation,[],[f14])).
% 19.53/2.99  
% 19.53/2.99  fof(f37,plain,(
% 19.53/2.99    v1_relat_1(sK2)),
% 19.53/2.99    inference(cnf_transformation,[],[f23])).
% 19.53/2.99  
% 19.53/2.99  fof(f7,axiom,(
% 19.53/2.99    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 19.53/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.53/2.99  
% 19.53/2.99  fof(f12,plain,(
% 19.53/2.99    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.53/2.99    inference(ennf_transformation,[],[f7])).
% 19.53/2.99  
% 19.53/2.99  fof(f35,plain,(
% 19.53/2.99    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 19.53/2.99    inference(cnf_transformation,[],[f12])).
% 19.53/2.99  
% 19.53/2.99  fof(f49,plain,(
% 19.53/2.99    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 19.53/2.99    inference(definition_unfolding,[],[f35,f41])).
% 19.53/2.99  
% 19.53/2.99  fof(f25,plain,(
% 19.53/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 19.53/2.99    inference(cnf_transformation,[],[f21])).
% 19.53/2.99  
% 19.53/2.99  fof(f46,plain,(
% 19.53/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 19.53/2.99    inference(definition_unfolding,[],[f25,f41])).
% 19.53/2.99  
% 19.53/2.99  fof(f52,plain,(
% 19.53/2.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 19.53/2.99    inference(equality_resolution,[],[f46])).
% 19.53/2.99  
% 19.53/2.99  fof(f24,plain,(
% 19.53/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 19.53/2.99    inference(cnf_transformation,[],[f21])).
% 19.53/2.99  
% 19.53/2.99  fof(f47,plain,(
% 19.53/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 19.53/2.99    inference(definition_unfolding,[],[f24,f41])).
% 19.53/2.99  
% 19.53/2.99  fof(f53,plain,(
% 19.53/2.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 19.53/2.99    inference(equality_resolution,[],[f47])).
% 19.53/2.99  
% 19.53/2.99  fof(f26,plain,(
% 19.53/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 19.53/2.99    inference(cnf_transformation,[],[f21])).
% 19.53/2.99  
% 19.53/2.99  fof(f45,plain,(
% 19.53/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 19.53/2.99    inference(definition_unfolding,[],[f26,f41])).
% 19.53/2.99  
% 19.53/2.99  fof(f51,plain,(
% 19.53/2.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 19.53/2.99    inference(equality_resolution,[],[f45])).
% 19.53/2.99  
% 19.53/2.99  fof(f27,plain,(
% 19.53/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.53/2.99    inference(cnf_transformation,[],[f21])).
% 19.53/2.99  
% 19.53/2.99  fof(f44,plain,(
% 19.53/2.99    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.53/2.99    inference(definition_unfolding,[],[f27,f41])).
% 19.53/2.99  
% 19.53/2.99  fof(f29,plain,(
% 19.53/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.53/2.99    inference(cnf_transformation,[],[f21])).
% 19.53/2.99  
% 19.53/2.99  fof(f42,plain,(
% 19.53/2.99    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.53/2.99    inference(definition_unfolding,[],[f29,f41])).
% 19.53/2.99  
% 19.53/2.99  fof(f6,axiom,(
% 19.53/2.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 19.53/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.53/2.99  
% 19.53/2.99  fof(f11,plain,(
% 19.53/2.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 19.53/2.99    inference(ennf_transformation,[],[f6])).
% 19.53/2.99  
% 19.53/2.99  fof(f34,plain,(
% 19.53/2.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.53/2.99    inference(cnf_transformation,[],[f11])).
% 19.53/2.99  
% 19.53/2.99  fof(f39,plain,(
% 19.53/2.99    k3_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 19.53/2.99    inference(cnf_transformation,[],[f23])).
% 19.53/2.99  
% 19.53/2.99  fof(f50,plain,(
% 19.53/2.99    k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,k1_relat_1(sK2)))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 19.53/2.99    inference(definition_unfolding,[],[f39,f41])).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1,plain,
% 19.53/2.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.53/2.99      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
% 19.53/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_362,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_11,negated_conjecture,
% 19.53/2.99      ( v1_funct_1(sK2) ),
% 19.53/2.99      inference(cnf_transformation,[],[f38]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_353,plain,
% 19.53/2.99      ( v1_funct_1(sK2) = iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_6,plain,
% 19.53/2.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 19.53/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_357,plain,
% 19.53/2.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_9,plain,
% 19.53/2.99      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 19.53/2.99      | ~ v1_funct_1(X1)
% 19.53/2.99      | ~ v1_relat_1(X1)
% 19.53/2.99      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 19.53/2.99      inference(cnf_transformation,[],[f36]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_354,plain,
% 19.53/2.99      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 19.53/2.99      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 19.53/2.99      | v1_funct_1(X0) != iProver_top
% 19.53/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_745,plain,
% 19.53/2.99      ( k9_relat_1(X0,k10_relat_1(X0,k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)))) = k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1))
% 19.53/2.99      | v1_funct_1(X0) != iProver_top
% 19.53/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_357,c_354]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1152,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0))
% 19.53/2.99      | v1_relat_1(sK2) != iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_353,c_745]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_12,negated_conjecture,
% 19.53/2.99      ( v1_relat_1(sK2) ),
% 19.53/2.99      inference(cnf_transformation,[],[f37]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_352,plain,
% 19.53/2.99      ( v1_relat_1(sK2) = iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_8,plain,
% 19.53/2.99      ( ~ v1_relat_1(X0)
% 19.53/2.99      | k10_relat_1(X0,k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 19.53/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_355,plain,
% 19.53/2.99      ( k10_relat_1(X0,k1_setfam_1(k2_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 19.53/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_881,plain,
% 19.53/2.99      ( k10_relat_1(sK2,k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0))) = k10_relat_1(sK2,X0) ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_352,c_355]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1153,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 19.53/2.99      | v1_relat_1(sK2) != iProver_top ),
% 19.53/2.99      inference(light_normalisation,[status(thm)],[c_1152,c_881]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_13,plain,
% 19.53/2.99      ( v1_relat_1(sK2) = iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1158,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 19.53/2.99      inference(global_propositional_subsumption,[status(thm)],[c_1153,c_13]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_4,plain,
% 19.53/2.99      ( r2_hidden(X0,X1)
% 19.53/2.99      | ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
% 19.53/2.99      inference(cnf_transformation,[],[f52]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_359,plain,
% 19.53/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.53/2.99      | r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1166,plain,
% 19.53/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.53/2.99      | r2_hidden(X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_1158,c_359]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1600,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(sK2,k10_relat_1(sK2,X2))
% 19.53/2.99      | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),X2) = iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),X1) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_362,c_1166]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_5,plain,
% 19.53/2.99      ( r2_hidden(X0,X1)
% 19.53/2.99      | ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
% 19.53/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_358,plain,
% 19.53/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.53/2.99      | r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) != iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2117,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X3))
% 19.53/2.99      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_relat_1(sK2,k10_relat_1(sK2,X3))),X3) = iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_relat_1(sK2,k10_relat_1(sK2,X3))),X1) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_1600,c_358]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1594,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = X3
% 19.53/2.99      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3),X3) = iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3),X1) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_362,c_358]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1167,plain,
% 19.53/2.99      ( r2_hidden(X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top
% 19.53/2.99      | r2_hidden(X0,k2_relat_1(sK2)) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_1158,c_358]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1599,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(sK2,k10_relat_1(sK2,X2))
% 19.53/2.99      | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),X1) = iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),k2_relat_1(sK2)) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_362,c_1167]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_3328,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X3))
% 19.53/2.99      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_relat_1(sK2,k10_relat_1(sK2,X3))),X2) = iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_relat_1(sK2,k10_relat_1(sK2,X3))),k2_relat_1(sK2)) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_1599,c_359]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_3,plain,
% 19.53/2.99      ( ~ r2_hidden(X0,X1)
% 19.53/2.99      | ~ r2_hidden(X0,X2)
% 19.53/2.99      | r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
% 19.53/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_360,plain,
% 19.53/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.53/2.99      | r2_hidden(X0,X2) != iProver_top
% 19.53/2.99      | r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1165,plain,
% 19.53/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.53/2.99      | r2_hidden(X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))) = iProver_top
% 19.53/2.99      | r2_hidden(X0,k2_relat_1(sK2)) != iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_1158,c_360]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2,plain,
% 19.53/2.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.53/2.99      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
% 19.53/2.99      inference(cnf_transformation,[],[f44]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_361,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1466,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_relat_1(sK2,k10_relat_1(sK2,X2))
% 19.53/2.99      | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),X0) = iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))),k2_relat_1(sK2)) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_361,c_1167]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2430,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))),k2_relat_1(sK2)) = iProver_top
% 19.53/2.99      | iProver_top != iProver_top ),
% 19.53/2.99      inference(equality_factoring,[status(thm)],[c_1466]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2432,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))),k2_relat_1(sK2)) = iProver_top ),
% 19.53/2.99      inference(equality_resolution_simp,[status(thm)],[c_2430]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2435,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),k2_relat_1(sK2)) = iProver_top ),
% 19.53/2.99      inference(demodulation,[status(thm)],[c_2432,c_1158]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_0,plain,
% 19.53/2.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 19.53/2.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 19.53/2.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 19.53/2.99      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
% 19.53/2.99      inference(cnf_transformation,[],[f42]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_363,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2626,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X0,k9_relat_1(sK2,k10_relat_1(sK2,X1))),k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_2435,c_363]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2631,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X1) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),k9_relat_1(sK2,k10_relat_1(sK2,X0))) != iProver_top ),
% 19.53/2.99      inference(demodulation,[status(thm)],[c_2626,c_1158]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2651,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X1) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),k2_relat_1(sK2)) != iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_1165,c_2631]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2889,plain,
% 19.53/2.99      ( r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X1) != iProver_top
% 19.53/2.99      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1)) ),
% 19.53/2.99      inference(global_propositional_subsumption,[status(thm)],[c_2651,c_2435]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2890,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X1) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),X1,k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top ),
% 19.53/2.99      inference(renaming,[status(thm)],[c_2889]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_2902,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k9_relat_1(sK2,k10_relat_1(sK2,X2))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k9_relat_1(sK2,k10_relat_1(sK2,X2))),X1) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k9_relat_1(sK2,k10_relat_1(sK2,X2))),X0) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k9_relat_1(sK2,k10_relat_1(sK2,X2))),X2) != iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_360,c_2890]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_61705,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X1) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),k2_relat_1(sK2)) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_3328,c_2902]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_61932,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X1) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top ),
% 19.53/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_61705,c_2902]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1601,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top
% 19.53/2.99      | iProver_top != iProver_top ),
% 19.53/2.99      inference(equality_factoring,[status(thm)],[c_362]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1603,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
% 19.53/2.99      | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top ),
% 19.53/2.99      inference(equality_resolution_simp,[status(thm)],[c_1601]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_9617,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
% 19.53/2.99      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_1603,c_359]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_9680,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))
% 19.53/2.99      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) != iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_9617,c_363]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_9881,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 19.53/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_9680,c_1603]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_9930,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_9881,c_1158]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_61933,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X1) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top ),
% 19.53/2.99      inference(demodulation,[status(thm)],[c_61932,c_1158,c_9930]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_63597,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 19.53/2.99      | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),k9_relat_1(sK2,k10_relat_1(sK2,X0))) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_1594,c_61933]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_1162,plain,
% 19.53/2.99      ( k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))) = k10_relat_1(sK2,X0) ),
% 19.53/2.99      inference(demodulation,[status(thm)],[c_1158,c_881]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_63618,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_relat_1(sK2)))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X1,X1,X1,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),k9_relat_1(sK2,k10_relat_1(sK2,X0))) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X1,X1,X1,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))))),X1) != iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_1162,c_61933]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_63622,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),X0) != iProver_top
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X1))),k9_relat_1(sK2,k10_relat_1(sK2,X1))) != iProver_top ),
% 19.53/2.99      inference(light_normalisation,[status(thm)],[c_63618,c_1162]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_63672,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 19.53/2.99      | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top ),
% 19.53/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_63597,c_63622]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_63673,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) != iProver_top ),
% 19.53/2.99      inference(demodulation,[status(thm)],[c_63672,c_1158,c_9930]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_63730,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 19.53/2.99      | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 19.53/2.99      | r2_hidden(sK0(k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))),k9_relat_1(sK2,k10_relat_1(sK2,X0))),X0) = iProver_top ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_2117,c_63673]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_63760,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0))
% 19.53/2.99      | k1_setfam_1(k2_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 19.53/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_63730,c_63673]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_63761,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 19.53/2.99      inference(demodulation,[status(thm)],[c_63760,c_1158,c_9930]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_7,plain,
% 19.53/2.99      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 19.53/2.99      inference(cnf_transformation,[],[f34]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_356,plain,
% 19.53/2.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 19.53/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.53/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_585,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 19.53/2.99      inference(superposition,[status(thm)],[c_352,c_356]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_10,negated_conjecture,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,k1_relat_1(sK2)))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
% 19.53/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_587,plain,
% 19.53/2.99      ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k2_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
% 19.53/2.99      inference(demodulation,[status(thm)],[c_585,c_10]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_63999,plain,
% 19.53/2.99      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
% 19.53/2.99      inference(demodulation,[status(thm)],[c_63761,c_587]) ).
% 19.53/2.99  
% 19.53/2.99  cnf(c_64005,plain,
% 19.53/2.99      ( $false ),
% 19.53/2.99      inference(equality_resolution_simp,[status(thm)],[c_63999]) ).
% 19.53/2.99  
% 19.53/2.99  
% 19.53/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.53/2.99  
% 19.53/2.99  ------                               Statistics
% 19.53/2.99  
% 19.53/2.99  ------ Selected
% 19.53/2.99  
% 19.53/2.99  total_time:                             2.313
% 19.53/2.99  
%------------------------------------------------------------------------------
