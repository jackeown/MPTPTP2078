%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:25 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 255 expanded)
%              Number of clauses        :   39 (  49 expanded)
%              Number of leaves         :   12 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  260 ( 744 expanded)
%              Number of equality atoms :   66 ( 200 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f42])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f42])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f42])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,sK2)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(sK2)))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f23,f22])).

fof(f40,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK2)))) ),
    inference(definition_unfolding,[],[f40,f42,f42])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f36,f42])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_358,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_903,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
    | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_358])).

cnf(c_905,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
    | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_903])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_355,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3138,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_355])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_359,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3158,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))
    | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3138,c_359])).

cnf(c_3350,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3158,c_905])).

cnf(c_6,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_353,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3370,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3350,c_353])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_350,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_352,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK2)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_349,plain,
    ( r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_698,plain,
    ( r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK2)) != iProver_top
    | r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_352,c_349])).

cnf(c_1119,plain,
    ( r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_350,c_698])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_711,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK2))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_10,c_7])).

cnf(c_719,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_711,c_9])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_959,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_11])).

cnf(c_960,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) ),
    inference(renaming,[status(thm)],[c_959])).

cnf(c_1129,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_960,c_9])).

cnf(c_1132,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK1)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1129,c_12])).

cnf(c_1133,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) ),
    inference(renaming,[status(thm)],[c_1132])).

cnf(c_1139,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1133,c_6])).

cnf(c_1140,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1208,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1209,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_1979,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1119,c_13,c_1140,c_1209])).

cnf(c_3696,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3370,c_1979])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:45:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.40/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.04  
% 3.40/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/1.04  
% 3.40/1.04  ------  iProver source info
% 3.40/1.04  
% 3.40/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.40/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/1.04  git: non_committed_changes: false
% 3.40/1.04  git: last_make_outside_of_git: false
% 3.40/1.04  
% 3.40/1.04  ------ 
% 3.40/1.04  
% 3.40/1.04  ------ Input Options
% 3.40/1.04  
% 3.40/1.04  --out_options                           all
% 3.40/1.04  --tptp_safe_out                         true
% 3.40/1.04  --problem_path                          ""
% 3.40/1.04  --include_path                          ""
% 3.40/1.04  --clausifier                            res/vclausify_rel
% 3.40/1.04  --clausifier_options                    --mode clausify
% 3.40/1.04  --stdin                                 false
% 3.40/1.04  --stats_out                             sel
% 3.40/1.04  
% 3.40/1.04  ------ General Options
% 3.40/1.04  
% 3.40/1.04  --fof                                   false
% 3.40/1.04  --time_out_real                         604.96
% 3.40/1.04  --time_out_virtual                      -1.
% 3.40/1.04  --symbol_type_check                     false
% 3.40/1.04  --clausify_out                          false
% 3.40/1.04  --sig_cnt_out                           false
% 3.40/1.04  --trig_cnt_out                          false
% 3.40/1.04  --trig_cnt_out_tolerance                1.
% 3.40/1.04  --trig_cnt_out_sk_spl                   false
% 3.40/1.04  --abstr_cl_out                          false
% 3.40/1.04  
% 3.40/1.04  ------ Global Options
% 3.40/1.04  
% 3.40/1.04  --schedule                              none
% 3.40/1.04  --add_important_lit                     false
% 3.40/1.04  --prop_solver_per_cl                    1000
% 3.40/1.04  --min_unsat_core                        false
% 3.40/1.04  --soft_assumptions                      false
% 3.40/1.04  --soft_lemma_size                       3
% 3.40/1.04  --prop_impl_unit_size                   0
% 3.40/1.04  --prop_impl_unit                        []
% 3.40/1.04  --share_sel_clauses                     true
% 3.40/1.04  --reset_solvers                         false
% 3.40/1.04  --bc_imp_inh                            [conj_cone]
% 3.40/1.04  --conj_cone_tolerance                   3.
% 3.40/1.04  --extra_neg_conj                        none
% 3.40/1.04  --large_theory_mode                     true
% 3.40/1.04  --prolific_symb_bound                   200
% 3.40/1.04  --lt_threshold                          2000
% 3.40/1.04  --clause_weak_htbl                      true
% 3.40/1.04  --gc_record_bc_elim                     false
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing Options
% 3.40/1.04  
% 3.40/1.04  --preprocessing_flag                    true
% 3.40/1.04  --time_out_prep_mult                    0.1
% 3.40/1.04  --splitting_mode                        input
% 3.40/1.04  --splitting_grd                         true
% 3.40/1.04  --splitting_cvd                         false
% 3.40/1.04  --splitting_cvd_svl                     false
% 3.40/1.04  --splitting_nvd                         32
% 3.40/1.04  --sub_typing                            true
% 3.40/1.04  --prep_gs_sim                           false
% 3.40/1.04  --prep_unflatten                        true
% 3.40/1.04  --prep_res_sim                          true
% 3.40/1.04  --prep_upred                            true
% 3.40/1.04  --prep_sem_filter                       exhaustive
% 3.40/1.04  --prep_sem_filter_out                   false
% 3.40/1.04  --pred_elim                             false
% 3.40/1.04  --res_sim_input                         true
% 3.40/1.04  --eq_ax_congr_red                       true
% 3.40/1.04  --pure_diseq_elim                       true
% 3.40/1.04  --brand_transform                       false
% 3.40/1.04  --non_eq_to_eq                          false
% 3.40/1.04  --prep_def_merge                        true
% 3.40/1.04  --prep_def_merge_prop_impl              false
% 3.40/1.04  --prep_def_merge_mbd                    true
% 3.40/1.04  --prep_def_merge_tr_red                 false
% 3.40/1.04  --prep_def_merge_tr_cl                  false
% 3.40/1.04  --smt_preprocessing                     true
% 3.40/1.04  --smt_ac_axioms                         fast
% 3.40/1.04  --preprocessed_out                      false
% 3.40/1.04  --preprocessed_stats                    false
% 3.40/1.04  
% 3.40/1.04  ------ Abstraction refinement Options
% 3.40/1.04  
% 3.40/1.04  --abstr_ref                             []
% 3.40/1.04  --abstr_ref_prep                        false
% 3.40/1.04  --abstr_ref_until_sat                   false
% 3.40/1.04  --abstr_ref_sig_restrict                funpre
% 3.40/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.04  --abstr_ref_under                       []
% 3.40/1.04  
% 3.40/1.04  ------ SAT Options
% 3.40/1.04  
% 3.40/1.04  --sat_mode                              false
% 3.40/1.04  --sat_fm_restart_options                ""
% 3.40/1.04  --sat_gr_def                            false
% 3.40/1.04  --sat_epr_types                         true
% 3.40/1.04  --sat_non_cyclic_types                  false
% 3.40/1.04  --sat_finite_models                     false
% 3.40/1.04  --sat_fm_lemmas                         false
% 3.40/1.04  --sat_fm_prep                           false
% 3.40/1.04  --sat_fm_uc_incr                        true
% 3.40/1.04  --sat_out_model                         small
% 3.40/1.04  --sat_out_clauses                       false
% 3.40/1.04  
% 3.40/1.04  ------ QBF Options
% 3.40/1.04  
% 3.40/1.04  --qbf_mode                              false
% 3.40/1.04  --qbf_elim_univ                         false
% 3.40/1.04  --qbf_dom_inst                          none
% 3.40/1.04  --qbf_dom_pre_inst                      false
% 3.40/1.04  --qbf_sk_in                             false
% 3.40/1.04  --qbf_pred_elim                         true
% 3.40/1.04  --qbf_split                             512
% 3.40/1.04  
% 3.40/1.04  ------ BMC1 Options
% 3.40/1.04  
% 3.40/1.04  --bmc1_incremental                      false
% 3.40/1.04  --bmc1_axioms                           reachable_all
% 3.40/1.04  --bmc1_min_bound                        0
% 3.40/1.04  --bmc1_max_bound                        -1
% 3.40/1.04  --bmc1_max_bound_default                -1
% 3.40/1.04  --bmc1_symbol_reachability              true
% 3.40/1.04  --bmc1_property_lemmas                  false
% 3.40/1.04  --bmc1_k_induction                      false
% 3.40/1.04  --bmc1_non_equiv_states                 false
% 3.40/1.04  --bmc1_deadlock                         false
% 3.40/1.04  --bmc1_ucm                              false
% 3.40/1.04  --bmc1_add_unsat_core                   none
% 3.40/1.04  --bmc1_unsat_core_children              false
% 3.40/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.04  --bmc1_out_stat                         full
% 3.40/1.04  --bmc1_ground_init                      false
% 3.40/1.04  --bmc1_pre_inst_next_state              false
% 3.40/1.04  --bmc1_pre_inst_state                   false
% 3.40/1.04  --bmc1_pre_inst_reach_state             false
% 3.40/1.04  --bmc1_out_unsat_core                   false
% 3.40/1.04  --bmc1_aig_witness_out                  false
% 3.40/1.04  --bmc1_verbose                          false
% 3.40/1.04  --bmc1_dump_clauses_tptp                false
% 3.40/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.04  --bmc1_dump_file                        -
% 3.40/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.04  --bmc1_ucm_extend_mode                  1
% 3.40/1.04  --bmc1_ucm_init_mode                    2
% 3.40/1.04  --bmc1_ucm_cone_mode                    none
% 3.40/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.04  --bmc1_ucm_relax_model                  4
% 3.40/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.04  --bmc1_ucm_layered_model                none
% 3.40/1.04  --bmc1_ucm_max_lemma_size               10
% 3.40/1.04  
% 3.40/1.04  ------ AIG Options
% 3.40/1.04  
% 3.40/1.04  --aig_mode                              false
% 3.40/1.04  
% 3.40/1.04  ------ Instantiation Options
% 3.40/1.04  
% 3.40/1.04  --instantiation_flag                    true
% 3.40/1.04  --inst_sos_flag                         false
% 3.40/1.04  --inst_sos_phase                        true
% 3.40/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.04  --inst_lit_sel_side                     num_symb
% 3.40/1.04  --inst_solver_per_active                1400
% 3.40/1.04  --inst_solver_calls_frac                1.
% 3.40/1.04  --inst_passive_queue_type               priority_queues
% 3.40/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.04  --inst_passive_queues_freq              [25;2]
% 3.40/1.04  --inst_dismatching                      true
% 3.40/1.04  --inst_eager_unprocessed_to_passive     true
% 3.40/1.04  --inst_prop_sim_given                   true
% 3.40/1.04  --inst_prop_sim_new                     false
% 3.40/1.04  --inst_subs_new                         false
% 3.40/1.04  --inst_eq_res_simp                      false
% 3.40/1.04  --inst_subs_given                       false
% 3.40/1.04  --inst_orphan_elimination               true
% 3.40/1.04  --inst_learning_loop_flag               true
% 3.40/1.04  --inst_learning_start                   3000
% 3.40/1.04  --inst_learning_factor                  2
% 3.40/1.04  --inst_start_prop_sim_after_learn       3
% 3.40/1.04  --inst_sel_renew                        solver
% 3.40/1.04  --inst_lit_activity_flag                true
% 3.40/1.04  --inst_restr_to_given                   false
% 3.40/1.04  --inst_activity_threshold               500
% 3.40/1.04  --inst_out_proof                        true
% 3.40/1.04  
% 3.40/1.04  ------ Resolution Options
% 3.40/1.04  
% 3.40/1.04  --resolution_flag                       true
% 3.40/1.04  --res_lit_sel                           adaptive
% 3.40/1.04  --res_lit_sel_side                      none
% 3.40/1.04  --res_ordering                          kbo
% 3.40/1.04  --res_to_prop_solver                    active
% 3.40/1.04  --res_prop_simpl_new                    false
% 3.40/1.04  --res_prop_simpl_given                  true
% 3.40/1.04  --res_passive_queue_type                priority_queues
% 3.40/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.04  --res_passive_queues_freq               [15;5]
% 3.40/1.04  --res_forward_subs                      full
% 3.40/1.04  --res_backward_subs                     full
% 3.40/1.04  --res_forward_subs_resolution           true
% 3.40/1.04  --res_backward_subs_resolution          true
% 3.40/1.04  --res_orphan_elimination                true
% 3.40/1.04  --res_time_limit                        2.
% 3.40/1.04  --res_out_proof                         true
% 3.40/1.04  
% 3.40/1.04  ------ Superposition Options
% 3.40/1.04  
% 3.40/1.04  --superposition_flag                    true
% 3.40/1.04  --sup_passive_queue_type                priority_queues
% 3.40/1.04  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.04  --sup_passive_queues_freq               [1;4]
% 3.40/1.04  --demod_completeness_check              fast
% 3.40/1.04  --demod_use_ground                      true
% 3.40/1.04  --sup_to_prop_solver                    passive
% 3.40/1.04  --sup_prop_simpl_new                    true
% 3.40/1.04  --sup_prop_simpl_given                  true
% 3.40/1.04  --sup_fun_splitting                     false
% 3.40/1.04  --sup_smt_interval                      50000
% 3.40/1.04  
% 3.40/1.04  ------ Superposition Simplification Setup
% 3.40/1.04  
% 3.40/1.04  --sup_indices_passive                   []
% 3.40/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_full_bw                           [BwDemod]
% 3.40/1.04  --sup_immed_triv                        [TrivRules]
% 3.40/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_immed_bw_main                     []
% 3.40/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.04  
% 3.40/1.04  ------ Combination Options
% 3.40/1.04  
% 3.40/1.04  --comb_res_mult                         3
% 3.40/1.04  --comb_sup_mult                         2
% 3.40/1.04  --comb_inst_mult                        10
% 3.40/1.04  
% 3.40/1.04  ------ Debug Options
% 3.40/1.04  
% 3.40/1.04  --dbg_backtrace                         false
% 3.40/1.04  --dbg_dump_prop_clauses                 false
% 3.40/1.04  --dbg_dump_prop_clauses_file            -
% 3.40/1.04  --dbg_out_stat                          false
% 3.40/1.04  ------ Parsing...
% 3.40/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/1.04  ------ Proving...
% 3.40/1.04  ------ Problem Properties 
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  clauses                                 13
% 3.40/1.04  conjectures                             3
% 3.40/1.04  EPR                                     2
% 3.40/1.04  Horn                                    11
% 3.40/1.04  unary                                   4
% 3.40/1.04  binary                                  3
% 3.40/1.04  lits                                    30
% 3.40/1.04  lits eq                                 3
% 3.40/1.04  fd_pure                                 0
% 3.40/1.04  fd_pseudo                               0
% 3.40/1.04  fd_cond                                 0
% 3.40/1.04  fd_pseudo_cond                          3
% 3.40/1.04  AC symbols                              0
% 3.40/1.04  
% 3.40/1.04  ------ Input Options Time Limit: Unbounded
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  ------ 
% 3.40/1.04  Current options:
% 3.40/1.04  ------ 
% 3.40/1.04  
% 3.40/1.04  ------ Input Options
% 3.40/1.04  
% 3.40/1.04  --out_options                           all
% 3.40/1.04  --tptp_safe_out                         true
% 3.40/1.04  --problem_path                          ""
% 3.40/1.04  --include_path                          ""
% 3.40/1.04  --clausifier                            res/vclausify_rel
% 3.40/1.04  --clausifier_options                    --mode clausify
% 3.40/1.04  --stdin                                 false
% 3.40/1.04  --stats_out                             sel
% 3.40/1.04  
% 3.40/1.04  ------ General Options
% 3.40/1.04  
% 3.40/1.04  --fof                                   false
% 3.40/1.04  --time_out_real                         604.96
% 3.40/1.04  --time_out_virtual                      -1.
% 3.40/1.04  --symbol_type_check                     false
% 3.40/1.04  --clausify_out                          false
% 3.40/1.04  --sig_cnt_out                           false
% 3.40/1.04  --trig_cnt_out                          false
% 3.40/1.04  --trig_cnt_out_tolerance                1.
% 3.40/1.04  --trig_cnt_out_sk_spl                   false
% 3.40/1.04  --abstr_cl_out                          false
% 3.40/1.04  
% 3.40/1.04  ------ Global Options
% 3.40/1.04  
% 3.40/1.04  --schedule                              none
% 3.40/1.04  --add_important_lit                     false
% 3.40/1.04  --prop_solver_per_cl                    1000
% 3.40/1.04  --min_unsat_core                        false
% 3.40/1.04  --soft_assumptions                      false
% 3.40/1.04  --soft_lemma_size                       3
% 3.40/1.04  --prop_impl_unit_size                   0
% 3.40/1.04  --prop_impl_unit                        []
% 3.40/1.04  --share_sel_clauses                     true
% 3.40/1.04  --reset_solvers                         false
% 3.40/1.04  --bc_imp_inh                            [conj_cone]
% 3.40/1.04  --conj_cone_tolerance                   3.
% 3.40/1.04  --extra_neg_conj                        none
% 3.40/1.04  --large_theory_mode                     true
% 3.40/1.04  --prolific_symb_bound                   200
% 3.40/1.04  --lt_threshold                          2000
% 3.40/1.04  --clause_weak_htbl                      true
% 3.40/1.04  --gc_record_bc_elim                     false
% 3.40/1.04  
% 3.40/1.04  ------ Preprocessing Options
% 3.40/1.04  
% 3.40/1.04  --preprocessing_flag                    true
% 3.40/1.04  --time_out_prep_mult                    0.1
% 3.40/1.04  --splitting_mode                        input
% 3.40/1.04  --splitting_grd                         true
% 3.40/1.04  --splitting_cvd                         false
% 3.40/1.04  --splitting_cvd_svl                     false
% 3.40/1.04  --splitting_nvd                         32
% 3.40/1.04  --sub_typing                            true
% 3.40/1.04  --prep_gs_sim                           false
% 3.40/1.04  --prep_unflatten                        true
% 3.40/1.04  --prep_res_sim                          true
% 3.40/1.04  --prep_upred                            true
% 3.40/1.04  --prep_sem_filter                       exhaustive
% 3.40/1.04  --prep_sem_filter_out                   false
% 3.40/1.04  --pred_elim                             false
% 3.40/1.04  --res_sim_input                         true
% 3.40/1.04  --eq_ax_congr_red                       true
% 3.40/1.04  --pure_diseq_elim                       true
% 3.40/1.04  --brand_transform                       false
% 3.40/1.04  --non_eq_to_eq                          false
% 3.40/1.04  --prep_def_merge                        true
% 3.40/1.04  --prep_def_merge_prop_impl              false
% 3.40/1.04  --prep_def_merge_mbd                    true
% 3.40/1.04  --prep_def_merge_tr_red                 false
% 3.40/1.04  --prep_def_merge_tr_cl                  false
% 3.40/1.04  --smt_preprocessing                     true
% 3.40/1.04  --smt_ac_axioms                         fast
% 3.40/1.04  --preprocessed_out                      false
% 3.40/1.04  --preprocessed_stats                    false
% 3.40/1.04  
% 3.40/1.04  ------ Abstraction refinement Options
% 3.40/1.04  
% 3.40/1.04  --abstr_ref                             []
% 3.40/1.04  --abstr_ref_prep                        false
% 3.40/1.04  --abstr_ref_until_sat                   false
% 3.40/1.04  --abstr_ref_sig_restrict                funpre
% 3.40/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.04  --abstr_ref_under                       []
% 3.40/1.04  
% 3.40/1.04  ------ SAT Options
% 3.40/1.04  
% 3.40/1.04  --sat_mode                              false
% 3.40/1.04  --sat_fm_restart_options                ""
% 3.40/1.04  --sat_gr_def                            false
% 3.40/1.04  --sat_epr_types                         true
% 3.40/1.04  --sat_non_cyclic_types                  false
% 3.40/1.04  --sat_finite_models                     false
% 3.40/1.04  --sat_fm_lemmas                         false
% 3.40/1.04  --sat_fm_prep                           false
% 3.40/1.04  --sat_fm_uc_incr                        true
% 3.40/1.04  --sat_out_model                         small
% 3.40/1.04  --sat_out_clauses                       false
% 3.40/1.04  
% 3.40/1.04  ------ QBF Options
% 3.40/1.04  
% 3.40/1.04  --qbf_mode                              false
% 3.40/1.04  --qbf_elim_univ                         false
% 3.40/1.04  --qbf_dom_inst                          none
% 3.40/1.04  --qbf_dom_pre_inst                      false
% 3.40/1.04  --qbf_sk_in                             false
% 3.40/1.04  --qbf_pred_elim                         true
% 3.40/1.04  --qbf_split                             512
% 3.40/1.04  
% 3.40/1.04  ------ BMC1 Options
% 3.40/1.04  
% 3.40/1.04  --bmc1_incremental                      false
% 3.40/1.04  --bmc1_axioms                           reachable_all
% 3.40/1.04  --bmc1_min_bound                        0
% 3.40/1.04  --bmc1_max_bound                        -1
% 3.40/1.04  --bmc1_max_bound_default                -1
% 3.40/1.04  --bmc1_symbol_reachability              true
% 3.40/1.04  --bmc1_property_lemmas                  false
% 3.40/1.04  --bmc1_k_induction                      false
% 3.40/1.04  --bmc1_non_equiv_states                 false
% 3.40/1.04  --bmc1_deadlock                         false
% 3.40/1.04  --bmc1_ucm                              false
% 3.40/1.04  --bmc1_add_unsat_core                   none
% 3.40/1.04  --bmc1_unsat_core_children              false
% 3.40/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.04  --bmc1_out_stat                         full
% 3.40/1.04  --bmc1_ground_init                      false
% 3.40/1.04  --bmc1_pre_inst_next_state              false
% 3.40/1.04  --bmc1_pre_inst_state                   false
% 3.40/1.04  --bmc1_pre_inst_reach_state             false
% 3.40/1.04  --bmc1_out_unsat_core                   false
% 3.40/1.04  --bmc1_aig_witness_out                  false
% 3.40/1.04  --bmc1_verbose                          false
% 3.40/1.04  --bmc1_dump_clauses_tptp                false
% 3.40/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.04  --bmc1_dump_file                        -
% 3.40/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.04  --bmc1_ucm_extend_mode                  1
% 3.40/1.04  --bmc1_ucm_init_mode                    2
% 3.40/1.04  --bmc1_ucm_cone_mode                    none
% 3.40/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.04  --bmc1_ucm_relax_model                  4
% 3.40/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.04  --bmc1_ucm_layered_model                none
% 3.40/1.04  --bmc1_ucm_max_lemma_size               10
% 3.40/1.04  
% 3.40/1.04  ------ AIG Options
% 3.40/1.04  
% 3.40/1.04  --aig_mode                              false
% 3.40/1.04  
% 3.40/1.04  ------ Instantiation Options
% 3.40/1.04  
% 3.40/1.04  --instantiation_flag                    true
% 3.40/1.04  --inst_sos_flag                         false
% 3.40/1.04  --inst_sos_phase                        true
% 3.40/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.04  --inst_lit_sel_side                     num_symb
% 3.40/1.04  --inst_solver_per_active                1400
% 3.40/1.04  --inst_solver_calls_frac                1.
% 3.40/1.04  --inst_passive_queue_type               priority_queues
% 3.40/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.04  --inst_passive_queues_freq              [25;2]
% 3.40/1.04  --inst_dismatching                      true
% 3.40/1.04  --inst_eager_unprocessed_to_passive     true
% 3.40/1.04  --inst_prop_sim_given                   true
% 3.40/1.04  --inst_prop_sim_new                     false
% 3.40/1.04  --inst_subs_new                         false
% 3.40/1.04  --inst_eq_res_simp                      false
% 3.40/1.04  --inst_subs_given                       false
% 3.40/1.04  --inst_orphan_elimination               true
% 3.40/1.04  --inst_learning_loop_flag               true
% 3.40/1.04  --inst_learning_start                   3000
% 3.40/1.04  --inst_learning_factor                  2
% 3.40/1.04  --inst_start_prop_sim_after_learn       3
% 3.40/1.04  --inst_sel_renew                        solver
% 3.40/1.04  --inst_lit_activity_flag                true
% 3.40/1.04  --inst_restr_to_given                   false
% 3.40/1.04  --inst_activity_threshold               500
% 3.40/1.04  --inst_out_proof                        true
% 3.40/1.04  
% 3.40/1.04  ------ Resolution Options
% 3.40/1.04  
% 3.40/1.04  --resolution_flag                       true
% 3.40/1.04  --res_lit_sel                           adaptive
% 3.40/1.04  --res_lit_sel_side                      none
% 3.40/1.04  --res_ordering                          kbo
% 3.40/1.04  --res_to_prop_solver                    active
% 3.40/1.04  --res_prop_simpl_new                    false
% 3.40/1.04  --res_prop_simpl_given                  true
% 3.40/1.04  --res_passive_queue_type                priority_queues
% 3.40/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.04  --res_passive_queues_freq               [15;5]
% 3.40/1.04  --res_forward_subs                      full
% 3.40/1.04  --res_backward_subs                     full
% 3.40/1.04  --res_forward_subs_resolution           true
% 3.40/1.04  --res_backward_subs_resolution          true
% 3.40/1.04  --res_orphan_elimination                true
% 3.40/1.04  --res_time_limit                        2.
% 3.40/1.04  --res_out_proof                         true
% 3.40/1.04  
% 3.40/1.04  ------ Superposition Options
% 3.40/1.04  
% 3.40/1.04  --superposition_flag                    true
% 3.40/1.04  --sup_passive_queue_type                priority_queues
% 3.40/1.04  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.04  --sup_passive_queues_freq               [1;4]
% 3.40/1.04  --demod_completeness_check              fast
% 3.40/1.04  --demod_use_ground                      true
% 3.40/1.04  --sup_to_prop_solver                    passive
% 3.40/1.04  --sup_prop_simpl_new                    true
% 3.40/1.04  --sup_prop_simpl_given                  true
% 3.40/1.04  --sup_fun_splitting                     false
% 3.40/1.04  --sup_smt_interval                      50000
% 3.40/1.04  
% 3.40/1.04  ------ Superposition Simplification Setup
% 3.40/1.04  
% 3.40/1.04  --sup_indices_passive                   []
% 3.40/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_full_bw                           [BwDemod]
% 3.40/1.04  --sup_immed_triv                        [TrivRules]
% 3.40/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_immed_bw_main                     []
% 3.40/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.04  
% 3.40/1.04  ------ Combination Options
% 3.40/1.04  
% 3.40/1.04  --comb_res_mult                         3
% 3.40/1.04  --comb_sup_mult                         2
% 3.40/1.04  --comb_inst_mult                        10
% 3.40/1.04  
% 3.40/1.04  ------ Debug Options
% 3.40/1.04  
% 3.40/1.04  --dbg_backtrace                         false
% 3.40/1.04  --dbg_dump_prop_clauses                 false
% 3.40/1.04  --dbg_dump_prop_clauses_file            -
% 3.40/1.04  --dbg_out_stat                          false
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  ------ Proving...
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  % SZS status Theorem for theBenchmark.p
% 3.40/1.04  
% 3.40/1.04   Resolution empty clause
% 3.40/1.04  
% 3.40/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/1.04  
% 3.40/1.04  fof(f1,axiom,(
% 3.40/1.04    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f17,plain,(
% 3.40/1.04    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.40/1.04    inference(nnf_transformation,[],[f1])).
% 3.40/1.04  
% 3.40/1.04  fof(f18,plain,(
% 3.40/1.04    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.40/1.04    inference(flattening,[],[f17])).
% 3.40/1.04  
% 3.40/1.04  fof(f19,plain,(
% 3.40/1.04    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.40/1.04    inference(rectify,[],[f18])).
% 3.40/1.04  
% 3.40/1.04  fof(f20,plain,(
% 3.40/1.04    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f21,plain,(
% 3.40/1.04    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.40/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.40/1.04  
% 3.40/1.04  fof(f29,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f21])).
% 3.40/1.04  
% 3.40/1.04  fof(f6,axiom,(
% 3.40/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f35,plain,(
% 3.40/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.40/1.04    inference(cnf_transformation,[],[f6])).
% 3.40/1.04  
% 3.40/1.04  fof(f4,axiom,(
% 3.40/1.04    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f33,plain,(
% 3.40/1.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f4])).
% 3.40/1.04  
% 3.40/1.04  fof(f5,axiom,(
% 3.40/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f34,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f5])).
% 3.40/1.04  
% 3.40/1.04  fof(f41,plain,(
% 3.40/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.40/1.04    inference(definition_unfolding,[],[f33,f34])).
% 3.40/1.04  
% 3.40/1.04  fof(f42,plain,(
% 3.40/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.40/1.04    inference(definition_unfolding,[],[f35,f41])).
% 3.40/1.04  
% 3.40/1.04  fof(f44,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.40/1.04    inference(definition_unfolding,[],[f29,f42])).
% 3.40/1.04  
% 3.40/1.04  fof(f26,plain,(
% 3.40/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.40/1.04    inference(cnf_transformation,[],[f21])).
% 3.40/1.04  
% 3.40/1.04  fof(f47,plain,(
% 3.40/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 3.40/1.04    inference(definition_unfolding,[],[f26,f42])).
% 3.40/1.04  
% 3.40/1.04  fof(f54,plain,(
% 3.40/1.04    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.40/1.04    inference(equality_resolution,[],[f47])).
% 3.40/1.04  
% 3.40/1.04  fof(f30,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f21])).
% 3.40/1.04  
% 3.40/1.04  fof(f43,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.40/1.04    inference(definition_unfolding,[],[f30,f42])).
% 3.40/1.04  
% 3.40/1.04  fof(f2,axiom,(
% 3.40/1.04    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f31,plain,(
% 3.40/1.04    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f2])).
% 3.40/1.04  
% 3.40/1.04  fof(f49,plain,(
% 3.40/1.04    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 3.40/1.04    inference(definition_unfolding,[],[f31,f42])).
% 3.40/1.04  
% 3.40/1.04  fof(f8,axiom,(
% 3.40/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f14,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.40/1.04    inference(ennf_transformation,[],[f8])).
% 3.40/1.04  
% 3.40/1.04  fof(f15,plain,(
% 3.40/1.04    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.40/1.04    inference(flattening,[],[f14])).
% 3.40/1.04  
% 3.40/1.04  fof(f37,plain,(
% 3.40/1.04    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f15])).
% 3.40/1.04  
% 3.40/1.04  fof(f3,axiom,(
% 3.40/1.04    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f11,plain,(
% 3.40/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.40/1.04    inference(ennf_transformation,[],[f3])).
% 3.40/1.04  
% 3.40/1.04  fof(f12,plain,(
% 3.40/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.40/1.04    inference(flattening,[],[f11])).
% 3.40/1.04  
% 3.40/1.04  fof(f32,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f12])).
% 3.40/1.04  
% 3.40/1.04  fof(f50,plain,(
% 3.40/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.40/1.04    inference(definition_unfolding,[],[f32,f42])).
% 3.40/1.04  
% 3.40/1.04  fof(f9,conjecture,(
% 3.40/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f10,negated_conjecture,(
% 3.40/1.04    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.40/1.04    inference(negated_conjecture,[],[f9])).
% 3.40/1.04  
% 3.40/1.04  fof(f16,plain,(
% 3.40/1.04    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.40/1.04    inference(ennf_transformation,[],[f10])).
% 3.40/1.04  
% 3.40/1.04  fof(f23,plain,(
% 3.40/1.04    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(X0,sK2)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(sK2))) & v1_relat_1(sK2))) )),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f22,plain,(
% 3.40/1.04    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 3.40/1.04    introduced(choice_axiom,[])).
% 3.40/1.04  
% 3.40/1.04  fof(f24,plain,(
% 3.40/1.04    (~r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 3.40/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f23,f22])).
% 3.40/1.04  
% 3.40/1.04  fof(f40,plain,(
% 3.40/1.04    ~r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))),
% 3.40/1.04    inference(cnf_transformation,[],[f24])).
% 3.40/1.04  
% 3.40/1.04  fof(f52,plain,(
% 3.40/1.04    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK2))))),
% 3.40/1.04    inference(definition_unfolding,[],[f40,f42,f42])).
% 3.40/1.04  
% 3.40/1.04  fof(f38,plain,(
% 3.40/1.04    v1_relat_1(sK1)),
% 3.40/1.04    inference(cnf_transformation,[],[f24])).
% 3.40/1.04  
% 3.40/1.04  fof(f39,plain,(
% 3.40/1.04    v1_relat_1(sK2)),
% 3.40/1.04    inference(cnf_transformation,[],[f24])).
% 3.40/1.04  
% 3.40/1.04  fof(f7,axiom,(
% 3.40/1.04    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 3.40/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.04  
% 3.40/1.04  fof(f13,plain,(
% 3.40/1.04    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.40/1.04    inference(ennf_transformation,[],[f7])).
% 3.40/1.04  
% 3.40/1.04  fof(f36,plain,(
% 3.40/1.04    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.40/1.04    inference(cnf_transformation,[],[f13])).
% 3.40/1.04  
% 3.40/1.04  fof(f51,plain,(
% 3.40/1.04    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 3.40/1.04    inference(definition_unfolding,[],[f36,f42])).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1,plain,
% 3.40/1.04      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.40/1.04      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.40/1.04      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
% 3.40/1.04      inference(cnf_transformation,[],[f44]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_358,plain,
% 3.40/1.04      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
% 3.40/1.04      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.40/1.04      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_903,plain,
% 3.40/1.04      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
% 3.40/1.04      | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top
% 3.40/1.04      | iProver_top != iProver_top ),
% 3.40/1.04      inference(equality_factoring,[status(thm)],[c_358]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_905,plain,
% 3.40/1.04      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1
% 3.40/1.04      | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top ),
% 3.40/1.04      inference(equality_resolution_simp,[status(thm)],[c_903]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_4,plain,
% 3.40/1.04      ( r2_hidden(X0,X1)
% 3.40/1.04      | ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
% 3.40/1.04      inference(cnf_transformation,[],[f54]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_355,plain,
% 3.40/1.04      ( r2_hidden(X0,X1) = iProver_top
% 3.40/1.04      | r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_3138,plain,
% 3.40/1.04      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
% 3.40/1.04      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2) = iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_905,c_355]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_0,plain,
% 3.40/1.04      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.40/1.04      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.40/1.04      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.40/1.04      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ),
% 3.40/1.04      inference(cnf_transformation,[],[f43]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_359,plain,
% 3.40/1.04      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
% 3.40/1.04      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 3.40/1.04      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 3.40/1.04      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_3158,plain,
% 3.40/1.04      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))
% 3.40/1.04      | r2_hidden(sK0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_3138,c_359]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_3350,plain,
% 3.40/1.04      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 3.40/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_3158,c_905]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_6,plain,
% 3.40/1.04      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 3.40/1.04      inference(cnf_transformation,[],[f49]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_353,plain,
% 3.40/1.04      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_3370,plain,
% 3.40/1.04      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_3350,c_353]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_9,plain,
% 3.40/1.04      ( ~ r1_tarski(X0,X1)
% 3.40/1.04      | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
% 3.40/1.04      | ~ v1_relat_1(X0)
% 3.40/1.04      | ~ v1_relat_1(X1) ),
% 3.40/1.04      inference(cnf_transformation,[],[f37]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_350,plain,
% 3.40/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.40/1.04      | r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) = iProver_top
% 3.40/1.04      | v1_relat_1(X0) != iProver_top
% 3.40/1.04      | v1_relat_1(X1) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_7,plain,
% 3.40/1.04      ( ~ r1_tarski(X0,X1)
% 3.40/1.04      | ~ r1_tarski(X0,X2)
% 3.40/1.04      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
% 3.40/1.04      inference(cnf_transformation,[],[f50]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_352,plain,
% 3.40/1.04      ( r1_tarski(X0,X1) != iProver_top
% 3.40/1.04      | r1_tarski(X0,X2) != iProver_top
% 3.40/1.04      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_10,negated_conjecture,
% 3.40/1.04      ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK2)))) ),
% 3.40/1.04      inference(cnf_transformation,[],[f52]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_349,plain,
% 3.40/1.04      ( r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK1),k3_relat_1(sK2)))) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_698,plain,
% 3.40/1.04      ( r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK2)) != iProver_top
% 3.40/1.04      | r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1)) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_352,c_349]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1119,plain,
% 3.40/1.04      ( r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1)) != iProver_top
% 3.40/1.04      | r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) != iProver_top
% 3.40/1.04      | v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) != iProver_top
% 3.40/1.04      | v1_relat_1(sK2) != iProver_top ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_350,c_698]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_12,negated_conjecture,
% 3.40/1.04      ( v1_relat_1(sK1) ),
% 3.40/1.04      inference(cnf_transformation,[],[f38]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_13,plain,
% 3.40/1.04      ( v1_relat_1(sK1) = iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_711,plain,
% 3.40/1.04      ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK2))
% 3.40/1.04      | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1)) ),
% 3.40/1.04      inference(resolution,[status(thm)],[c_10,c_7]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_719,plain,
% 3.40/1.04      ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1))
% 3.40/1.04      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
% 3.40/1.04      | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
% 3.40/1.04      | ~ v1_relat_1(sK2) ),
% 3.40/1.04      inference(resolution,[status(thm)],[c_711,c_9]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_11,negated_conjecture,
% 3.40/1.04      ( v1_relat_1(sK2) ),
% 3.40/1.04      inference(cnf_transformation,[],[f39]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_959,plain,
% 3.40/1.04      ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
% 3.40/1.04      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
% 3.40/1.04      | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1)) ),
% 3.40/1.04      inference(global_propositional_subsumption,[status(thm)],[c_719,c_11]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_960,plain,
% 3.40/1.04      ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k3_relat_1(sK1))
% 3.40/1.04      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
% 3.40/1.04      | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_959]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1129,plain,
% 3.40/1.04      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
% 3.40/1.04      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK1)
% 3.40/1.04      | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
% 3.40/1.04      | ~ v1_relat_1(sK1) ),
% 3.40/1.04      inference(resolution,[status(thm)],[c_960,c_9]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1132,plain,
% 3.40/1.04      ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
% 3.40/1.04      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK1)
% 3.40/1.04      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) ),
% 3.40/1.04      inference(global_propositional_subsumption,[status(thm)],[c_1129,c_12]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1133,plain,
% 3.40/1.04      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
% 3.40/1.04      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK1)
% 3.40/1.04      | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) ),
% 3.40/1.04      inference(renaming,[status(thm)],[c_1132]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1139,plain,
% 3.40/1.04      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2)
% 3.40/1.04      | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) ),
% 3.40/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_1133,c_6]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1140,plain,
% 3.40/1.04      ( r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) != iProver_top
% 3.40/1.04      | v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_8,plain,
% 3.40/1.04      ( ~ v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 3.40/1.04      inference(cnf_transformation,[],[f51]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1208,plain,
% 3.40/1.04      ( v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)))
% 3.40/1.04      | ~ v1_relat_1(sK1) ),
% 3.40/1.04      inference(instantiation,[status(thm)],[c_8]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1209,plain,
% 3.40/1.04      ( v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))) = iProver_top
% 3.40/1.04      | v1_relat_1(sK1) != iProver_top ),
% 3.40/1.04      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_1979,plain,
% 3.40/1.04      ( r1_tarski(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),sK2) != iProver_top ),
% 3.40/1.04      inference(global_propositional_subsumption,
% 3.40/1.04                [status(thm)],
% 3.40/1.04                [c_1119,c_13,c_1140,c_1209]) ).
% 3.40/1.04  
% 3.40/1.04  cnf(c_3696,plain,
% 3.40/1.04      ( $false ),
% 3.40/1.04      inference(superposition,[status(thm)],[c_3370,c_1979]) ).
% 3.40/1.04  
% 3.40/1.04  
% 3.40/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/1.04  
% 3.40/1.04  ------                               Statistics
% 3.40/1.04  
% 3.40/1.04  ------ Selected
% 3.40/1.04  
% 3.40/1.04  total_time:                             0.262
% 3.40/1.04  
%------------------------------------------------------------------------------
