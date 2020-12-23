%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:52 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 163 expanded)
%              Number of clauses        :   38 (  46 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  241 ( 456 expanded)
%              Number of equality atoms :   93 ( 173 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f31,f32,f32])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
      & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f23])).

fof(f39,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f43])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_7,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_418,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_411,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_414,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_667,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK3))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_411,c_414])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_816,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_17])).

cnf(c_819,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK3))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK3)) ),
    inference(superposition,[status(thm)],[c_6,c_816])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_413,plain,
    ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_609,plain,
    ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(sK2,sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6,c_413])).

cnf(c_1079,plain,
    ( r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_819,c_609])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_416,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1284,plain,
    ( k1_funct_1(sK3,k1_funct_1(k6_relat_1(sK2),sK1)) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k6_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_416])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_419,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_729,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_419])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_415,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_997,plain,
    ( k1_funct_1(k6_relat_1(sK2),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_729,c_415])).

cnf(c_1285,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1)
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k6_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1284,c_997])).

cnf(c_16,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,negated_conjecture,
    ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_164,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_442,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != X0
    | k1_funct_1(sK3,sK1) != X0
    | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_447,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
    | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
    | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_163,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_453,plain,
    ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_8,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2393,plain,
    ( v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2394,plain,
    ( v1_relat_1(k6_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2393])).

cnf(c_3731,plain,
    ( v1_funct_1(k6_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1285,c_16,c_17,c_12,c_447,c_453,c_2394])).

cnf(c_3735,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_418,c_3731])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:22:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.32/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.02  
% 3.32/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/1.02  
% 3.32/1.02  ------  iProver source info
% 3.32/1.02  
% 3.32/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.32/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/1.02  git: non_committed_changes: false
% 3.32/1.02  git: last_make_outside_of_git: false
% 3.32/1.02  
% 3.32/1.02  ------ 
% 3.32/1.02  
% 3.32/1.02  ------ Input Options
% 3.32/1.02  
% 3.32/1.02  --out_options                           all
% 3.32/1.02  --tptp_safe_out                         true
% 3.32/1.02  --problem_path                          ""
% 3.32/1.02  --include_path                          ""
% 3.32/1.02  --clausifier                            res/vclausify_rel
% 3.32/1.02  --clausifier_options                    ""
% 3.32/1.02  --stdin                                 false
% 3.32/1.02  --stats_out                             all
% 3.32/1.02  
% 3.32/1.02  ------ General Options
% 3.32/1.02  
% 3.32/1.02  --fof                                   false
% 3.32/1.02  --time_out_real                         305.
% 3.32/1.02  --time_out_virtual                      -1.
% 3.32/1.02  --symbol_type_check                     false
% 3.32/1.02  --clausify_out                          false
% 3.32/1.02  --sig_cnt_out                           false
% 3.32/1.02  --trig_cnt_out                          false
% 3.32/1.02  --trig_cnt_out_tolerance                1.
% 3.32/1.02  --trig_cnt_out_sk_spl                   false
% 3.32/1.02  --abstr_cl_out                          false
% 3.32/1.02  
% 3.32/1.02  ------ Global Options
% 3.32/1.02  
% 3.32/1.02  --schedule                              default
% 3.32/1.02  --add_important_lit                     false
% 3.32/1.02  --prop_solver_per_cl                    1000
% 3.32/1.02  --min_unsat_core                        false
% 3.32/1.02  --soft_assumptions                      false
% 3.32/1.02  --soft_lemma_size                       3
% 3.32/1.02  --prop_impl_unit_size                   0
% 3.32/1.02  --prop_impl_unit                        []
% 3.32/1.02  --share_sel_clauses                     true
% 3.32/1.02  --reset_solvers                         false
% 3.32/1.02  --bc_imp_inh                            [conj_cone]
% 3.32/1.02  --conj_cone_tolerance                   3.
% 3.32/1.02  --extra_neg_conj                        none
% 3.32/1.02  --large_theory_mode                     true
% 3.32/1.02  --prolific_symb_bound                   200
% 3.32/1.02  --lt_threshold                          2000
% 3.32/1.02  --clause_weak_htbl                      true
% 3.32/1.02  --gc_record_bc_elim                     false
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing Options
% 3.32/1.02  
% 3.32/1.02  --preprocessing_flag                    true
% 3.32/1.02  --time_out_prep_mult                    0.1
% 3.32/1.02  --splitting_mode                        input
% 3.32/1.02  --splitting_grd                         true
% 3.32/1.02  --splitting_cvd                         false
% 3.32/1.02  --splitting_cvd_svl                     false
% 3.32/1.02  --splitting_nvd                         32
% 3.32/1.02  --sub_typing                            true
% 3.32/1.02  --prep_gs_sim                           true
% 3.32/1.02  --prep_unflatten                        true
% 3.32/1.02  --prep_res_sim                          true
% 3.32/1.02  --prep_upred                            true
% 3.32/1.02  --prep_sem_filter                       exhaustive
% 3.32/1.02  --prep_sem_filter_out                   false
% 3.32/1.02  --pred_elim                             true
% 3.32/1.02  --res_sim_input                         true
% 3.32/1.02  --eq_ax_congr_red                       true
% 3.32/1.02  --pure_diseq_elim                       true
% 3.32/1.02  --brand_transform                       false
% 3.32/1.02  --non_eq_to_eq                          false
% 3.32/1.02  --prep_def_merge                        true
% 3.32/1.02  --prep_def_merge_prop_impl              false
% 3.32/1.02  --prep_def_merge_mbd                    true
% 3.32/1.02  --prep_def_merge_tr_red                 false
% 3.32/1.02  --prep_def_merge_tr_cl                  false
% 3.32/1.02  --smt_preprocessing                     true
% 3.32/1.02  --smt_ac_axioms                         fast
% 3.32/1.02  --preprocessed_out                      false
% 3.32/1.02  --preprocessed_stats                    false
% 3.32/1.02  
% 3.32/1.02  ------ Abstraction refinement Options
% 3.32/1.02  
% 3.32/1.02  --abstr_ref                             []
% 3.32/1.02  --abstr_ref_prep                        false
% 3.32/1.02  --abstr_ref_until_sat                   false
% 3.32/1.02  --abstr_ref_sig_restrict                funpre
% 3.32/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/1.02  --abstr_ref_under                       []
% 3.32/1.02  
% 3.32/1.02  ------ SAT Options
% 3.32/1.02  
% 3.32/1.02  --sat_mode                              false
% 3.32/1.02  --sat_fm_restart_options                ""
% 3.32/1.02  --sat_gr_def                            false
% 3.32/1.02  --sat_epr_types                         true
% 3.32/1.02  --sat_non_cyclic_types                  false
% 3.32/1.02  --sat_finite_models                     false
% 3.32/1.02  --sat_fm_lemmas                         false
% 3.32/1.02  --sat_fm_prep                           false
% 3.32/1.02  --sat_fm_uc_incr                        true
% 3.32/1.02  --sat_out_model                         small
% 3.32/1.02  --sat_out_clauses                       false
% 3.32/1.02  
% 3.32/1.02  ------ QBF Options
% 3.32/1.02  
% 3.32/1.02  --qbf_mode                              false
% 3.32/1.02  --qbf_elim_univ                         false
% 3.32/1.02  --qbf_dom_inst                          none
% 3.32/1.02  --qbf_dom_pre_inst                      false
% 3.32/1.02  --qbf_sk_in                             false
% 3.32/1.02  --qbf_pred_elim                         true
% 3.32/1.02  --qbf_split                             512
% 3.32/1.02  
% 3.32/1.02  ------ BMC1 Options
% 3.32/1.02  
% 3.32/1.02  --bmc1_incremental                      false
% 3.32/1.02  --bmc1_axioms                           reachable_all
% 3.32/1.02  --bmc1_min_bound                        0
% 3.32/1.02  --bmc1_max_bound                        -1
% 3.32/1.02  --bmc1_max_bound_default                -1
% 3.32/1.02  --bmc1_symbol_reachability              true
% 3.32/1.02  --bmc1_property_lemmas                  false
% 3.32/1.02  --bmc1_k_induction                      false
% 3.32/1.02  --bmc1_non_equiv_states                 false
% 3.32/1.02  --bmc1_deadlock                         false
% 3.32/1.02  --bmc1_ucm                              false
% 3.32/1.02  --bmc1_add_unsat_core                   none
% 3.32/1.02  --bmc1_unsat_core_children              false
% 3.32/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/1.02  --bmc1_out_stat                         full
% 3.32/1.02  --bmc1_ground_init                      false
% 3.32/1.02  --bmc1_pre_inst_next_state              false
% 3.32/1.02  --bmc1_pre_inst_state                   false
% 3.32/1.02  --bmc1_pre_inst_reach_state             false
% 3.32/1.02  --bmc1_out_unsat_core                   false
% 3.32/1.02  --bmc1_aig_witness_out                  false
% 3.32/1.02  --bmc1_verbose                          false
% 3.32/1.02  --bmc1_dump_clauses_tptp                false
% 3.32/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.32/1.02  --bmc1_dump_file                        -
% 3.32/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.32/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.32/1.02  --bmc1_ucm_extend_mode                  1
% 3.32/1.02  --bmc1_ucm_init_mode                    2
% 3.32/1.02  --bmc1_ucm_cone_mode                    none
% 3.32/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.32/1.02  --bmc1_ucm_relax_model                  4
% 3.32/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.32/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/1.02  --bmc1_ucm_layered_model                none
% 3.32/1.02  --bmc1_ucm_max_lemma_size               10
% 3.32/1.02  
% 3.32/1.02  ------ AIG Options
% 3.32/1.02  
% 3.32/1.02  --aig_mode                              false
% 3.32/1.02  
% 3.32/1.02  ------ Instantiation Options
% 3.32/1.02  
% 3.32/1.02  --instantiation_flag                    true
% 3.32/1.02  --inst_sos_flag                         true
% 3.32/1.02  --inst_sos_phase                        true
% 3.32/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/1.02  --inst_lit_sel_side                     num_symb
% 3.32/1.02  --inst_solver_per_active                1400
% 3.32/1.02  --inst_solver_calls_frac                1.
% 3.32/1.02  --inst_passive_queue_type               priority_queues
% 3.32/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/1.02  --inst_passive_queues_freq              [25;2]
% 3.32/1.02  --inst_dismatching                      true
% 3.32/1.02  --inst_eager_unprocessed_to_passive     true
% 3.32/1.02  --inst_prop_sim_given                   true
% 3.32/1.02  --inst_prop_sim_new                     false
% 3.32/1.02  --inst_subs_new                         false
% 3.32/1.02  --inst_eq_res_simp                      false
% 3.32/1.02  --inst_subs_given                       false
% 3.32/1.02  --inst_orphan_elimination               true
% 3.32/1.02  --inst_learning_loop_flag               true
% 3.32/1.02  --inst_learning_start                   3000
% 3.32/1.02  --inst_learning_factor                  2
% 3.32/1.02  --inst_start_prop_sim_after_learn       3
% 3.32/1.02  --inst_sel_renew                        solver
% 3.32/1.02  --inst_lit_activity_flag                true
% 3.32/1.02  --inst_restr_to_given                   false
% 3.32/1.02  --inst_activity_threshold               500
% 3.32/1.02  --inst_out_proof                        true
% 3.32/1.02  
% 3.32/1.02  ------ Resolution Options
% 3.32/1.02  
% 3.32/1.02  --resolution_flag                       true
% 3.32/1.02  --res_lit_sel                           adaptive
% 3.32/1.02  --res_lit_sel_side                      none
% 3.32/1.02  --res_ordering                          kbo
% 3.32/1.02  --res_to_prop_solver                    active
% 3.32/1.02  --res_prop_simpl_new                    false
% 3.32/1.02  --res_prop_simpl_given                  true
% 3.32/1.02  --res_passive_queue_type                priority_queues
% 3.32/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/1.02  --res_passive_queues_freq               [15;5]
% 3.32/1.02  --res_forward_subs                      full
% 3.32/1.02  --res_backward_subs                     full
% 3.32/1.02  --res_forward_subs_resolution           true
% 3.32/1.02  --res_backward_subs_resolution          true
% 3.32/1.02  --res_orphan_elimination                true
% 3.32/1.02  --res_time_limit                        2.
% 3.32/1.02  --res_out_proof                         true
% 3.32/1.02  
% 3.32/1.02  ------ Superposition Options
% 3.32/1.02  
% 3.32/1.02  --superposition_flag                    true
% 3.32/1.02  --sup_passive_queue_type                priority_queues
% 3.32/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.32/1.02  --demod_completeness_check              fast
% 3.32/1.02  --demod_use_ground                      true
% 3.32/1.02  --sup_to_prop_solver                    passive
% 3.32/1.02  --sup_prop_simpl_new                    true
% 3.32/1.02  --sup_prop_simpl_given                  true
% 3.32/1.02  --sup_fun_splitting                     true
% 3.32/1.02  --sup_smt_interval                      50000
% 3.32/1.02  
% 3.32/1.02  ------ Superposition Simplification Setup
% 3.32/1.02  
% 3.32/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.32/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.32/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.32/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.32/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.32/1.02  --sup_immed_triv                        [TrivRules]
% 3.32/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.02  --sup_immed_bw_main                     []
% 3.32/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.32/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.02  --sup_input_bw                          []
% 3.32/1.02  
% 3.32/1.02  ------ Combination Options
% 3.32/1.02  
% 3.32/1.02  --comb_res_mult                         3
% 3.32/1.02  --comb_sup_mult                         2
% 3.32/1.02  --comb_inst_mult                        10
% 3.32/1.02  
% 3.32/1.02  ------ Debug Options
% 3.32/1.02  
% 3.32/1.02  --dbg_backtrace                         false
% 3.32/1.02  --dbg_dump_prop_clauses                 false
% 3.32/1.02  --dbg_dump_prop_clauses_file            -
% 3.32/1.02  --dbg_out_stat                          false
% 3.32/1.02  ------ Parsing...
% 3.32/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/1.02  ------ Proving...
% 3.32/1.02  ------ Problem Properties 
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  clauses                                 16
% 3.32/1.02  conjectures                             4
% 3.32/1.02  EPR                                     2
% 3.32/1.02  Horn                                    14
% 3.32/1.02  unary                                   7
% 3.32/1.02  binary                                  3
% 3.32/1.02  lits                                    35
% 3.32/1.02  lits eq                                 8
% 3.32/1.02  fd_pure                                 0
% 3.32/1.02  fd_pseudo                               0
% 3.32/1.02  fd_cond                                 0
% 3.32/1.02  fd_pseudo_cond                          3
% 3.32/1.02  AC symbols                              0
% 3.32/1.02  
% 3.32/1.02  ------ Schedule dynamic 5 is on 
% 3.32/1.02  
% 3.32/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  ------ 
% 3.32/1.02  Current options:
% 3.32/1.02  ------ 
% 3.32/1.02  
% 3.32/1.02  ------ Input Options
% 3.32/1.02  
% 3.32/1.02  --out_options                           all
% 3.32/1.02  --tptp_safe_out                         true
% 3.32/1.02  --problem_path                          ""
% 3.32/1.02  --include_path                          ""
% 3.32/1.02  --clausifier                            res/vclausify_rel
% 3.32/1.02  --clausifier_options                    ""
% 3.32/1.02  --stdin                                 false
% 3.32/1.02  --stats_out                             all
% 3.32/1.02  
% 3.32/1.02  ------ General Options
% 3.32/1.02  
% 3.32/1.02  --fof                                   false
% 3.32/1.02  --time_out_real                         305.
% 3.32/1.02  --time_out_virtual                      -1.
% 3.32/1.02  --symbol_type_check                     false
% 3.32/1.02  --clausify_out                          false
% 3.32/1.02  --sig_cnt_out                           false
% 3.32/1.02  --trig_cnt_out                          false
% 3.32/1.02  --trig_cnt_out_tolerance                1.
% 3.32/1.02  --trig_cnt_out_sk_spl                   false
% 3.32/1.02  --abstr_cl_out                          false
% 3.32/1.02  
% 3.32/1.02  ------ Global Options
% 3.32/1.02  
% 3.32/1.02  --schedule                              default
% 3.32/1.02  --add_important_lit                     false
% 3.32/1.02  --prop_solver_per_cl                    1000
% 3.32/1.02  --min_unsat_core                        false
% 3.32/1.02  --soft_assumptions                      false
% 3.32/1.02  --soft_lemma_size                       3
% 3.32/1.02  --prop_impl_unit_size                   0
% 3.32/1.02  --prop_impl_unit                        []
% 3.32/1.02  --share_sel_clauses                     true
% 3.32/1.02  --reset_solvers                         false
% 3.32/1.02  --bc_imp_inh                            [conj_cone]
% 3.32/1.02  --conj_cone_tolerance                   3.
% 3.32/1.02  --extra_neg_conj                        none
% 3.32/1.02  --large_theory_mode                     true
% 3.32/1.02  --prolific_symb_bound                   200
% 3.32/1.02  --lt_threshold                          2000
% 3.32/1.02  --clause_weak_htbl                      true
% 3.32/1.02  --gc_record_bc_elim                     false
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing Options
% 3.32/1.02  
% 3.32/1.02  --preprocessing_flag                    true
% 3.32/1.02  --time_out_prep_mult                    0.1
% 3.32/1.02  --splitting_mode                        input
% 3.32/1.02  --splitting_grd                         true
% 3.32/1.02  --splitting_cvd                         false
% 3.32/1.02  --splitting_cvd_svl                     false
% 3.32/1.02  --splitting_nvd                         32
% 3.32/1.02  --sub_typing                            true
% 3.32/1.02  --prep_gs_sim                           true
% 3.32/1.02  --prep_unflatten                        true
% 3.32/1.02  --prep_res_sim                          true
% 3.32/1.02  --prep_upred                            true
% 3.32/1.02  --prep_sem_filter                       exhaustive
% 3.32/1.02  --prep_sem_filter_out                   false
% 3.32/1.02  --pred_elim                             true
% 3.32/1.02  --res_sim_input                         true
% 3.32/1.02  --eq_ax_congr_red                       true
% 3.32/1.02  --pure_diseq_elim                       true
% 3.32/1.02  --brand_transform                       false
% 3.32/1.02  --non_eq_to_eq                          false
% 3.32/1.02  --prep_def_merge                        true
% 3.32/1.02  --prep_def_merge_prop_impl              false
% 3.32/1.02  --prep_def_merge_mbd                    true
% 3.32/1.02  --prep_def_merge_tr_red                 false
% 3.32/1.02  --prep_def_merge_tr_cl                  false
% 3.32/1.02  --smt_preprocessing                     true
% 3.32/1.02  --smt_ac_axioms                         fast
% 3.32/1.02  --preprocessed_out                      false
% 3.32/1.02  --preprocessed_stats                    false
% 3.32/1.02  
% 3.32/1.02  ------ Abstraction refinement Options
% 3.32/1.02  
% 3.32/1.02  --abstr_ref                             []
% 3.32/1.02  --abstr_ref_prep                        false
% 3.32/1.02  --abstr_ref_until_sat                   false
% 3.32/1.02  --abstr_ref_sig_restrict                funpre
% 3.32/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/1.02  --abstr_ref_under                       []
% 3.32/1.02  
% 3.32/1.02  ------ SAT Options
% 3.32/1.02  
% 3.32/1.02  --sat_mode                              false
% 3.32/1.02  --sat_fm_restart_options                ""
% 3.32/1.02  --sat_gr_def                            false
% 3.32/1.02  --sat_epr_types                         true
% 3.32/1.02  --sat_non_cyclic_types                  false
% 3.32/1.02  --sat_finite_models                     false
% 3.32/1.02  --sat_fm_lemmas                         false
% 3.32/1.02  --sat_fm_prep                           false
% 3.32/1.02  --sat_fm_uc_incr                        true
% 3.32/1.02  --sat_out_model                         small
% 3.32/1.02  --sat_out_clauses                       false
% 3.32/1.02  
% 3.32/1.02  ------ QBF Options
% 3.32/1.02  
% 3.32/1.02  --qbf_mode                              false
% 3.32/1.02  --qbf_elim_univ                         false
% 3.32/1.02  --qbf_dom_inst                          none
% 3.32/1.02  --qbf_dom_pre_inst                      false
% 3.32/1.02  --qbf_sk_in                             false
% 3.32/1.02  --qbf_pred_elim                         true
% 3.32/1.02  --qbf_split                             512
% 3.32/1.02  
% 3.32/1.02  ------ BMC1 Options
% 3.32/1.02  
% 3.32/1.02  --bmc1_incremental                      false
% 3.32/1.02  --bmc1_axioms                           reachable_all
% 3.32/1.02  --bmc1_min_bound                        0
% 3.32/1.02  --bmc1_max_bound                        -1
% 3.32/1.02  --bmc1_max_bound_default                -1
% 3.32/1.02  --bmc1_symbol_reachability              true
% 3.32/1.02  --bmc1_property_lemmas                  false
% 3.32/1.02  --bmc1_k_induction                      false
% 3.32/1.02  --bmc1_non_equiv_states                 false
% 3.32/1.02  --bmc1_deadlock                         false
% 3.32/1.02  --bmc1_ucm                              false
% 3.32/1.02  --bmc1_add_unsat_core                   none
% 3.32/1.02  --bmc1_unsat_core_children              false
% 3.32/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/1.02  --bmc1_out_stat                         full
% 3.32/1.02  --bmc1_ground_init                      false
% 3.32/1.02  --bmc1_pre_inst_next_state              false
% 3.32/1.02  --bmc1_pre_inst_state                   false
% 3.32/1.02  --bmc1_pre_inst_reach_state             false
% 3.32/1.02  --bmc1_out_unsat_core                   false
% 3.32/1.02  --bmc1_aig_witness_out                  false
% 3.32/1.02  --bmc1_verbose                          false
% 3.32/1.02  --bmc1_dump_clauses_tptp                false
% 3.32/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.32/1.02  --bmc1_dump_file                        -
% 3.32/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.32/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.32/1.02  --bmc1_ucm_extend_mode                  1
% 3.32/1.02  --bmc1_ucm_init_mode                    2
% 3.32/1.02  --bmc1_ucm_cone_mode                    none
% 3.32/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.32/1.02  --bmc1_ucm_relax_model                  4
% 3.32/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.32/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/1.02  --bmc1_ucm_layered_model                none
% 3.32/1.02  --bmc1_ucm_max_lemma_size               10
% 3.32/1.02  
% 3.32/1.02  ------ AIG Options
% 3.32/1.02  
% 3.32/1.02  --aig_mode                              false
% 3.32/1.02  
% 3.32/1.02  ------ Instantiation Options
% 3.32/1.02  
% 3.32/1.02  --instantiation_flag                    true
% 3.32/1.02  --inst_sos_flag                         true
% 3.32/1.02  --inst_sos_phase                        true
% 3.32/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/1.02  --inst_lit_sel_side                     none
% 3.32/1.02  --inst_solver_per_active                1400
% 3.32/1.02  --inst_solver_calls_frac                1.
% 3.32/1.02  --inst_passive_queue_type               priority_queues
% 3.32/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/1.02  --inst_passive_queues_freq              [25;2]
% 3.32/1.02  --inst_dismatching                      true
% 3.32/1.02  --inst_eager_unprocessed_to_passive     true
% 3.32/1.02  --inst_prop_sim_given                   true
% 3.32/1.02  --inst_prop_sim_new                     false
% 3.32/1.02  --inst_subs_new                         false
% 3.32/1.02  --inst_eq_res_simp                      false
% 3.32/1.02  --inst_subs_given                       false
% 3.32/1.02  --inst_orphan_elimination               true
% 3.32/1.02  --inst_learning_loop_flag               true
% 3.32/1.02  --inst_learning_start                   3000
% 3.32/1.02  --inst_learning_factor                  2
% 3.32/1.02  --inst_start_prop_sim_after_learn       3
% 3.32/1.02  --inst_sel_renew                        solver
% 3.32/1.02  --inst_lit_activity_flag                true
% 3.32/1.02  --inst_restr_to_given                   false
% 3.32/1.02  --inst_activity_threshold               500
% 3.32/1.02  --inst_out_proof                        true
% 3.32/1.02  
% 3.32/1.02  ------ Resolution Options
% 3.32/1.02  
% 3.32/1.02  --resolution_flag                       false
% 3.32/1.02  --res_lit_sel                           adaptive
% 3.32/1.02  --res_lit_sel_side                      none
% 3.32/1.02  --res_ordering                          kbo
% 3.32/1.02  --res_to_prop_solver                    active
% 3.32/1.02  --res_prop_simpl_new                    false
% 3.32/1.02  --res_prop_simpl_given                  true
% 3.32/1.02  --res_passive_queue_type                priority_queues
% 3.32/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/1.02  --res_passive_queues_freq               [15;5]
% 3.32/1.02  --res_forward_subs                      full
% 3.32/1.02  --res_backward_subs                     full
% 3.32/1.02  --res_forward_subs_resolution           true
% 3.32/1.02  --res_backward_subs_resolution          true
% 3.32/1.02  --res_orphan_elimination                true
% 3.32/1.02  --res_time_limit                        2.
% 3.32/1.02  --res_out_proof                         true
% 3.32/1.02  
% 3.32/1.02  ------ Superposition Options
% 3.32/1.02  
% 3.32/1.02  --superposition_flag                    true
% 3.32/1.02  --sup_passive_queue_type                priority_queues
% 3.32/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.32/1.02  --demod_completeness_check              fast
% 3.32/1.02  --demod_use_ground                      true
% 3.32/1.02  --sup_to_prop_solver                    passive
% 3.32/1.02  --sup_prop_simpl_new                    true
% 3.32/1.02  --sup_prop_simpl_given                  true
% 3.32/1.02  --sup_fun_splitting                     true
% 3.32/1.02  --sup_smt_interval                      50000
% 3.32/1.02  
% 3.32/1.02  ------ Superposition Simplification Setup
% 3.32/1.02  
% 3.32/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.32/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.32/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.32/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.32/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.32/1.02  --sup_immed_triv                        [TrivRules]
% 3.32/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.02  --sup_immed_bw_main                     []
% 3.32/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.32/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.02  --sup_input_bw                          []
% 3.32/1.02  
% 3.32/1.02  ------ Combination Options
% 3.32/1.02  
% 3.32/1.02  --comb_res_mult                         3
% 3.32/1.02  --comb_sup_mult                         2
% 3.32/1.02  --comb_inst_mult                        10
% 3.32/1.02  
% 3.32/1.02  ------ Debug Options
% 3.32/1.02  
% 3.32/1.02  --dbg_backtrace                         false
% 3.32/1.02  --dbg_dump_prop_clauses                 false
% 3.32/1.02  --dbg_dump_prop_clauses_file            -
% 3.32/1.02  --dbg_out_stat                          false
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  ------ Proving...
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  % SZS status Theorem for theBenchmark.p
% 3.32/1.02  
% 3.32/1.02   Resolution empty clause
% 3.32/1.02  
% 3.32/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/1.02  
% 3.32/1.02  fof(f5,axiom,(
% 3.32/1.02    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.32/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.02  
% 3.32/1.02  fof(f35,plain,(
% 3.32/1.02    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.32/1.02    inference(cnf_transformation,[],[f5])).
% 3.32/1.02  
% 3.32/1.02  fof(f2,axiom,(
% 3.32/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.32/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.02  
% 3.32/1.02  fof(f31,plain,(
% 3.32/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.32/1.02    inference(cnf_transformation,[],[f2])).
% 3.32/1.02  
% 3.32/1.02  fof(f3,axiom,(
% 3.32/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.32/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.02  
% 3.32/1.02  fof(f32,plain,(
% 3.32/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.32/1.02    inference(cnf_transformation,[],[f3])).
% 3.32/1.02  
% 3.32/1.02  fof(f50,plain,(
% 3.32/1.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.32/1.02    inference(definition_unfolding,[],[f31,f32,f32])).
% 3.32/1.02  
% 3.32/1.02  fof(f9,conjecture,(
% 3.32/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 3.32/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.02  
% 3.32/1.02  fof(f10,negated_conjecture,(
% 3.32/1.02    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 3.32/1.02    inference(negated_conjecture,[],[f9])).
% 3.32/1.02  
% 3.32/1.02  fof(f16,plain,(
% 3.32/1.02    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.32/1.02    inference(ennf_transformation,[],[f10])).
% 3.32/1.02  
% 3.32/1.02  fof(f17,plain,(
% 3.32/1.02    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.32/1.02    inference(flattening,[],[f16])).
% 3.32/1.02  
% 3.32/1.02  fof(f23,plain,(
% 3.32/1.02    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 3.32/1.02    introduced(choice_axiom,[])).
% 3.32/1.02  
% 3.32/1.02  fof(f24,plain,(
% 3.32/1.02    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) & r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 3.32/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f23])).
% 3.32/1.02  
% 3.32/1.02  fof(f39,plain,(
% 3.32/1.02    v1_relat_1(sK3)),
% 3.32/1.02    inference(cnf_transformation,[],[f24])).
% 3.32/1.02  
% 3.32/1.02  fof(f8,axiom,(
% 3.32/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 3.32/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.02  
% 3.32/1.02  fof(f14,plain,(
% 3.32/1.02    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.32/1.02    inference(ennf_transformation,[],[f8])).
% 3.32/1.02  
% 3.32/1.02  fof(f15,plain,(
% 3.32/1.02    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.32/1.02    inference(flattening,[],[f14])).
% 3.32/1.02  
% 3.32/1.02  fof(f38,plain,(
% 3.32/1.02    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.32/1.02    inference(cnf_transformation,[],[f15])).
% 3.32/1.02  
% 3.32/1.02  fof(f4,axiom,(
% 3.32/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.32/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.02  
% 3.32/1.02  fof(f33,plain,(
% 3.32/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.32/1.02    inference(cnf_transformation,[],[f4])).
% 3.32/1.02  
% 3.32/1.02  fof(f43,plain,(
% 3.32/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.32/1.02    inference(definition_unfolding,[],[f33,f32])).
% 3.32/1.02  
% 3.32/1.02  fof(f51,plain,(
% 3.32/1.02    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.32/1.02    inference(definition_unfolding,[],[f38,f43])).
% 3.32/1.02  
% 3.32/1.02  fof(f40,plain,(
% 3.32/1.02    v1_funct_1(sK3)),
% 3.32/1.02    inference(cnf_transformation,[],[f24])).
% 3.32/1.02  
% 3.32/1.02  fof(f41,plain,(
% 3.32/1.02    r2_hidden(sK1,k3_xboole_0(k1_relat_1(sK3),sK2))),
% 3.32/1.02    inference(cnf_transformation,[],[f24])).
% 3.32/1.02  
% 3.32/1.02  fof(f52,plain,(
% 3.32/1.02    r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2)))),
% 3.32/1.02    inference(definition_unfolding,[],[f41,f43])).
% 3.32/1.02  
% 3.32/1.02  fof(f6,axiom,(
% 3.32/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 3.32/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.02  
% 3.32/1.02  fof(f11,plain,(
% 3.32/1.02    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.32/1.02    inference(ennf_transformation,[],[f6])).
% 3.32/1.02  
% 3.32/1.02  fof(f12,plain,(
% 3.32/1.02    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.32/1.02    inference(flattening,[],[f11])).
% 3.32/1.02  
% 3.32/1.02  fof(f36,plain,(
% 3.32/1.02    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.32/1.02    inference(cnf_transformation,[],[f12])).
% 3.32/1.02  
% 3.32/1.02  fof(f1,axiom,(
% 3.32/1.02    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.32/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.02  
% 3.32/1.02  fof(f18,plain,(
% 3.32/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.32/1.02    inference(nnf_transformation,[],[f1])).
% 3.32/1.02  
% 3.32/1.02  fof(f19,plain,(
% 3.32/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.32/1.02    inference(flattening,[],[f18])).
% 3.32/1.02  
% 3.32/1.02  fof(f20,plain,(
% 3.32/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.32/1.02    inference(rectify,[],[f19])).
% 3.32/1.02  
% 3.32/1.02  fof(f21,plain,(
% 3.32/1.02    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.32/1.02    introduced(choice_axiom,[])).
% 3.32/1.02  
% 3.32/1.02  fof(f22,plain,(
% 3.32/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.32/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.32/1.02  
% 3.32/1.02  fof(f25,plain,(
% 3.32/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.32/1.02    inference(cnf_transformation,[],[f22])).
% 3.32/1.02  
% 3.32/1.02  fof(f49,plain,(
% 3.32/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2) )),
% 3.32/1.02    inference(definition_unfolding,[],[f25,f43])).
% 3.32/1.02  
% 3.32/1.02  fof(f55,plain,(
% 3.32/1.02    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.32/1.02    inference(equality_resolution,[],[f49])).
% 3.32/1.02  
% 3.32/1.02  fof(f7,axiom,(
% 3.32/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 3.32/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.02  
% 3.32/1.02  fof(f13,plain,(
% 3.32/1.02    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 3.32/1.02    inference(ennf_transformation,[],[f7])).
% 3.32/1.02  
% 3.32/1.02  fof(f37,plain,(
% 3.32/1.02    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 3.32/1.02    inference(cnf_transformation,[],[f13])).
% 3.32/1.02  
% 3.32/1.02  fof(f42,plain,(
% 3.32/1.02    k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)),
% 3.32/1.02    inference(cnf_transformation,[],[f24])).
% 3.32/1.02  
% 3.32/1.02  fof(f34,plain,(
% 3.32/1.02    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.32/1.02    inference(cnf_transformation,[],[f5])).
% 3.32/1.02  
% 3.32/1.02  cnf(c_7,plain,
% 3.32/1.02      ( v1_funct_1(k6_relat_1(X0)) ),
% 3.32/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_418,plain,
% 3.32/1.02      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_6,plain,
% 3.32/1.02      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.32/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_15,negated_conjecture,
% 3.32/1.02      ( v1_relat_1(sK3) ),
% 3.32/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_411,plain,
% 3.32/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_11,plain,
% 3.32/1.02      ( ~ v1_relat_1(X0)
% 3.32/1.02      | ~ v1_funct_1(X0)
% 3.32/1.02      | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) ),
% 3.32/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_414,plain,
% 3.32/1.02      ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),X0))
% 3.32/1.02      | v1_relat_1(X0) != iProver_top
% 3.32/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_667,plain,
% 3.32/1.02      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK3))
% 3.32/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.32/1.02      inference(superposition,[status(thm)],[c_411,c_414]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_14,negated_conjecture,
% 3.32/1.02      ( v1_funct_1(sK3) ),
% 3.32/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_17,plain,
% 3.32/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_816,plain,
% 3.32/1.02      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK3)) ),
% 3.32/1.02      inference(global_propositional_subsumption,[status(thm)],[c_667,c_17]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_819,plain,
% 3.32/1.02      ( k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK3))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK3)) ),
% 3.32/1.02      inference(superposition,[status(thm)],[c_6,c_816]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_13,negated_conjecture,
% 3.32/1.02      ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) ),
% 3.32/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_413,plain,
% 3.32/1.02      ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) = iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_609,plain,
% 3.32/1.02      ( r2_hidden(sK1,k1_setfam_1(k1_enumset1(sK2,sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.32/1.02      inference(demodulation,[status(thm)],[c_6,c_413]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_1079,plain,
% 3.32/1.02      ( r2_hidden(sK1,k1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))) = iProver_top ),
% 3.32/1.02      inference(demodulation,[status(thm)],[c_819,c_609]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_9,plain,
% 3.32/1.02      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 3.32/1.02      | ~ v1_relat_1(X1)
% 3.32/1.02      | ~ v1_relat_1(X2)
% 3.32/1.02      | ~ v1_funct_1(X1)
% 3.32/1.02      | ~ v1_funct_1(X2)
% 3.32/1.02      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.32/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_416,plain,
% 3.32/1.02      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.32/1.02      | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 3.32/1.02      | v1_relat_1(X0) != iProver_top
% 3.32/1.02      | v1_relat_1(X1) != iProver_top
% 3.32/1.02      | v1_funct_1(X0) != iProver_top
% 3.32/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_1284,plain,
% 3.32/1.02      ( k1_funct_1(sK3,k1_funct_1(k6_relat_1(sK2),sK1)) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
% 3.32/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 3.32/1.02      | v1_relat_1(sK3) != iProver_top
% 3.32/1.02      | v1_funct_1(k6_relat_1(sK2)) != iProver_top
% 3.32/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.32/1.02      inference(superposition,[status(thm)],[c_1079,c_416]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_5,plain,
% 3.32/1.02      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 3.32/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_419,plain,
% 3.32/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.32/1.02      | r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_729,plain,
% 3.32/1.02      ( r2_hidden(sK1,sK2) = iProver_top ),
% 3.32/1.02      inference(superposition,[status(thm)],[c_609,c_419]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_10,plain,
% 3.32/1.02      ( ~ r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
% 3.32/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_415,plain,
% 3.32/1.02      ( k1_funct_1(k6_relat_1(X0),X1) = X1 | r2_hidden(X1,X0) != iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_997,plain,
% 3.32/1.02      ( k1_funct_1(k6_relat_1(sK2),sK1) = sK1 ),
% 3.32/1.02      inference(superposition,[status(thm)],[c_729,c_415]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_1285,plain,
% 3.32/1.02      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) = k1_funct_1(sK3,sK1)
% 3.32/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 3.32/1.02      | v1_relat_1(sK3) != iProver_top
% 3.32/1.02      | v1_funct_1(k6_relat_1(sK2)) != iProver_top
% 3.32/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.32/1.02      inference(light_normalisation,[status(thm)],[c_1284,c_997]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_16,plain,
% 3.32/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_12,negated_conjecture,
% 3.32/1.02      ( k1_funct_1(sK3,sK1) != k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
% 3.32/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_164,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_442,plain,
% 3.32/1.02      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != X0
% 3.32/1.02      | k1_funct_1(sK3,sK1) != X0
% 3.32/1.02      | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) ),
% 3.32/1.02      inference(instantiation,[status(thm)],[c_164]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_447,plain,
% 3.32/1.02      ( k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1) != k1_funct_1(sK3,sK1)
% 3.32/1.02      | k1_funct_1(sK3,sK1) = k1_funct_1(k5_relat_1(k6_relat_1(sK2),sK3),sK1)
% 3.32/1.02      | k1_funct_1(sK3,sK1) != k1_funct_1(sK3,sK1) ),
% 3.32/1.02      inference(instantiation,[status(thm)],[c_442]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_163,plain,( X0 = X0 ),theory(equality) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_453,plain,
% 3.32/1.02      ( k1_funct_1(sK3,sK1) = k1_funct_1(sK3,sK1) ),
% 3.32/1.02      inference(instantiation,[status(thm)],[c_163]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_8,plain,
% 3.32/1.02      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.32/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_2393,plain,
% 3.32/1.02      ( v1_relat_1(k6_relat_1(sK2)) ),
% 3.32/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_2394,plain,
% 3.32/1.02      ( v1_relat_1(k6_relat_1(sK2)) = iProver_top ),
% 3.32/1.02      inference(predicate_to_equality,[status(thm)],[c_2393]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_3731,plain,
% 3.32/1.02      ( v1_funct_1(k6_relat_1(sK2)) != iProver_top ),
% 3.32/1.02      inference(global_propositional_subsumption,
% 3.32/1.02                [status(thm)],
% 3.32/1.02                [c_1285,c_16,c_17,c_12,c_447,c_453,c_2394]) ).
% 3.32/1.02  
% 3.32/1.02  cnf(c_3735,plain,
% 3.32/1.02      ( $false ),
% 3.32/1.02      inference(superposition,[status(thm)],[c_418,c_3731]) ).
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/1.02  
% 3.32/1.02  ------                               Statistics
% 3.32/1.02  
% 3.32/1.02  ------ General
% 3.32/1.02  
% 3.32/1.02  abstr_ref_over_cycles:                  0
% 3.32/1.02  abstr_ref_under_cycles:                 0
% 3.32/1.02  gc_basic_clause_elim:                   0
% 3.32/1.02  forced_gc_time:                         0
% 3.32/1.02  parsing_time:                           0.008
% 3.32/1.02  unif_index_cands_time:                  0.
% 3.32/1.02  unif_index_add_time:                    0.
% 3.32/1.02  orderings_time:                         0.
% 3.32/1.02  out_proof_time:                         0.01
% 3.32/1.02  total_time:                             0.219
% 3.32/1.02  num_of_symbols:                         44
% 3.32/1.02  num_of_terms:                           5452
% 3.32/1.02  
% 3.32/1.02  ------ Preprocessing
% 3.32/1.02  
% 3.32/1.02  num_of_splits:                          0
% 3.32/1.02  num_of_split_atoms:                     0
% 3.32/1.02  num_of_reused_defs:                     0
% 3.32/1.02  num_eq_ax_congr_red:                    6
% 3.32/1.02  num_of_sem_filtered_clauses:            1
% 3.32/1.02  num_of_subtypes:                        0
% 3.32/1.02  monotx_restored_types:                  0
% 3.32/1.02  sat_num_of_epr_types:                   0
% 3.32/1.02  sat_num_of_non_cyclic_types:            0
% 3.32/1.02  sat_guarded_non_collapsed_types:        0
% 3.32/1.02  num_pure_diseq_elim:                    0
% 3.32/1.02  simp_replaced_by:                       0
% 3.32/1.02  res_preprocessed:                       71
% 3.32/1.02  prep_upred:                             0
% 3.32/1.02  prep_unflattend:                        0
% 3.32/1.02  smt_new_axioms:                         0
% 3.32/1.02  pred_elim_cands:                        3
% 3.32/1.02  pred_elim:                              0
% 3.32/1.02  pred_elim_cl:                           0
% 3.32/1.02  pred_elim_cycles:                       1
% 3.32/1.02  merged_defs:                            0
% 3.32/1.02  merged_defs_ncl:                        0
% 3.32/1.02  bin_hyper_res:                          0
% 3.32/1.02  prep_cycles:                            3
% 3.32/1.02  pred_elim_time:                         0.
% 3.32/1.02  splitting_time:                         0.
% 3.32/1.02  sem_filter_time:                        0.
% 3.32/1.02  monotx_time:                            0.
% 3.32/1.02  subtype_inf_time:                       0.
% 3.32/1.02  
% 3.32/1.02  ------ Problem properties
% 3.32/1.02  
% 3.32/1.02  clauses:                                16
% 3.32/1.02  conjectures:                            4
% 3.32/1.02  epr:                                    2
% 3.32/1.02  horn:                                   14
% 3.32/1.02  ground:                                 4
% 3.32/1.02  unary:                                  7
% 3.32/1.02  binary:                                 3
% 3.32/1.02  lits:                                   35
% 3.32/1.02  lits_eq:                                8
% 3.32/1.02  fd_pure:                                0
% 3.32/1.02  fd_pseudo:                              0
% 3.32/1.02  fd_cond:                                0
% 3.32/1.02  fd_pseudo_cond:                         3
% 3.32/1.02  ac_symbols:                             0
% 3.32/1.02  
% 3.32/1.02  ------ Propositional Solver
% 3.32/1.02  
% 3.32/1.02  prop_solver_calls:                      28
% 3.32/1.02  prop_fast_solver_calls:                 466
% 3.32/1.02  smt_solver_calls:                       0
% 3.32/1.02  smt_fast_solver_calls:                  0
% 3.32/1.02  prop_num_of_clauses:                    1593
% 3.32/1.02  prop_preprocess_simplified:             4057
% 3.32/1.02  prop_fo_subsumed:                       7
% 3.32/1.02  prop_solver_time:                       0.
% 3.32/1.02  smt_solver_time:                        0.
% 3.32/1.02  smt_fast_solver_time:                   0.
% 3.32/1.02  prop_fast_solver_time:                  0.
% 3.32/1.02  prop_unsat_core_time:                   0.
% 3.32/1.02  
% 3.32/1.02  ------ QBF
% 3.32/1.02  
% 3.32/1.02  qbf_q_res:                              0
% 3.32/1.02  qbf_num_tautologies:                    0
% 3.32/1.02  qbf_prep_cycles:                        0
% 3.32/1.02  
% 3.32/1.02  ------ BMC1
% 3.32/1.02  
% 3.32/1.02  bmc1_current_bound:                     -1
% 3.32/1.02  bmc1_last_solved_bound:                 -1
% 3.32/1.02  bmc1_unsat_core_size:                   -1
% 3.32/1.02  bmc1_unsat_core_parents_size:           -1
% 3.32/1.02  bmc1_merge_next_fun:                    0
% 3.32/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.32/1.02  
% 3.32/1.02  ------ Instantiation
% 3.32/1.02  
% 3.32/1.02  inst_num_of_clauses:                    504
% 3.32/1.02  inst_num_in_passive:                    177
% 3.32/1.02  inst_num_in_active:                     252
% 3.32/1.02  inst_num_in_unprocessed:                75
% 3.32/1.02  inst_num_of_loops:                      300
% 3.32/1.02  inst_num_of_learning_restarts:          0
% 3.32/1.02  inst_num_moves_active_passive:          44
% 3.32/1.02  inst_lit_activity:                      0
% 3.32/1.02  inst_lit_activity_moves:                0
% 3.32/1.02  inst_num_tautologies:                   0
% 3.32/1.02  inst_num_prop_implied:                  0
% 3.32/1.02  inst_num_existing_simplified:           0
% 3.32/1.02  inst_num_eq_res_simplified:             0
% 3.32/1.02  inst_num_child_elim:                    0
% 3.32/1.02  inst_num_of_dismatching_blockings:      172
% 3.32/1.02  inst_num_of_non_proper_insts:           637
% 3.32/1.02  inst_num_of_duplicates:                 0
% 3.32/1.02  inst_inst_num_from_inst_to_res:         0
% 3.32/1.02  inst_dismatching_checking_time:         0.
% 3.32/1.02  
% 3.32/1.02  ------ Resolution
% 3.32/1.02  
% 3.32/1.02  res_num_of_clauses:                     0
% 3.32/1.02  res_num_in_passive:                     0
% 3.32/1.02  res_num_in_active:                      0
% 3.32/1.02  res_num_of_loops:                       74
% 3.32/1.02  res_forward_subset_subsumed:            135
% 3.32/1.02  res_backward_subset_subsumed:           0
% 3.32/1.02  res_forward_subsumed:                   0
% 3.32/1.02  res_backward_subsumed:                  0
% 3.32/1.02  res_forward_subsumption_resolution:     0
% 3.32/1.02  res_backward_subsumption_resolution:    0
% 3.32/1.02  res_clause_to_clause_subsumption:       786
% 3.32/1.02  res_orphan_elimination:                 0
% 3.32/1.02  res_tautology_del:                      105
% 3.32/1.02  res_num_eq_res_simplified:              0
% 3.32/1.02  res_num_sel_changes:                    0
% 3.32/1.02  res_moves_from_active_to_pass:          0
% 3.32/1.02  
% 3.32/1.02  ------ Superposition
% 3.32/1.02  
% 3.32/1.02  sup_time_total:                         0.
% 3.32/1.02  sup_time_generating:                    0.
% 3.32/1.02  sup_time_sim_full:                      0.
% 3.32/1.02  sup_time_sim_immed:                     0.
% 3.32/1.02  
% 3.32/1.02  sup_num_of_clauses:                     203
% 3.32/1.02  sup_num_in_active:                      55
% 3.32/1.02  sup_num_in_passive:                     148
% 3.32/1.02  sup_num_of_loops:                       59
% 3.32/1.02  sup_fw_superposition:                   145
% 3.32/1.02  sup_bw_superposition:                   123
% 3.32/1.02  sup_immediate_simplified:               38
% 3.32/1.02  sup_given_eliminated:                   0
% 3.32/1.02  comparisons_done:                       0
% 3.32/1.02  comparisons_avoided:                    13
% 3.32/1.02  
% 3.32/1.02  ------ Simplifications
% 3.32/1.02  
% 3.32/1.02  
% 3.32/1.02  sim_fw_subset_subsumed:                 2
% 3.32/1.02  sim_bw_subset_subsumed:                 2
% 3.32/1.02  sim_fw_subsumed:                        14
% 3.32/1.02  sim_bw_subsumed:                        5
% 3.32/1.02  sim_fw_subsumption_res:                 0
% 3.32/1.02  sim_bw_subsumption_res:                 0
% 3.32/1.02  sim_tautology_del:                      21
% 3.32/1.02  sim_eq_tautology_del:                   3
% 3.32/1.02  sim_eq_res_simp:                        4
% 3.32/1.02  sim_fw_demodulated:                     18
% 3.32/1.02  sim_bw_demodulated:                     2
% 3.32/1.02  sim_light_normalised:                   3
% 3.32/1.02  sim_joinable_taut:                      0
% 3.32/1.02  sim_joinable_simp:                      0
% 3.32/1.02  sim_ac_normalised:                      0
% 3.32/1.02  sim_smt_subsumption:                    0
% 3.32/1.02  
%------------------------------------------------------------------------------
