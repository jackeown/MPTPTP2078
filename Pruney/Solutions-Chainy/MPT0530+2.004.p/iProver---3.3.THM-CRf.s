%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:36 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 216 expanded)
%              Number of clauses        :   38 (  71 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   23
%              Number of atoms          :  254 ( 869 expanded)
%              Number of equality atoms :   90 ( 244 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f2])).

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
    inference(flattening,[],[f19])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5))
      & r1_tarski(sK3,sK4)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5))
    & r1_tarski(sK3,sK4)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f29])).

fof(f48,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f41,f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f47,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1422,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1425,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1835,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X2,k4_xboole_0(X0,X1)),X1) != iProver_top
    | r2_hidden(sK1(X2,k4_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1425])).

cnf(c_2491,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X1
    | r2_hidden(sK1(X1,X0),k1_xboole_0) != iProver_top
    | r2_hidden(sK1(X1,k4_xboole_0(X0,k1_xboole_0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1835])).

cnf(c_2513,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top
    | r2_hidden(sK1(X1,X0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2491,c_9])).

cnf(c_2514,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2513,c_9])).

cnf(c_1585,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1425])).

cnf(c_2741,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2514,c_1585])).

cnf(c_2743,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_2741])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1420,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK2(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3756,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_1420])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1424,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3865,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3756,c_1424])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_167,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_168,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_167])).

cnf(c_1418,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_9356,plain,
    ( k4_xboole_0(sK3,X0) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3865,c_1418])).

cnf(c_3866,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3756,c_1425])).

cnf(c_10654,plain,
    ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9356,c_3866])).

cnf(c_12,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10891,plain,
    ( k1_setfam_1(k1_enumset1(sK3,sK3,sK4)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10654,c_12])).

cnf(c_10946,plain,
    ( k1_setfam_1(k1_enumset1(sK3,sK3,sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_10891,c_9])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_160,plain,
    ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_161,plain,
    ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK5) = k8_relat_1(X0,k8_relat_1(X1,sK5)) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_1442,plain,
    ( k8_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),sK5) = k8_relat_1(X0,k8_relat_1(X1,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_161,c_12])).

cnf(c_11273,plain,
    ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) = k8_relat_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_10946,c_1442])).

cnf(c_14,negated_conjecture,
    ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11841,plain,
    ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_11273,c_14])).

cnf(c_11842,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_11841])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 4.13/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.01  
% 4.13/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.13/1.01  
% 4.13/1.01  ------  iProver source info
% 4.13/1.01  
% 4.13/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.13/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.13/1.01  git: non_committed_changes: false
% 4.13/1.01  git: last_make_outside_of_git: false
% 4.13/1.01  
% 4.13/1.01  ------ 
% 4.13/1.01  ------ Parsing...
% 4.13/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  ------ Proving...
% 4.13/1.01  ------ Problem Properties 
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  clauses                                 15
% 4.13/1.01  conjectures                             3
% 4.13/1.01  EPR                                     1
% 4.13/1.01  Horn                                    10
% 4.13/1.01  unary                                   4
% 4.13/1.01  binary                                  4
% 4.13/1.01  lits                                    34
% 4.13/1.01  lits eq                                 9
% 4.13/1.01  fd_pure                                 0
% 4.13/1.01  fd_pseudo                               0
% 4.13/1.01  fd_cond                                 0
% 4.13/1.01  fd_pseudo_cond                          5
% 4.13/1.01  AC symbols                              0
% 4.13/1.01  
% 4.13/1.01  ------ Input Options Time Limit: Unbounded
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing...
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 4.13/1.01  Current options:
% 4.13/1.01  ------ 
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing...
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing...
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing...
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  % SZS status Theorem for theBenchmark.p
% 4.13/1.01  
% 4.13/1.01   Resolution empty clause
% 4.13/1.01  
% 4.13/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.13/1.01  
% 4.13/1.01  fof(f3,axiom,(
% 4.13/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f14,plain,(
% 4.13/1.01    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 4.13/1.01    inference(ennf_transformation,[],[f3])).
% 4.13/1.01  
% 4.13/1.01  fof(f24,plain,(
% 4.13/1.01    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 4.13/1.01    inference(nnf_transformation,[],[f14])).
% 4.13/1.01  
% 4.13/1.01  fof(f25,plain,(
% 4.13/1.01    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 4.13/1.01    introduced(choice_axiom,[])).
% 4.13/1.01  
% 4.13/1.01  fof(f26,plain,(
% 4.13/1.01    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 4.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 4.13/1.01  
% 4.13/1.01  fof(f38,plain,(
% 4.13/1.01    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f26])).
% 4.13/1.01  
% 4.13/1.01  fof(f4,axiom,(
% 4.13/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f40,plain,(
% 4.13/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.13/1.01    inference(cnf_transformation,[],[f4])).
% 4.13/1.01  
% 4.13/1.01  fof(f2,axiom,(
% 4.13/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f19,plain,(
% 4.13/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.13/1.01    inference(nnf_transformation,[],[f2])).
% 4.13/1.01  
% 4.13/1.01  fof(f20,plain,(
% 4.13/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.13/1.01    inference(flattening,[],[f19])).
% 4.13/1.01  
% 4.13/1.01  fof(f21,plain,(
% 4.13/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.13/1.01    inference(rectify,[],[f20])).
% 4.13/1.01  
% 4.13/1.01  fof(f22,plain,(
% 4.13/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.13/1.01    introduced(choice_axiom,[])).
% 4.13/1.01  
% 4.13/1.01  fof(f23,plain,(
% 4.13/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 4.13/1.01  
% 4.13/1.01  fof(f33,plain,(
% 4.13/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.13/1.01    inference(cnf_transformation,[],[f23])).
% 4.13/1.01  
% 4.13/1.01  fof(f53,plain,(
% 4.13/1.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 4.13/1.01    inference(equality_resolution,[],[f33])).
% 4.13/1.01  
% 4.13/1.01  fof(f7,axiom,(
% 4.13/1.01    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f15,plain,(
% 4.13/1.01    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 4.13/1.01    inference(ennf_transformation,[],[f7])).
% 4.13/1.01  
% 4.13/1.01  fof(f27,plain,(
% 4.13/1.01    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 4.13/1.01    introduced(choice_axiom,[])).
% 4.13/1.01  
% 4.13/1.01  fof(f28,plain,(
% 4.13/1.01    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 4.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f27])).
% 4.13/1.01  
% 4.13/1.01  fof(f43,plain,(
% 4.13/1.01    ( ! [X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X0,X1)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f28])).
% 4.13/1.01  
% 4.13/1.01  fof(f32,plain,(
% 4.13/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.13/1.01    inference(cnf_transformation,[],[f23])).
% 4.13/1.01  
% 4.13/1.01  fof(f54,plain,(
% 4.13/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 4.13/1.01    inference(equality_resolution,[],[f32])).
% 4.13/1.01  
% 4.13/1.01  fof(f1,axiom,(
% 4.13/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f12,plain,(
% 4.13/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.13/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 4.13/1.01  
% 4.13/1.01  fof(f13,plain,(
% 4.13/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 4.13/1.01    inference(ennf_transformation,[],[f12])).
% 4.13/1.01  
% 4.13/1.01  fof(f31,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f13])).
% 4.13/1.01  
% 4.13/1.01  fof(f10,conjecture,(
% 4.13/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f11,negated_conjecture,(
% 4.13/1.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 4.13/1.01    inference(negated_conjecture,[],[f10])).
% 4.13/1.01  
% 4.13/1.01  fof(f17,plain,(
% 4.13/1.01    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 4.13/1.01    inference(ennf_transformation,[],[f11])).
% 4.13/1.01  
% 4.13/1.01  fof(f18,plain,(
% 4.13/1.01    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 4.13/1.01    inference(flattening,[],[f17])).
% 4.13/1.01  
% 4.13/1.01  fof(f29,plain,(
% 4.13/1.01    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) & r1_tarski(sK3,sK4) & v1_relat_1(sK5))),
% 4.13/1.01    introduced(choice_axiom,[])).
% 4.13/1.01  
% 4.13/1.01  fof(f30,plain,(
% 4.13/1.01    k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) & r1_tarski(sK3,sK4) & v1_relat_1(sK5)),
% 4.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f29])).
% 4.13/1.01  
% 4.13/1.01  fof(f48,plain,(
% 4.13/1.01    r1_tarski(sK3,sK4)),
% 4.13/1.01    inference(cnf_transformation,[],[f30])).
% 4.13/1.01  
% 4.13/1.01  fof(f8,axiom,(
% 4.13/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f45,plain,(
% 4.13/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.13/1.01    inference(cnf_transformation,[],[f8])).
% 4.13/1.01  
% 4.13/1.01  fof(f5,axiom,(
% 4.13/1.01    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f41,plain,(
% 4.13/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f5])).
% 4.13/1.01  
% 4.13/1.01  fof(f6,axiom,(
% 4.13/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f42,plain,(
% 4.13/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f6])).
% 4.13/1.01  
% 4.13/1.01  fof(f50,plain,(
% 4.13/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 4.13/1.01    inference(definition_unfolding,[],[f45,f41,f42])).
% 4.13/1.01  
% 4.13/1.01  fof(f9,axiom,(
% 4.13/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f16,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 4.13/1.01    inference(ennf_transformation,[],[f9])).
% 4.13/1.01  
% 4.13/1.01  fof(f46,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f16])).
% 4.13/1.01  
% 4.13/1.01  fof(f51,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) | ~v1_relat_1(X2)) )),
% 4.13/1.01    inference(definition_unfolding,[],[f46,f41])).
% 4.13/1.01  
% 4.13/1.01  fof(f47,plain,(
% 4.13/1.01    v1_relat_1(sK5)),
% 4.13/1.01    inference(cnf_transformation,[],[f30])).
% 4.13/1.01  
% 4.13/1.01  fof(f49,plain,(
% 4.13/1.01    k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5))),
% 4.13/1.01    inference(cnf_transformation,[],[f30])).
% 4.13/1.01  
% 4.13/1.01  cnf(c_8,plain,
% 4.13/1.01      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X0 = X1 ),
% 4.13/1.01      inference(cnf_transformation,[],[f38]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1422,plain,
% 4.13/1.01      ( X0 = X1
% 4.13/1.01      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 4.13/1.01      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9,plain,
% 4.13/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.13/1.01      inference(cnf_transformation,[],[f40]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_5,negated_conjecture,
% 4.13/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 4.13/1.01      inference(cnf_transformation,[],[f53]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1425,plain,
% 4.13/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.13/1.01      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1835,plain,
% 4.13/1.01      ( k4_xboole_0(X0,X1) = X2
% 4.13/1.01      | r2_hidden(sK1(X2,k4_xboole_0(X0,X1)),X1) != iProver_top
% 4.13/1.01      | r2_hidden(sK1(X2,k4_xboole_0(X0,X1)),X2) = iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1422,c_1425]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2491,plain,
% 4.13/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X1
% 4.13/1.01      | r2_hidden(sK1(X1,X0),k1_xboole_0) != iProver_top
% 4.13/1.01      | r2_hidden(sK1(X1,k4_xboole_0(X0,k1_xboole_0)),X1) = iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_9,c_1835]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2513,plain,
% 4.13/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X1
% 4.13/1.01      | r2_hidden(sK1(X1,X0),X1) = iProver_top
% 4.13/1.01      | r2_hidden(sK1(X1,X0),k1_xboole_0) != iProver_top ),
% 4.13/1.01      inference(light_normalisation,[status(thm)],[c_2491,c_9]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2514,plain,
% 4.13/1.01      ( X0 = X1
% 4.13/1.01      | r2_hidden(sK1(X0,X1),X0) = iProver_top
% 4.13/1.01      | r2_hidden(sK1(X0,X1),k1_xboole_0) != iProver_top ),
% 4.13/1.01      inference(demodulation,[status(thm)],[c_2513,c_9]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1585,plain,
% 4.13/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.13/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_9,c_1425]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2741,plain,
% 4.13/1.01      ( X0 = X1 | r2_hidden(sK1(X1,X0),k1_xboole_0) != iProver_top ),
% 4.13/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_2514,c_1585]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2743,plain,
% 4.13/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0,k1_xboole_0),X0) = iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1422,c_2741]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_11,plain,
% 4.13/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1) ),
% 4.13/1.01      inference(cnf_transformation,[],[f43]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1420,plain,
% 4.13/1.01      ( r2_hidden(X0,X1) != iProver_top | r2_hidden(sK2(X1),X1) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_3756,plain,
% 4.13/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_2743,c_1420]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_6,plain,
% 4.13/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 4.13/1.01      inference(cnf_transformation,[],[f54]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1424,plain,
% 4.13/1.01      ( r2_hidden(X0,X1) = iProver_top
% 4.13/1.01      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_3865,plain,
% 4.13/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 4.13/1.01      | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_3756,c_1424]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_0,plain,
% 4.13/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 4.13/1.01      inference(cnf_transformation,[],[f31]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_15,negated_conjecture,
% 4.13/1.01      ( r1_tarski(sK3,sK4) ),
% 4.13/1.01      inference(cnf_transformation,[],[f48]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_167,plain,
% 4.13/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK4 != X2 | sK3 != X1 ),
% 4.13/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_15]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_168,plain,
% 4.13/1.01      ( r2_hidden(X0,sK4) | ~ r2_hidden(X0,sK3) ),
% 4.13/1.01      inference(unflattening,[status(thm)],[c_167]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1418,plain,
% 4.13/1.01      ( r2_hidden(X0,sK4) = iProver_top | r2_hidden(X0,sK3) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_168]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9356,plain,
% 4.13/1.01      ( k4_xboole_0(sK3,X0) = k1_xboole_0
% 4.13/1.01      | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK4) = iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_3865,c_1418]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_3866,plain,
% 4.13/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 4.13/1.01      | r2_hidden(sK2(k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_3756,c_1425]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_10654,plain,
% 4.13/1.01      ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_9356,c_3866]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_12,plain,
% 4.13/1.01      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.13/1.01      inference(cnf_transformation,[],[f50]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_10891,plain,
% 4.13/1.01      ( k1_setfam_1(k1_enumset1(sK3,sK3,sK4)) = k4_xboole_0(sK3,k1_xboole_0) ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_10654,c_12]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_10946,plain,
% 4.13/1.01      ( k1_setfam_1(k1_enumset1(sK3,sK3,sK4)) = sK3 ),
% 4.13/1.01      inference(demodulation,[status(thm)],[c_10891,c_9]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_13,plain,
% 4.13/1.01      ( ~ v1_relat_1(X0)
% 4.13/1.01      | k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
% 4.13/1.01      inference(cnf_transformation,[],[f51]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_16,negated_conjecture,
% 4.13/1.01      ( v1_relat_1(sK5) ),
% 4.13/1.01      inference(cnf_transformation,[],[f47]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_160,plain,
% 4.13/1.01      ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
% 4.13/1.01      | sK5 != X2 ),
% 4.13/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_161,plain,
% 4.13/1.01      ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK5) = k8_relat_1(X0,k8_relat_1(X1,sK5)) ),
% 4.13/1.01      inference(unflattening,[status(thm)],[c_160]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1442,plain,
% 4.13/1.01      ( k8_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),sK5) = k8_relat_1(X0,k8_relat_1(X1,sK5)) ),
% 4.13/1.01      inference(light_normalisation,[status(thm)],[c_161,c_12]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_11273,plain,
% 4.13/1.01      ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) = k8_relat_1(sK3,sK5) ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_10946,c_1442]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_14,negated_conjecture,
% 4.13/1.01      ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
% 4.13/1.01      inference(cnf_transformation,[],[f49]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_11841,plain,
% 4.13/1.01      ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,sK5) ),
% 4.13/1.01      inference(demodulation,[status(thm)],[c_11273,c_14]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_11842,plain,
% 4.13/1.01      ( $false ),
% 4.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_11841]) ).
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.13/1.01  
% 4.13/1.01  ------                               Statistics
% 4.13/1.01  
% 4.13/1.01  ------ Selected
% 4.13/1.01  
% 4.13/1.01  total_time:                             0.464
% 4.13/1.01  
%------------------------------------------------------------------------------
