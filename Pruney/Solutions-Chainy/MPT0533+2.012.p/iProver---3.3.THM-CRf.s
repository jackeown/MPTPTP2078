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
% DateTime   : Thu Dec  3 11:45:41 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 229 expanded)
%              Number of clauses        :   54 (  69 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  332 ( 901 expanded)
%              Number of equality atoms :  117 ( 156 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f31,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f31,f30])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK7))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X3))
          & r1_tarski(sK4,sK5)
          & r1_tarski(sK6,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f22,f34,f33])).

fof(f53,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f46,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK2(X4),sK3(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( v1_relat_1(X0)
      | k4_tarski(X2,X3) != sK1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_580,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_572,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_578,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_582,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1254,plain,
    ( k1_setfam_1(k2_tarski(k8_relat_1(X0,X1),X1)) = k8_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_582])).

cnf(c_4169,plain,
    ( k1_setfam_1(k2_tarski(k8_relat_1(X0,sK7),sK7)) = k8_relat_1(X0,sK7) ),
    inference(superposition,[status(thm)],[c_572,c_1254])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_586,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4360,plain,
    ( r2_hidden(X0,k8_relat_1(X1,sK7)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_4169,c_586])).

cnf(c_4726,plain,
    ( r2_hidden(sK1(k8_relat_1(X0,sK7)),sK7) = iProver_top
    | v1_relat_1(k8_relat_1(X0,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_580,c_4360])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_579,plain,
    ( k4_tarski(sK2(X0),sK3(X0)) = X0
    | r2_hidden(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7184,plain,
    ( k4_tarski(sK2(sK1(k8_relat_1(X0,sK7))),sK3(sK1(k8_relat_1(X0,sK7)))) = sK1(k8_relat_1(X0,sK7))
    | v1_relat_1(k8_relat_1(X0,sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4726,c_579])).

cnf(c_21,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( v1_relat_1(X0)
    | k4_tarski(X1,X2) != sK1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1280,plain,
    ( v1_relat_1(k8_relat_1(X0,sK7))
    | k4_tarski(X1,X2) != sK1(k8_relat_1(X0,sK7)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_20904,plain,
    ( v1_relat_1(k8_relat_1(X0,sK7))
    | k4_tarski(sK2(sK1(k8_relat_1(X0,sK7))),sK3(sK1(k8_relat_1(X0,sK7)))) != sK1(k8_relat_1(X0,sK7)) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_20909,plain,
    ( k4_tarski(sK2(sK1(k8_relat_1(X0,sK7))),sK3(sK1(k8_relat_1(X0,sK7)))) != sK1(k8_relat_1(X0,sK7))
    | v1_relat_1(k8_relat_1(X0,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20904])).

cnf(c_21347,plain,
    ( v1_relat_1(k8_relat_1(X0,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7184,c_21,c_20909])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_574,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_577,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1773,plain,
    ( k8_relat_1(sK5,k8_relat_1(sK4,X0)) = k8_relat_1(sK4,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_577])).

cnf(c_2533,plain,
    ( k8_relat_1(sK5,k8_relat_1(sK4,sK7)) = k8_relat_1(sK4,sK7) ),
    inference(superposition,[status(thm)],[c_572,c_1773])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_576,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2541,plain,
    ( r1_tarski(k8_relat_1(sK4,sK7),X0) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK7),k8_relat_1(sK5,X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_576])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_573,plain,
    ( r1_tarski(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_583,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1076,plain,
    ( k2_xboole_0(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) = k8_relat_1(X0,X2)
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_576,c_583])).

cnf(c_3007,plain,
    ( k2_xboole_0(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7)) = k8_relat_1(X0,sK7)
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_1076])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_762,plain,
    ( r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7))
    | ~ r1_tarski(sK6,sK7)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_814,plain,
    ( ~ r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7))
    | k2_xboole_0(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7)) = k8_relat_1(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3678,plain,
    ( k2_xboole_0(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7)) = k8_relat_1(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3007,c_19,c_18,c_17,c_762,c_814])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_584,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3682,plain,
    ( r1_tarski(k8_relat_1(X0,sK7),X1) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK6),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3678,c_584])).

cnf(c_5407,plain,
    ( r1_tarski(k8_relat_1(sK4,sK7),X0) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_3682])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_575,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19677,plain,
    ( r1_tarski(k8_relat_1(sK4,sK7),sK7) != iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5407,c_575])).

cnf(c_19723,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK7),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19677,c_21])).

cnf(c_19724,plain,
    ( r1_tarski(k8_relat_1(sK4,sK7),sK7) != iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_19723])).

cnf(c_19729,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_19724])).

cnf(c_19902,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19729,c_21])).

cnf(c_21371,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_21347,c_19902])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:59:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.05/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.05/1.49  
% 7.05/1.49  ------  iProver source info
% 7.05/1.49  
% 7.05/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.05/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.05/1.49  git: non_committed_changes: false
% 7.05/1.49  git: last_make_outside_of_git: false
% 7.05/1.49  
% 7.05/1.49  ------ 
% 7.05/1.49  
% 7.05/1.49  ------ Input Options
% 7.05/1.49  
% 7.05/1.49  --out_options                           all
% 7.05/1.49  --tptp_safe_out                         true
% 7.05/1.49  --problem_path                          ""
% 7.05/1.49  --include_path                          ""
% 7.05/1.49  --clausifier                            res/vclausify_rel
% 7.05/1.49  --clausifier_options                    --mode clausify
% 7.05/1.49  --stdin                                 false
% 7.05/1.49  --stats_out                             all
% 7.05/1.49  
% 7.05/1.49  ------ General Options
% 7.05/1.49  
% 7.05/1.49  --fof                                   false
% 7.05/1.49  --time_out_real                         305.
% 7.05/1.49  --time_out_virtual                      -1.
% 7.05/1.49  --symbol_type_check                     false
% 7.05/1.49  --clausify_out                          false
% 7.05/1.49  --sig_cnt_out                           false
% 7.05/1.49  --trig_cnt_out                          false
% 7.05/1.49  --trig_cnt_out_tolerance                1.
% 7.05/1.49  --trig_cnt_out_sk_spl                   false
% 7.05/1.49  --abstr_cl_out                          false
% 7.05/1.49  
% 7.05/1.49  ------ Global Options
% 7.05/1.49  
% 7.05/1.49  --schedule                              default
% 7.05/1.49  --add_important_lit                     false
% 7.05/1.49  --prop_solver_per_cl                    1000
% 7.05/1.49  --min_unsat_core                        false
% 7.05/1.49  --soft_assumptions                      false
% 7.05/1.49  --soft_lemma_size                       3
% 7.05/1.49  --prop_impl_unit_size                   0
% 7.05/1.49  --prop_impl_unit                        []
% 7.05/1.49  --share_sel_clauses                     true
% 7.05/1.49  --reset_solvers                         false
% 7.05/1.49  --bc_imp_inh                            [conj_cone]
% 7.05/1.49  --conj_cone_tolerance                   3.
% 7.05/1.49  --extra_neg_conj                        none
% 7.05/1.49  --large_theory_mode                     true
% 7.05/1.49  --prolific_symb_bound                   200
% 7.05/1.49  --lt_threshold                          2000
% 7.05/1.49  --clause_weak_htbl                      true
% 7.05/1.49  --gc_record_bc_elim                     false
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing Options
% 7.05/1.49  
% 7.05/1.49  --preprocessing_flag                    true
% 7.05/1.49  --time_out_prep_mult                    0.1
% 7.05/1.49  --splitting_mode                        input
% 7.05/1.49  --splitting_grd                         true
% 7.05/1.49  --splitting_cvd                         false
% 7.05/1.49  --splitting_cvd_svl                     false
% 7.05/1.49  --splitting_nvd                         32
% 7.05/1.49  --sub_typing                            true
% 7.05/1.49  --prep_gs_sim                           true
% 7.05/1.49  --prep_unflatten                        true
% 7.05/1.49  --prep_res_sim                          true
% 7.05/1.49  --prep_upred                            true
% 7.05/1.49  --prep_sem_filter                       exhaustive
% 7.05/1.49  --prep_sem_filter_out                   false
% 7.05/1.49  --pred_elim                             true
% 7.05/1.49  --res_sim_input                         true
% 7.05/1.49  --eq_ax_congr_red                       true
% 7.05/1.49  --pure_diseq_elim                       true
% 7.05/1.49  --brand_transform                       false
% 7.05/1.49  --non_eq_to_eq                          false
% 7.05/1.49  --prep_def_merge                        true
% 7.05/1.49  --prep_def_merge_prop_impl              false
% 7.05/1.49  --prep_def_merge_mbd                    true
% 7.05/1.49  --prep_def_merge_tr_red                 false
% 7.05/1.49  --prep_def_merge_tr_cl                  false
% 7.05/1.49  --smt_preprocessing                     true
% 7.05/1.49  --smt_ac_axioms                         fast
% 7.05/1.49  --preprocessed_out                      false
% 7.05/1.49  --preprocessed_stats                    false
% 7.05/1.49  
% 7.05/1.49  ------ Abstraction refinement Options
% 7.05/1.49  
% 7.05/1.49  --abstr_ref                             []
% 7.05/1.49  --abstr_ref_prep                        false
% 7.05/1.49  --abstr_ref_until_sat                   false
% 7.05/1.49  --abstr_ref_sig_restrict                funpre
% 7.05/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.49  --abstr_ref_under                       []
% 7.05/1.49  
% 7.05/1.49  ------ SAT Options
% 7.05/1.49  
% 7.05/1.49  --sat_mode                              false
% 7.05/1.49  --sat_fm_restart_options                ""
% 7.05/1.49  --sat_gr_def                            false
% 7.05/1.49  --sat_epr_types                         true
% 7.05/1.49  --sat_non_cyclic_types                  false
% 7.05/1.49  --sat_finite_models                     false
% 7.05/1.49  --sat_fm_lemmas                         false
% 7.05/1.49  --sat_fm_prep                           false
% 7.05/1.49  --sat_fm_uc_incr                        true
% 7.05/1.49  --sat_out_model                         small
% 7.05/1.49  --sat_out_clauses                       false
% 7.05/1.49  
% 7.05/1.49  ------ QBF Options
% 7.05/1.49  
% 7.05/1.49  --qbf_mode                              false
% 7.05/1.49  --qbf_elim_univ                         false
% 7.05/1.49  --qbf_dom_inst                          none
% 7.05/1.49  --qbf_dom_pre_inst                      false
% 7.05/1.49  --qbf_sk_in                             false
% 7.05/1.49  --qbf_pred_elim                         true
% 7.05/1.49  --qbf_split                             512
% 7.05/1.49  
% 7.05/1.49  ------ BMC1 Options
% 7.05/1.49  
% 7.05/1.49  --bmc1_incremental                      false
% 7.05/1.49  --bmc1_axioms                           reachable_all
% 7.05/1.49  --bmc1_min_bound                        0
% 7.05/1.49  --bmc1_max_bound                        -1
% 7.05/1.49  --bmc1_max_bound_default                -1
% 7.05/1.49  --bmc1_symbol_reachability              true
% 7.05/1.49  --bmc1_property_lemmas                  false
% 7.05/1.49  --bmc1_k_induction                      false
% 7.05/1.49  --bmc1_non_equiv_states                 false
% 7.05/1.49  --bmc1_deadlock                         false
% 7.05/1.49  --bmc1_ucm                              false
% 7.05/1.49  --bmc1_add_unsat_core                   none
% 7.05/1.49  --bmc1_unsat_core_children              false
% 7.05/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.49  --bmc1_out_stat                         full
% 7.05/1.49  --bmc1_ground_init                      false
% 7.05/1.49  --bmc1_pre_inst_next_state              false
% 7.05/1.49  --bmc1_pre_inst_state                   false
% 7.05/1.49  --bmc1_pre_inst_reach_state             false
% 7.05/1.49  --bmc1_out_unsat_core                   false
% 7.05/1.49  --bmc1_aig_witness_out                  false
% 7.05/1.49  --bmc1_verbose                          false
% 7.05/1.49  --bmc1_dump_clauses_tptp                false
% 7.05/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.49  --bmc1_dump_file                        -
% 7.05/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.49  --bmc1_ucm_extend_mode                  1
% 7.05/1.49  --bmc1_ucm_init_mode                    2
% 7.05/1.49  --bmc1_ucm_cone_mode                    none
% 7.05/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.49  --bmc1_ucm_relax_model                  4
% 7.05/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.49  --bmc1_ucm_layered_model                none
% 7.05/1.49  --bmc1_ucm_max_lemma_size               10
% 7.05/1.49  
% 7.05/1.49  ------ AIG Options
% 7.05/1.49  
% 7.05/1.49  --aig_mode                              false
% 7.05/1.49  
% 7.05/1.49  ------ Instantiation Options
% 7.05/1.49  
% 7.05/1.49  --instantiation_flag                    true
% 7.05/1.49  --inst_sos_flag                         false
% 7.05/1.49  --inst_sos_phase                        true
% 7.05/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel_side                     num_symb
% 7.05/1.49  --inst_solver_per_active                1400
% 7.05/1.49  --inst_solver_calls_frac                1.
% 7.05/1.49  --inst_passive_queue_type               priority_queues
% 7.05/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.49  --inst_passive_queues_freq              [25;2]
% 7.05/1.49  --inst_dismatching                      true
% 7.05/1.49  --inst_eager_unprocessed_to_passive     true
% 7.05/1.49  --inst_prop_sim_given                   true
% 7.05/1.49  --inst_prop_sim_new                     false
% 7.05/1.49  --inst_subs_new                         false
% 7.05/1.49  --inst_eq_res_simp                      false
% 7.05/1.49  --inst_subs_given                       false
% 7.05/1.49  --inst_orphan_elimination               true
% 7.05/1.49  --inst_learning_loop_flag               true
% 7.05/1.49  --inst_learning_start                   3000
% 7.05/1.49  --inst_learning_factor                  2
% 7.05/1.49  --inst_start_prop_sim_after_learn       3
% 7.05/1.49  --inst_sel_renew                        solver
% 7.05/1.49  --inst_lit_activity_flag                true
% 7.05/1.49  --inst_restr_to_given                   false
% 7.05/1.49  --inst_activity_threshold               500
% 7.05/1.49  --inst_out_proof                        true
% 7.05/1.49  
% 7.05/1.49  ------ Resolution Options
% 7.05/1.49  
% 7.05/1.49  --resolution_flag                       true
% 7.05/1.49  --res_lit_sel                           adaptive
% 7.05/1.49  --res_lit_sel_side                      none
% 7.05/1.49  --res_ordering                          kbo
% 7.05/1.49  --res_to_prop_solver                    active
% 7.05/1.49  --res_prop_simpl_new                    false
% 7.05/1.49  --res_prop_simpl_given                  true
% 7.05/1.49  --res_passive_queue_type                priority_queues
% 7.05/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.49  --res_passive_queues_freq               [15;5]
% 7.05/1.49  --res_forward_subs                      full
% 7.05/1.49  --res_backward_subs                     full
% 7.05/1.49  --res_forward_subs_resolution           true
% 7.05/1.49  --res_backward_subs_resolution          true
% 7.05/1.49  --res_orphan_elimination                true
% 7.05/1.49  --res_time_limit                        2.
% 7.05/1.49  --res_out_proof                         true
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Options
% 7.05/1.49  
% 7.05/1.49  --superposition_flag                    true
% 7.05/1.49  --sup_passive_queue_type                priority_queues
% 7.05/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.49  --demod_completeness_check              fast
% 7.05/1.49  --demod_use_ground                      true
% 7.05/1.49  --sup_to_prop_solver                    passive
% 7.05/1.49  --sup_prop_simpl_new                    true
% 7.05/1.49  --sup_prop_simpl_given                  true
% 7.05/1.49  --sup_fun_splitting                     false
% 7.05/1.49  --sup_smt_interval                      50000
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Simplification Setup
% 7.05/1.49  
% 7.05/1.49  --sup_indices_passive                   []
% 7.05/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_full_bw                           [BwDemod]
% 7.05/1.49  --sup_immed_triv                        [TrivRules]
% 7.05/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_immed_bw_main                     []
% 7.05/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  
% 7.05/1.49  ------ Combination Options
% 7.05/1.49  
% 7.05/1.49  --comb_res_mult                         3
% 7.05/1.49  --comb_sup_mult                         2
% 7.05/1.49  --comb_inst_mult                        10
% 7.05/1.49  
% 7.05/1.49  ------ Debug Options
% 7.05/1.49  
% 7.05/1.49  --dbg_backtrace                         false
% 7.05/1.49  --dbg_dump_prop_clauses                 false
% 7.05/1.49  --dbg_dump_prop_clauses_file            -
% 7.05/1.49  --dbg_out_stat                          false
% 7.05/1.49  ------ Parsing...
% 7.05/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.05/1.49  ------ Proving...
% 7.05/1.49  ------ Problem Properties 
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  clauses                                 20
% 7.05/1.49  conjectures                             5
% 7.05/1.49  EPR                                     4
% 7.05/1.49  Horn                                    17
% 7.05/1.49  unary                                   5
% 7.05/1.49  binary                                  8
% 7.05/1.49  lits                                    44
% 7.05/1.49  lits eq                                 8
% 7.05/1.49  fd_pure                                 0
% 7.05/1.49  fd_pseudo                               0
% 7.05/1.49  fd_cond                                 0
% 7.05/1.49  fd_pseudo_cond                          3
% 7.05/1.49  AC symbols                              0
% 7.05/1.49  
% 7.05/1.49  ------ Schedule dynamic 5 is on 
% 7.05/1.49  
% 7.05/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  ------ 
% 7.05/1.49  Current options:
% 7.05/1.49  ------ 
% 7.05/1.49  
% 7.05/1.49  ------ Input Options
% 7.05/1.49  
% 7.05/1.49  --out_options                           all
% 7.05/1.49  --tptp_safe_out                         true
% 7.05/1.49  --problem_path                          ""
% 7.05/1.49  --include_path                          ""
% 7.05/1.49  --clausifier                            res/vclausify_rel
% 7.05/1.49  --clausifier_options                    --mode clausify
% 7.05/1.49  --stdin                                 false
% 7.05/1.49  --stats_out                             all
% 7.05/1.49  
% 7.05/1.49  ------ General Options
% 7.05/1.49  
% 7.05/1.49  --fof                                   false
% 7.05/1.49  --time_out_real                         305.
% 7.05/1.49  --time_out_virtual                      -1.
% 7.05/1.49  --symbol_type_check                     false
% 7.05/1.49  --clausify_out                          false
% 7.05/1.49  --sig_cnt_out                           false
% 7.05/1.49  --trig_cnt_out                          false
% 7.05/1.49  --trig_cnt_out_tolerance                1.
% 7.05/1.49  --trig_cnt_out_sk_spl                   false
% 7.05/1.49  --abstr_cl_out                          false
% 7.05/1.49  
% 7.05/1.49  ------ Global Options
% 7.05/1.49  
% 7.05/1.49  --schedule                              default
% 7.05/1.49  --add_important_lit                     false
% 7.05/1.49  --prop_solver_per_cl                    1000
% 7.05/1.49  --min_unsat_core                        false
% 7.05/1.49  --soft_assumptions                      false
% 7.05/1.49  --soft_lemma_size                       3
% 7.05/1.49  --prop_impl_unit_size                   0
% 7.05/1.49  --prop_impl_unit                        []
% 7.05/1.49  --share_sel_clauses                     true
% 7.05/1.49  --reset_solvers                         false
% 7.05/1.49  --bc_imp_inh                            [conj_cone]
% 7.05/1.49  --conj_cone_tolerance                   3.
% 7.05/1.49  --extra_neg_conj                        none
% 7.05/1.49  --large_theory_mode                     true
% 7.05/1.49  --prolific_symb_bound                   200
% 7.05/1.49  --lt_threshold                          2000
% 7.05/1.49  --clause_weak_htbl                      true
% 7.05/1.49  --gc_record_bc_elim                     false
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing Options
% 7.05/1.49  
% 7.05/1.49  --preprocessing_flag                    true
% 7.05/1.49  --time_out_prep_mult                    0.1
% 7.05/1.49  --splitting_mode                        input
% 7.05/1.49  --splitting_grd                         true
% 7.05/1.49  --splitting_cvd                         false
% 7.05/1.49  --splitting_cvd_svl                     false
% 7.05/1.49  --splitting_nvd                         32
% 7.05/1.49  --sub_typing                            true
% 7.05/1.49  --prep_gs_sim                           true
% 7.05/1.49  --prep_unflatten                        true
% 7.05/1.49  --prep_res_sim                          true
% 7.05/1.49  --prep_upred                            true
% 7.05/1.49  --prep_sem_filter                       exhaustive
% 7.05/1.49  --prep_sem_filter_out                   false
% 7.05/1.49  --pred_elim                             true
% 7.05/1.49  --res_sim_input                         true
% 7.05/1.49  --eq_ax_congr_red                       true
% 7.05/1.49  --pure_diseq_elim                       true
% 7.05/1.49  --brand_transform                       false
% 7.05/1.49  --non_eq_to_eq                          false
% 7.05/1.49  --prep_def_merge                        true
% 7.05/1.49  --prep_def_merge_prop_impl              false
% 7.05/1.49  --prep_def_merge_mbd                    true
% 7.05/1.49  --prep_def_merge_tr_red                 false
% 7.05/1.49  --prep_def_merge_tr_cl                  false
% 7.05/1.49  --smt_preprocessing                     true
% 7.05/1.49  --smt_ac_axioms                         fast
% 7.05/1.49  --preprocessed_out                      false
% 7.05/1.49  --preprocessed_stats                    false
% 7.05/1.49  
% 7.05/1.49  ------ Abstraction refinement Options
% 7.05/1.49  
% 7.05/1.49  --abstr_ref                             []
% 7.05/1.49  --abstr_ref_prep                        false
% 7.05/1.49  --abstr_ref_until_sat                   false
% 7.05/1.49  --abstr_ref_sig_restrict                funpre
% 7.05/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.49  --abstr_ref_under                       []
% 7.05/1.49  
% 7.05/1.49  ------ SAT Options
% 7.05/1.49  
% 7.05/1.49  --sat_mode                              false
% 7.05/1.49  --sat_fm_restart_options                ""
% 7.05/1.49  --sat_gr_def                            false
% 7.05/1.49  --sat_epr_types                         true
% 7.05/1.49  --sat_non_cyclic_types                  false
% 7.05/1.49  --sat_finite_models                     false
% 7.05/1.49  --sat_fm_lemmas                         false
% 7.05/1.49  --sat_fm_prep                           false
% 7.05/1.49  --sat_fm_uc_incr                        true
% 7.05/1.49  --sat_out_model                         small
% 7.05/1.49  --sat_out_clauses                       false
% 7.05/1.49  
% 7.05/1.49  ------ QBF Options
% 7.05/1.49  
% 7.05/1.49  --qbf_mode                              false
% 7.05/1.49  --qbf_elim_univ                         false
% 7.05/1.49  --qbf_dom_inst                          none
% 7.05/1.49  --qbf_dom_pre_inst                      false
% 7.05/1.49  --qbf_sk_in                             false
% 7.05/1.49  --qbf_pred_elim                         true
% 7.05/1.49  --qbf_split                             512
% 7.05/1.49  
% 7.05/1.49  ------ BMC1 Options
% 7.05/1.49  
% 7.05/1.49  --bmc1_incremental                      false
% 7.05/1.49  --bmc1_axioms                           reachable_all
% 7.05/1.49  --bmc1_min_bound                        0
% 7.05/1.49  --bmc1_max_bound                        -1
% 7.05/1.49  --bmc1_max_bound_default                -1
% 7.05/1.49  --bmc1_symbol_reachability              true
% 7.05/1.49  --bmc1_property_lemmas                  false
% 7.05/1.49  --bmc1_k_induction                      false
% 7.05/1.49  --bmc1_non_equiv_states                 false
% 7.05/1.49  --bmc1_deadlock                         false
% 7.05/1.49  --bmc1_ucm                              false
% 7.05/1.49  --bmc1_add_unsat_core                   none
% 7.05/1.49  --bmc1_unsat_core_children              false
% 7.05/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.49  --bmc1_out_stat                         full
% 7.05/1.49  --bmc1_ground_init                      false
% 7.05/1.49  --bmc1_pre_inst_next_state              false
% 7.05/1.49  --bmc1_pre_inst_state                   false
% 7.05/1.49  --bmc1_pre_inst_reach_state             false
% 7.05/1.49  --bmc1_out_unsat_core                   false
% 7.05/1.49  --bmc1_aig_witness_out                  false
% 7.05/1.49  --bmc1_verbose                          false
% 7.05/1.49  --bmc1_dump_clauses_tptp                false
% 7.05/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.49  --bmc1_dump_file                        -
% 7.05/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.49  --bmc1_ucm_extend_mode                  1
% 7.05/1.49  --bmc1_ucm_init_mode                    2
% 7.05/1.49  --bmc1_ucm_cone_mode                    none
% 7.05/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.49  --bmc1_ucm_relax_model                  4
% 7.05/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.49  --bmc1_ucm_layered_model                none
% 7.05/1.49  --bmc1_ucm_max_lemma_size               10
% 7.05/1.49  
% 7.05/1.49  ------ AIG Options
% 7.05/1.49  
% 7.05/1.49  --aig_mode                              false
% 7.05/1.49  
% 7.05/1.49  ------ Instantiation Options
% 7.05/1.49  
% 7.05/1.49  --instantiation_flag                    true
% 7.05/1.49  --inst_sos_flag                         false
% 7.05/1.49  --inst_sos_phase                        true
% 7.05/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel_side                     none
% 7.05/1.49  --inst_solver_per_active                1400
% 7.05/1.49  --inst_solver_calls_frac                1.
% 7.05/1.49  --inst_passive_queue_type               priority_queues
% 7.05/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.49  --inst_passive_queues_freq              [25;2]
% 7.05/1.49  --inst_dismatching                      true
% 7.05/1.49  --inst_eager_unprocessed_to_passive     true
% 7.05/1.49  --inst_prop_sim_given                   true
% 7.05/1.49  --inst_prop_sim_new                     false
% 7.05/1.49  --inst_subs_new                         false
% 7.05/1.49  --inst_eq_res_simp                      false
% 7.05/1.49  --inst_subs_given                       false
% 7.05/1.49  --inst_orphan_elimination               true
% 7.05/1.49  --inst_learning_loop_flag               true
% 7.05/1.49  --inst_learning_start                   3000
% 7.05/1.49  --inst_learning_factor                  2
% 7.05/1.49  --inst_start_prop_sim_after_learn       3
% 7.05/1.49  --inst_sel_renew                        solver
% 7.05/1.49  --inst_lit_activity_flag                true
% 7.05/1.49  --inst_restr_to_given                   false
% 7.05/1.49  --inst_activity_threshold               500
% 7.05/1.49  --inst_out_proof                        true
% 7.05/1.49  
% 7.05/1.49  ------ Resolution Options
% 7.05/1.49  
% 7.05/1.49  --resolution_flag                       false
% 7.05/1.49  --res_lit_sel                           adaptive
% 7.05/1.49  --res_lit_sel_side                      none
% 7.05/1.49  --res_ordering                          kbo
% 7.05/1.49  --res_to_prop_solver                    active
% 7.05/1.49  --res_prop_simpl_new                    false
% 7.05/1.49  --res_prop_simpl_given                  true
% 7.05/1.49  --res_passive_queue_type                priority_queues
% 7.05/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.49  --res_passive_queues_freq               [15;5]
% 7.05/1.49  --res_forward_subs                      full
% 7.05/1.49  --res_backward_subs                     full
% 7.05/1.49  --res_forward_subs_resolution           true
% 7.05/1.49  --res_backward_subs_resolution          true
% 7.05/1.49  --res_orphan_elimination                true
% 7.05/1.49  --res_time_limit                        2.
% 7.05/1.49  --res_out_proof                         true
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Options
% 7.05/1.49  
% 7.05/1.49  --superposition_flag                    true
% 7.05/1.49  --sup_passive_queue_type                priority_queues
% 7.05/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.49  --demod_completeness_check              fast
% 7.05/1.49  --demod_use_ground                      true
% 7.05/1.49  --sup_to_prop_solver                    passive
% 7.05/1.49  --sup_prop_simpl_new                    true
% 7.05/1.49  --sup_prop_simpl_given                  true
% 7.05/1.49  --sup_fun_splitting                     false
% 7.05/1.49  --sup_smt_interval                      50000
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Simplification Setup
% 7.05/1.49  
% 7.05/1.49  --sup_indices_passive                   []
% 7.05/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_full_bw                           [BwDemod]
% 7.05/1.49  --sup_immed_triv                        [TrivRules]
% 7.05/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_immed_bw_main                     []
% 7.05/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  
% 7.05/1.49  ------ Combination Options
% 7.05/1.49  
% 7.05/1.49  --comb_res_mult                         3
% 7.05/1.49  --comb_sup_mult                         2
% 7.05/1.49  --comb_inst_mult                        10
% 7.05/1.49  
% 7.05/1.49  ------ Debug Options
% 7.05/1.49  
% 7.05/1.49  --dbg_backtrace                         false
% 7.05/1.49  --dbg_dump_prop_clauses                 false
% 7.05/1.49  --dbg_dump_prop_clauses_file            -
% 7.05/1.49  --dbg_out_stat                          false
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  ------ Proving...
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  % SZS status Theorem for theBenchmark.p
% 7.05/1.49  
% 7.05/1.49   Resolution empty clause
% 7.05/1.49  
% 7.05/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  fof(f6,axiom,(
% 7.05/1.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f15,plain,(
% 7.05/1.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f6])).
% 7.05/1.49  
% 7.05/1.49  fof(f28,plain,(
% 7.05/1.49    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 7.05/1.49    inference(nnf_transformation,[],[f15])).
% 7.05/1.49  
% 7.05/1.49  fof(f29,plain,(
% 7.05/1.49    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 7.05/1.49    inference(rectify,[],[f28])).
% 7.05/1.49  
% 7.05/1.49  fof(f31,plain,(
% 7.05/1.49    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f30,plain,(
% 7.05/1.49    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f32,plain,(
% 7.05/1.49    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 7.05/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f31,f30])).
% 7.05/1.49  
% 7.05/1.49  fof(f47,plain,(
% 7.05/1.49    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f32])).
% 7.05/1.49  
% 7.05/1.49  fof(f10,conjecture,(
% 7.05/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f11,negated_conjecture,(
% 7.05/1.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 7.05/1.49    inference(negated_conjecture,[],[f10])).
% 7.05/1.49  
% 7.05/1.49  fof(f21,plain,(
% 7.05/1.49    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 7.05/1.49    inference(ennf_transformation,[],[f11])).
% 7.05/1.49  
% 7.05/1.49  fof(f22,plain,(
% 7.05/1.49    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 7.05/1.49    inference(flattening,[],[f21])).
% 7.05/1.49  
% 7.05/1.49  fof(f34,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK7)) & r1_tarski(X0,X1) & r1_tarski(X2,sK7) & v1_relat_1(sK7))) )),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f33,plain,(
% 7.05/1.49    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X3)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,X3) & v1_relat_1(X3)) & v1_relat_1(sK6))),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f35,plain,(
% 7.05/1.49    (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,sK7) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 7.05/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f22,f34,f33])).
% 7.05/1.49  
% 7.05/1.49  fof(f53,plain,(
% 7.05/1.49    v1_relat_1(sK7)),
% 7.05/1.49    inference(cnf_transformation,[],[f35])).
% 7.05/1.49  
% 7.05/1.49  fof(f7,axiom,(
% 7.05/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f16,plain,(
% 7.05/1.49    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 7.05/1.49    inference(ennf_transformation,[],[f7])).
% 7.05/1.49  
% 7.05/1.49  fof(f49,plain,(
% 7.05/1.49    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f16])).
% 7.05/1.49  
% 7.05/1.49  fof(f4,axiom,(
% 7.05/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f14,plain,(
% 7.05/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.05/1.49    inference(ennf_transformation,[],[f4])).
% 7.05/1.49  
% 7.05/1.49  fof(f44,plain,(
% 7.05/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f14])).
% 7.05/1.49  
% 7.05/1.49  fof(f5,axiom,(
% 7.05/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f45,plain,(
% 7.05/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.05/1.49    inference(cnf_transformation,[],[f5])).
% 7.05/1.49  
% 7.05/1.49  fof(f63,plain,(
% 7.05/1.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.05/1.49    inference(definition_unfolding,[],[f44,f45])).
% 7.05/1.49  
% 7.05/1.49  fof(f1,axiom,(
% 7.05/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f23,plain,(
% 7.05/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.05/1.49    inference(nnf_transformation,[],[f1])).
% 7.05/1.49  
% 7.05/1.49  fof(f24,plain,(
% 7.05/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.05/1.49    inference(flattening,[],[f23])).
% 7.05/1.49  
% 7.05/1.49  fof(f25,plain,(
% 7.05/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.05/1.49    inference(rectify,[],[f24])).
% 7.05/1.49  
% 7.05/1.49  fof(f26,plain,(
% 7.05/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f27,plain,(
% 7.05/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.05/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 7.05/1.49  
% 7.05/1.49  fof(f37,plain,(
% 7.05/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.05/1.49    inference(cnf_transformation,[],[f27])).
% 7.05/1.49  
% 7.05/1.49  fof(f61,plain,(
% 7.05/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 7.05/1.49    inference(definition_unfolding,[],[f37,f45])).
% 7.05/1.49  
% 7.05/1.49  fof(f65,plain,(
% 7.05/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.05/1.49    inference(equality_resolution,[],[f61])).
% 7.05/1.49  
% 7.05/1.49  fof(f46,plain,(
% 7.05/1.49    ( ! [X4,X0] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f32])).
% 7.05/1.49  
% 7.05/1.49  fof(f48,plain,(
% 7.05/1.49    ( ! [X2,X0,X3] : (v1_relat_1(X0) | k4_tarski(X2,X3) != sK1(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f32])).
% 7.05/1.49  
% 7.05/1.49  fof(f55,plain,(
% 7.05/1.49    r1_tarski(sK4,sK5)),
% 7.05/1.49    inference(cnf_transformation,[],[f35])).
% 7.05/1.49  
% 7.05/1.49  fof(f8,axiom,(
% 7.05/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f17,plain,(
% 7.05/1.49    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 7.05/1.49    inference(ennf_transformation,[],[f8])).
% 7.05/1.49  
% 7.05/1.49  fof(f18,plain,(
% 7.05/1.49    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 7.05/1.49    inference(flattening,[],[f17])).
% 7.05/1.49  
% 7.05/1.49  fof(f50,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f18])).
% 7.05/1.49  
% 7.05/1.49  fof(f9,axiom,(
% 7.05/1.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f19,plain,(
% 7.05/1.49    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 7.05/1.49    inference(ennf_transformation,[],[f9])).
% 7.05/1.49  
% 7.05/1.49  fof(f20,plain,(
% 7.05/1.49    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 7.05/1.49    inference(flattening,[],[f19])).
% 7.05/1.49  
% 7.05/1.49  fof(f51,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f20])).
% 7.05/1.49  
% 7.05/1.49  fof(f54,plain,(
% 7.05/1.49    r1_tarski(sK6,sK7)),
% 7.05/1.49    inference(cnf_transformation,[],[f35])).
% 7.05/1.49  
% 7.05/1.49  fof(f3,axiom,(
% 7.05/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f13,plain,(
% 7.05/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.05/1.49    inference(ennf_transformation,[],[f3])).
% 7.05/1.49  
% 7.05/1.49  fof(f43,plain,(
% 7.05/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f13])).
% 7.05/1.49  
% 7.05/1.49  fof(f52,plain,(
% 7.05/1.49    v1_relat_1(sK6)),
% 7.05/1.49    inference(cnf_transformation,[],[f35])).
% 7.05/1.49  
% 7.05/1.49  fof(f2,axiom,(
% 7.05/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.05/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f12,plain,(
% 7.05/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.05/1.49    inference(ennf_transformation,[],[f2])).
% 7.05/1.49  
% 7.05/1.49  fof(f42,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f12])).
% 7.05/1.49  
% 7.05/1.49  fof(f56,plain,(
% 7.05/1.49    ~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),
% 7.05/1.49    inference(cnf_transformation,[],[f35])).
% 7.05/1.49  
% 7.05/1.49  cnf(c_10,plain,
% 7.05/1.49      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_580,plain,
% 7.05/1.49      ( r2_hidden(sK1(X0),X0) = iProver_top | v1_relat_1(X0) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_18,negated_conjecture,
% 7.05/1.49      ( v1_relat_1(sK7) ),
% 7.05/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_572,plain,
% 7.05/1.49      ( v1_relat_1(sK7) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_12,plain,
% 7.05/1.49      ( r1_tarski(k8_relat_1(X0,X1),X1) | ~ v1_relat_1(X1) ),
% 7.05/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_578,plain,
% 7.05/1.49      ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
% 7.05/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_8,plain,
% 7.05/1.49      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 7.05/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_582,plain,
% 7.05/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1254,plain,
% 7.05/1.49      ( k1_setfam_1(k2_tarski(k8_relat_1(X0,X1),X1)) = k8_relat_1(X0,X1)
% 7.05/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_578,c_582]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4169,plain,
% 7.05/1.49      ( k1_setfam_1(k2_tarski(k8_relat_1(X0,sK7),sK7)) = k8_relat_1(X0,sK7) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_572,c_1254]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4,plain,
% 7.05/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 7.05/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_586,plain,
% 7.05/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.05/1.49      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4360,plain,
% 7.05/1.49      ( r2_hidden(X0,k8_relat_1(X1,sK7)) != iProver_top
% 7.05/1.49      | r2_hidden(X0,sK7) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_4169,c_586]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4726,plain,
% 7.05/1.49      ( r2_hidden(sK1(k8_relat_1(X0,sK7)),sK7) = iProver_top
% 7.05/1.49      | v1_relat_1(k8_relat_1(X0,sK7)) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_580,c_4360]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_11,plain,
% 7.05/1.49      ( ~ r2_hidden(X0,X1)
% 7.05/1.49      | ~ v1_relat_1(X1)
% 7.05/1.49      | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
% 7.05/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_579,plain,
% 7.05/1.49      ( k4_tarski(sK2(X0),sK3(X0)) = X0
% 7.05/1.49      | r2_hidden(X0,X1) != iProver_top
% 7.05/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_7184,plain,
% 7.05/1.49      ( k4_tarski(sK2(sK1(k8_relat_1(X0,sK7))),sK3(sK1(k8_relat_1(X0,sK7)))) = sK1(k8_relat_1(X0,sK7))
% 7.05/1.49      | v1_relat_1(k8_relat_1(X0,sK7)) = iProver_top
% 7.05/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_4726,c_579]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_21,plain,
% 7.05/1.49      ( v1_relat_1(sK7) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_9,plain,
% 7.05/1.49      ( v1_relat_1(X0) | k4_tarski(X1,X2) != sK1(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1280,plain,
% 7.05/1.49      ( v1_relat_1(k8_relat_1(X0,sK7))
% 7.05/1.49      | k4_tarski(X1,X2) != sK1(k8_relat_1(X0,sK7)) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_20904,plain,
% 7.05/1.49      ( v1_relat_1(k8_relat_1(X0,sK7))
% 7.05/1.49      | k4_tarski(sK2(sK1(k8_relat_1(X0,sK7))),sK3(sK1(k8_relat_1(X0,sK7)))) != sK1(k8_relat_1(X0,sK7)) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_1280]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_20909,plain,
% 7.05/1.49      ( k4_tarski(sK2(sK1(k8_relat_1(X0,sK7))),sK3(sK1(k8_relat_1(X0,sK7)))) != sK1(k8_relat_1(X0,sK7))
% 7.05/1.49      | v1_relat_1(k8_relat_1(X0,sK7)) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_20904]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_21347,plain,
% 7.05/1.49      ( v1_relat_1(k8_relat_1(X0,sK7)) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_7184,c_21,c_20909]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_16,negated_conjecture,
% 7.05/1.49      ( r1_tarski(sK4,sK5) ),
% 7.05/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_574,plain,
% 7.05/1.49      ( r1_tarski(sK4,sK5) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_13,plain,
% 7.05/1.49      ( ~ r1_tarski(X0,X1)
% 7.05/1.49      | ~ v1_relat_1(X2)
% 7.05/1.49      | k8_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,X2) ),
% 7.05/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_577,plain,
% 7.05/1.49      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
% 7.05/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.05/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1773,plain,
% 7.05/1.49      ( k8_relat_1(sK5,k8_relat_1(sK4,X0)) = k8_relat_1(sK4,X0)
% 7.05/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_574,c_577]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2533,plain,
% 7.05/1.49      ( k8_relat_1(sK5,k8_relat_1(sK4,sK7)) = k8_relat_1(sK4,sK7) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_572,c_1773]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_14,plain,
% 7.05/1.49      ( ~ r1_tarski(X0,X1)
% 7.05/1.49      | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
% 7.05/1.49      | ~ v1_relat_1(X0)
% 7.05/1.49      | ~ v1_relat_1(X1) ),
% 7.05/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_576,plain,
% 7.05/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.05/1.49      | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1)) = iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2541,plain,
% 7.05/1.49      ( r1_tarski(k8_relat_1(sK4,sK7),X0) != iProver_top
% 7.05/1.49      | r1_tarski(k8_relat_1(sK4,sK7),k8_relat_1(sK5,X0)) = iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_2533,c_576]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17,negated_conjecture,
% 7.05/1.49      ( r1_tarski(sK6,sK7) ),
% 7.05/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_573,plain,
% 7.05/1.49      ( r1_tarski(sK6,sK7) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_7,plain,
% 7.05/1.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.05/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_583,plain,
% 7.05/1.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1076,plain,
% 7.05/1.49      ( k2_xboole_0(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) = k8_relat_1(X0,X2)
% 7.05/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.05/1.49      | v1_relat_1(X1) != iProver_top
% 7.05/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_576,c_583]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3007,plain,
% 7.05/1.49      ( k2_xboole_0(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7)) = k8_relat_1(X0,sK7)
% 7.05/1.49      | v1_relat_1(sK7) != iProver_top
% 7.05/1.49      | v1_relat_1(sK6) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_573,c_1076]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_19,negated_conjecture,
% 7.05/1.49      ( v1_relat_1(sK6) ),
% 7.05/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_762,plain,
% 7.05/1.49      ( r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7))
% 7.05/1.49      | ~ r1_tarski(sK6,sK7)
% 7.05/1.49      | ~ v1_relat_1(sK7)
% 7.05/1.49      | ~ v1_relat_1(sK6) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_814,plain,
% 7.05/1.49      ( ~ r1_tarski(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7))
% 7.05/1.49      | k2_xboole_0(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7)) = k8_relat_1(X0,sK7) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3678,plain,
% 7.05/1.49      ( k2_xboole_0(k8_relat_1(X0,sK6),k8_relat_1(X0,sK7)) = k8_relat_1(X0,sK7) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_3007,c_19,c_18,c_17,c_762,c_814]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6,plain,
% 7.05/1.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 7.05/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_584,plain,
% 7.05/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.05/1.49      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3682,plain,
% 7.05/1.49      ( r1_tarski(k8_relat_1(X0,sK7),X1) != iProver_top
% 7.05/1.49      | r1_tarski(k8_relat_1(X0,sK6),X1) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_3678,c_584]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5407,plain,
% 7.05/1.49      ( r1_tarski(k8_relat_1(sK4,sK7),X0) != iProver_top
% 7.05/1.49      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0)) = iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_2541,c_3682]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_15,negated_conjecture,
% 7.05/1.49      ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
% 7.05/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_575,plain,
% 7.05/1.49      ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_19677,plain,
% 7.05/1.49      ( r1_tarski(k8_relat_1(sK4,sK7),sK7) != iProver_top
% 7.05/1.49      | v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top
% 7.05/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_5407,c_575]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_19723,plain,
% 7.05/1.49      ( v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top
% 7.05/1.49      | r1_tarski(k8_relat_1(sK4,sK7),sK7) != iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,[status(thm)],[c_19677,c_21]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_19724,plain,
% 7.05/1.49      ( r1_tarski(k8_relat_1(sK4,sK7),sK7) != iProver_top
% 7.05/1.49      | v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_19723]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_19729,plain,
% 7.05/1.49      ( v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top
% 7.05/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_578,c_19724]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_19902,plain,
% 7.05/1.49      ( v1_relat_1(k8_relat_1(sK4,sK7)) != iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,[status(thm)],[c_19729,c_21]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_21371,plain,
% 7.05/1.49      ( $false ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_21347,c_19902]) ).
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  ------                               Statistics
% 7.05/1.49  
% 7.05/1.49  ------ General
% 7.05/1.49  
% 7.05/1.49  abstr_ref_over_cycles:                  0
% 7.05/1.49  abstr_ref_under_cycles:                 0
% 7.05/1.49  gc_basic_clause_elim:                   0
% 7.05/1.49  forced_gc_time:                         0
% 7.05/1.49  parsing_time:                           0.009
% 7.05/1.49  unif_index_cands_time:                  0.
% 7.05/1.49  unif_index_add_time:                    0.
% 7.05/1.49  orderings_time:                         0.
% 7.05/1.49  out_proof_time:                         0.011
% 7.05/1.49  total_time:                             0.57
% 7.05/1.49  num_of_symbols:                         47
% 7.05/1.49  num_of_terms:                           24752
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing
% 7.05/1.49  
% 7.05/1.49  num_of_splits:                          0
% 7.05/1.49  num_of_split_atoms:                     0
% 7.05/1.49  num_of_reused_defs:                     0
% 7.05/1.49  num_eq_ax_congr_red:                    20
% 7.05/1.49  num_of_sem_filtered_clauses:            1
% 7.05/1.49  num_of_subtypes:                        0
% 7.05/1.49  monotx_restored_types:                  0
% 7.05/1.49  sat_num_of_epr_types:                   0
% 7.05/1.49  sat_num_of_non_cyclic_types:            0
% 7.05/1.49  sat_guarded_non_collapsed_types:        0
% 7.05/1.49  num_pure_diseq_elim:                    0
% 7.05/1.49  simp_replaced_by:                       0
% 7.05/1.49  res_preprocessed:                       77
% 7.05/1.49  prep_upred:                             0
% 7.05/1.49  prep_unflattend:                        0
% 7.05/1.49  smt_new_axioms:                         0
% 7.05/1.49  pred_elim_cands:                        3
% 7.05/1.49  pred_elim:                              0
% 7.05/1.49  pred_elim_cl:                           0
% 7.05/1.49  pred_elim_cycles:                       1
% 7.05/1.49  merged_defs:                            0
% 7.05/1.49  merged_defs_ncl:                        0
% 7.05/1.49  bin_hyper_res:                          0
% 7.05/1.49  prep_cycles:                            3
% 7.05/1.49  pred_elim_time:                         0.
% 7.05/1.49  splitting_time:                         0.
% 7.05/1.49  sem_filter_time:                        0.
% 7.05/1.49  monotx_time:                            0.001
% 7.05/1.49  subtype_inf_time:                       0.
% 7.05/1.49  
% 7.05/1.49  ------ Problem properties
% 7.05/1.49  
% 7.05/1.49  clauses:                                20
% 7.05/1.49  conjectures:                            5
% 7.05/1.49  epr:                                    4
% 7.05/1.49  horn:                                   17
% 7.05/1.49  ground:                                 5
% 7.05/1.49  unary:                                  5
% 7.05/1.49  binary:                                 8
% 7.05/1.49  lits:                                   44
% 7.05/1.49  lits_eq:                                8
% 7.05/1.49  fd_pure:                                0
% 7.05/1.49  fd_pseudo:                              0
% 7.05/1.49  fd_cond:                                0
% 7.05/1.49  fd_pseudo_cond:                         3
% 7.05/1.49  ac_symbols:                             0
% 7.05/1.49  
% 7.05/1.49  ------ Propositional Solver
% 7.05/1.49  
% 7.05/1.49  prop_solver_calls:                      24
% 7.05/1.49  prop_fast_solver_calls:                 867
% 7.05/1.49  smt_solver_calls:                       0
% 7.05/1.49  smt_fast_solver_calls:                  0
% 7.05/1.49  prop_num_of_clauses:                    7890
% 7.05/1.49  prop_preprocess_simplified:             14645
% 7.05/1.49  prop_fo_subsumed:                       30
% 7.05/1.49  prop_solver_time:                       0.
% 7.05/1.49  smt_solver_time:                        0.
% 7.05/1.49  smt_fast_solver_time:                   0.
% 7.05/1.49  prop_fast_solver_time:                  0.
% 7.05/1.49  prop_unsat_core_time:                   0.
% 7.05/1.49  
% 7.05/1.49  ------ QBF
% 7.05/1.49  
% 7.05/1.49  qbf_q_res:                              0
% 7.05/1.49  qbf_num_tautologies:                    0
% 7.05/1.49  qbf_prep_cycles:                        0
% 7.05/1.49  
% 7.05/1.49  ------ BMC1
% 7.05/1.49  
% 7.05/1.49  bmc1_current_bound:                     -1
% 7.05/1.49  bmc1_last_solved_bound:                 -1
% 7.05/1.49  bmc1_unsat_core_size:                   -1
% 7.05/1.49  bmc1_unsat_core_parents_size:           -1
% 7.05/1.49  bmc1_merge_next_fun:                    0
% 7.05/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.05/1.49  
% 7.05/1.49  ------ Instantiation
% 7.05/1.49  
% 7.05/1.49  inst_num_of_clauses:                    1947
% 7.05/1.49  inst_num_in_passive:                    355
% 7.05/1.49  inst_num_in_active:                     765
% 7.05/1.49  inst_num_in_unprocessed:                827
% 7.05/1.49  inst_num_of_loops:                      910
% 7.05/1.49  inst_num_of_learning_restarts:          0
% 7.05/1.49  inst_num_moves_active_passive:          144
% 7.05/1.49  inst_lit_activity:                      0
% 7.05/1.49  inst_lit_activity_moves:                0
% 7.05/1.49  inst_num_tautologies:                   0
% 7.05/1.49  inst_num_prop_implied:                  0
% 7.05/1.49  inst_num_existing_simplified:           0
% 7.05/1.49  inst_num_eq_res_simplified:             0
% 7.05/1.49  inst_num_child_elim:                    0
% 7.05/1.49  inst_num_of_dismatching_blockings:      2076
% 7.05/1.49  inst_num_of_non_proper_insts:           2190
% 7.05/1.49  inst_num_of_duplicates:                 0
% 7.05/1.49  inst_inst_num_from_inst_to_res:         0
% 7.05/1.49  inst_dismatching_checking_time:         0.
% 7.05/1.49  
% 7.05/1.49  ------ Resolution
% 7.05/1.49  
% 7.05/1.49  res_num_of_clauses:                     0
% 7.05/1.49  res_num_in_passive:                     0
% 7.05/1.49  res_num_in_active:                      0
% 7.05/1.49  res_num_of_loops:                       80
% 7.05/1.49  res_forward_subset_subsumed:            73
% 7.05/1.49  res_backward_subset_subsumed:           0
% 7.05/1.49  res_forward_subsumed:                   0
% 7.05/1.49  res_backward_subsumed:                  0
% 7.05/1.49  res_forward_subsumption_resolution:     0
% 7.05/1.49  res_backward_subsumption_resolution:    0
% 7.05/1.49  res_clause_to_clause_subsumption:       2905
% 7.05/1.49  res_orphan_elimination:                 0
% 7.05/1.49  res_tautology_del:                      109
% 7.05/1.49  res_num_eq_res_simplified:              0
% 7.05/1.49  res_num_sel_changes:                    0
% 7.05/1.49  res_moves_from_active_to_pass:          0
% 7.05/1.49  
% 7.05/1.49  ------ Superposition
% 7.05/1.49  
% 7.05/1.49  sup_time_total:                         0.
% 7.05/1.49  sup_time_generating:                    0.
% 7.05/1.49  sup_time_sim_full:                      0.
% 7.05/1.49  sup_time_sim_immed:                     0.
% 7.05/1.49  
% 7.05/1.49  sup_num_of_clauses:                     566
% 7.05/1.49  sup_num_in_active:                      182
% 7.05/1.49  sup_num_in_passive:                     384
% 7.05/1.49  sup_num_of_loops:                       181
% 7.05/1.49  sup_fw_superposition:                   277
% 7.05/1.49  sup_bw_superposition:                   557
% 7.05/1.49  sup_immediate_simplified:               137
% 7.05/1.49  sup_given_eliminated:                   0
% 7.05/1.49  comparisons_done:                       0
% 7.05/1.49  comparisons_avoided:                    8
% 7.05/1.49  
% 7.05/1.49  ------ Simplifications
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  sim_fw_subset_subsumed:                 17
% 7.05/1.49  sim_bw_subset_subsumed:                 4
% 7.05/1.49  sim_fw_subsumed:                        65
% 7.05/1.49  sim_bw_subsumed:                        0
% 7.05/1.49  sim_fw_subsumption_res:                 11
% 7.05/1.49  sim_bw_subsumption_res:                 0
% 7.05/1.49  sim_tautology_del:                      117
% 7.05/1.49  sim_eq_tautology_del:                   2
% 7.05/1.49  sim_eq_res_simp:                        10
% 7.05/1.49  sim_fw_demodulated:                     26
% 7.05/1.49  sim_bw_demodulated:                     0
% 7.05/1.49  sim_light_normalised:                   34
% 7.05/1.49  sim_joinable_taut:                      0
% 7.05/1.49  sim_joinable_simp:                      0
% 7.05/1.49  sim_ac_normalised:                      0
% 7.05/1.49  sim_smt_subsumption:                    0
% 7.05/1.49  
%------------------------------------------------------------------------------
