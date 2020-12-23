%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:42 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 308 expanded)
%              Number of clauses        :   58 (  97 expanded)
%              Number of leaves         :   13 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  345 (1241 expanded)
%              Number of equality atoms :  107 ( 169 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f29,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f29,f28])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f33,plain,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f20,f32,f31])).

fof(f48,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f42,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK2(X4),sK3(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( v1_relat_1(X0)
      | k4_tarski(X2,X3) != sK1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_527,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_518,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_525,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_529,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_978,plain,
    ( k3_xboole_0(k8_relat_1(X0,X1),X1) = k8_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_525,c_529])).

cnf(c_1393,plain,
    ( k3_xboole_0(k8_relat_1(X0,sK6),sK6) = k8_relat_1(X0,sK6) ),
    inference(superposition,[status(thm)],[c_518,c_978])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_532,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1495,plain,
    ( r2_hidden(X0,k8_relat_1(X1,sK6)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_532])).

cnf(c_2895,plain,
    ( r2_hidden(sK1(k8_relat_1(X0,sK6)),sK6) = iProver_top
    | v1_relat_1(k8_relat_1(X0,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_527,c_1495])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_526,plain,
    ( k4_tarski(sK2(X0),sK3(X0)) = X0
    | r2_hidden(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4701,plain,
    ( k4_tarski(sK2(sK1(k8_relat_1(X0,sK6))),sK3(sK1(k8_relat_1(X0,sK6)))) = sK1(k8_relat_1(X0,sK6))
    | v1_relat_1(k8_relat_1(X0,sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2895,c_526])).

cnf(c_19,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_44223,plain,
    ( v1_relat_1(k8_relat_1(X0,sK6)) = iProver_top
    | k4_tarski(sK2(sK1(k8_relat_1(X0,sK6))),sK3(sK1(k8_relat_1(X0,sK6)))) = sK1(k8_relat_1(X0,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4701,c_19])).

cnf(c_44224,plain,
    ( k4_tarski(sK2(sK1(k8_relat_1(X0,sK6))),sK3(sK1(k8_relat_1(X0,sK6)))) = sK1(k8_relat_1(X0,sK6))
    | v1_relat_1(k8_relat_1(X0,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_44223])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_521,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_524,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1620,plain,
    ( k8_relat_1(sK5,k8_relat_1(sK4,X0)) = k8_relat_1(sK4,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_521,c_524])).

cnf(c_2093,plain,
    ( k8_relat_1(sK5,k8_relat_1(sK4,sK6)) = k8_relat_1(sK4,sK6) ),
    inference(superposition,[status(thm)],[c_518,c_1620])).

cnf(c_2284,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK4,sK6)) = iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2093,c_525])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,plain,
    ( r1_tarski(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_561,plain,
    ( ~ r1_tarski(X0,k8_relat_1(sK5,sK7))
    | ~ r1_tarski(k8_relat_1(sK4,sK6),X0)
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_579,plain,
    ( ~ r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7))
    | ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0))
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_580,plain,
    ( r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7)) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0)) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_582,plain,
    ( r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7)) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) = iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_618,plain,
    ( ~ r1_tarski(X0,sK7)
    | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_619,plain,
    ( r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_621,plain,
    ( r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7)) = iProver_top
    | r1_tarski(sK6,sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_973,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_974,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_523,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2285,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),X0) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2093,c_523])).

cnf(c_2289,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) = iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),sK6) != iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_3204,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2284,c_19,c_20,c_21,c_23,c_582,c_621,c_974,c_2289])).

cnf(c_44251,plain,
    ( k4_tarski(sK2(sK1(k8_relat_1(sK4,sK6))),sK3(sK1(k8_relat_1(sK4,sK6)))) = sK1(k8_relat_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_44224,c_3204])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | k4_tarski(X1,X2) != sK1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1634,plain,
    ( v1_relat_1(k8_relat_1(X0,X1))
    | k4_tarski(X2,X3) != sK1(k8_relat_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7366,plain,
    ( v1_relat_1(k8_relat_1(X0,X1))
    | k4_tarski(sK2(sK1(k8_relat_1(X0,X1))),sK3(sK1(k8_relat_1(X0,X1)))) != sK1(k8_relat_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_18762,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK6))
    | k4_tarski(sK2(sK1(k8_relat_1(sK4,sK6))),sK3(sK1(k8_relat_1(sK4,sK6)))) != sK1(k8_relat_1(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_7366])).

cnf(c_2288,plain,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),X0)
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2285])).

cnf(c_2290,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6))
    | ~ r1_tarski(k8_relat_1(sK4,sK6),sK6)
    | ~ v1_relat_1(k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2288])).

cnf(c_620,plain,
    ( r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7))
    | ~ r1_tarski(sK6,sK7)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_581,plain,
    ( ~ r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7))
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
    | ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44251,c_18762,c_2290,c_973,c_620,c_581,c_14,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:41:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.68/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.68/1.99  
% 11.68/1.99  ------  iProver source info
% 11.68/1.99  
% 11.68/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.68/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.68/1.99  git: non_committed_changes: false
% 11.68/1.99  git: last_make_outside_of_git: false
% 11.68/1.99  
% 11.68/1.99  ------ 
% 11.68/1.99  
% 11.68/1.99  ------ Input Options
% 11.68/1.99  
% 11.68/1.99  --out_options                           all
% 11.68/1.99  --tptp_safe_out                         true
% 11.68/1.99  --problem_path                          ""
% 11.68/1.99  --include_path                          ""
% 11.68/1.99  --clausifier                            res/vclausify_rel
% 11.68/1.99  --clausifier_options                    ""
% 11.68/1.99  --stdin                                 false
% 11.68/1.99  --stats_out                             all
% 11.68/1.99  
% 11.68/1.99  ------ General Options
% 11.68/1.99  
% 11.68/1.99  --fof                                   false
% 11.68/1.99  --time_out_real                         305.
% 11.68/1.99  --time_out_virtual                      -1.
% 11.68/1.99  --symbol_type_check                     false
% 11.68/1.99  --clausify_out                          false
% 11.68/1.99  --sig_cnt_out                           false
% 11.68/1.99  --trig_cnt_out                          false
% 11.68/1.99  --trig_cnt_out_tolerance                1.
% 11.68/1.99  --trig_cnt_out_sk_spl                   false
% 11.68/1.99  --abstr_cl_out                          false
% 11.68/1.99  
% 11.68/1.99  ------ Global Options
% 11.68/1.99  
% 11.68/1.99  --schedule                              default
% 11.68/1.99  --add_important_lit                     false
% 11.68/1.99  --prop_solver_per_cl                    1000
% 11.68/1.99  --min_unsat_core                        false
% 11.68/1.99  --soft_assumptions                      false
% 11.68/1.99  --soft_lemma_size                       3
% 11.68/1.99  --prop_impl_unit_size                   0
% 11.68/1.99  --prop_impl_unit                        []
% 11.68/1.99  --share_sel_clauses                     true
% 11.68/1.99  --reset_solvers                         false
% 11.68/1.99  --bc_imp_inh                            [conj_cone]
% 11.68/1.99  --conj_cone_tolerance                   3.
% 11.68/1.99  --extra_neg_conj                        none
% 11.68/1.99  --large_theory_mode                     true
% 11.68/1.99  --prolific_symb_bound                   200
% 11.68/1.99  --lt_threshold                          2000
% 11.68/1.99  --clause_weak_htbl                      true
% 11.68/1.99  --gc_record_bc_elim                     false
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing Options
% 11.68/1.99  
% 11.68/1.99  --preprocessing_flag                    true
% 11.68/1.99  --time_out_prep_mult                    0.1
% 11.68/1.99  --splitting_mode                        input
% 11.68/1.99  --splitting_grd                         true
% 11.68/1.99  --splitting_cvd                         false
% 11.68/1.99  --splitting_cvd_svl                     false
% 11.68/1.99  --splitting_nvd                         32
% 11.68/1.99  --sub_typing                            true
% 11.68/1.99  --prep_gs_sim                           true
% 11.68/1.99  --prep_unflatten                        true
% 11.68/1.99  --prep_res_sim                          true
% 11.68/1.99  --prep_upred                            true
% 11.68/1.99  --prep_sem_filter                       exhaustive
% 11.68/1.99  --prep_sem_filter_out                   false
% 11.68/1.99  --pred_elim                             true
% 11.68/1.99  --res_sim_input                         true
% 11.68/1.99  --eq_ax_congr_red                       true
% 11.68/1.99  --pure_diseq_elim                       true
% 11.68/1.99  --brand_transform                       false
% 11.68/1.99  --non_eq_to_eq                          false
% 11.68/1.99  --prep_def_merge                        true
% 11.68/1.99  --prep_def_merge_prop_impl              false
% 11.68/1.99  --prep_def_merge_mbd                    true
% 11.68/1.99  --prep_def_merge_tr_red                 false
% 11.68/1.99  --prep_def_merge_tr_cl                  false
% 11.68/1.99  --smt_preprocessing                     true
% 11.68/1.99  --smt_ac_axioms                         fast
% 11.68/1.99  --preprocessed_out                      false
% 11.68/1.99  --preprocessed_stats                    false
% 11.68/1.99  
% 11.68/1.99  ------ Abstraction refinement Options
% 11.68/1.99  
% 11.68/1.99  --abstr_ref                             []
% 11.68/1.99  --abstr_ref_prep                        false
% 11.68/1.99  --abstr_ref_until_sat                   false
% 11.68/1.99  --abstr_ref_sig_restrict                funpre
% 11.68/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.68/1.99  --abstr_ref_under                       []
% 11.68/1.99  
% 11.68/1.99  ------ SAT Options
% 11.68/1.99  
% 11.68/1.99  --sat_mode                              false
% 11.68/1.99  --sat_fm_restart_options                ""
% 11.68/1.99  --sat_gr_def                            false
% 11.68/1.99  --sat_epr_types                         true
% 11.68/1.99  --sat_non_cyclic_types                  false
% 11.68/1.99  --sat_finite_models                     false
% 11.68/1.99  --sat_fm_lemmas                         false
% 11.68/1.99  --sat_fm_prep                           false
% 11.68/1.99  --sat_fm_uc_incr                        true
% 11.68/1.99  --sat_out_model                         small
% 11.68/1.99  --sat_out_clauses                       false
% 11.68/1.99  
% 11.68/1.99  ------ QBF Options
% 11.68/1.99  
% 11.68/1.99  --qbf_mode                              false
% 11.68/1.99  --qbf_elim_univ                         false
% 11.68/1.99  --qbf_dom_inst                          none
% 11.68/1.99  --qbf_dom_pre_inst                      false
% 11.68/1.99  --qbf_sk_in                             false
% 11.68/1.99  --qbf_pred_elim                         true
% 11.68/1.99  --qbf_split                             512
% 11.68/1.99  
% 11.68/1.99  ------ BMC1 Options
% 11.68/1.99  
% 11.68/1.99  --bmc1_incremental                      false
% 11.68/1.99  --bmc1_axioms                           reachable_all
% 11.68/1.99  --bmc1_min_bound                        0
% 11.68/1.99  --bmc1_max_bound                        -1
% 11.68/1.99  --bmc1_max_bound_default                -1
% 11.68/1.99  --bmc1_symbol_reachability              true
% 11.68/1.99  --bmc1_property_lemmas                  false
% 11.68/1.99  --bmc1_k_induction                      false
% 11.68/1.99  --bmc1_non_equiv_states                 false
% 11.68/1.99  --bmc1_deadlock                         false
% 11.68/1.99  --bmc1_ucm                              false
% 11.68/1.99  --bmc1_add_unsat_core                   none
% 11.68/1.99  --bmc1_unsat_core_children              false
% 11.68/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.68/1.99  --bmc1_out_stat                         full
% 11.68/1.99  --bmc1_ground_init                      false
% 11.68/1.99  --bmc1_pre_inst_next_state              false
% 11.68/1.99  --bmc1_pre_inst_state                   false
% 11.68/1.99  --bmc1_pre_inst_reach_state             false
% 11.68/1.99  --bmc1_out_unsat_core                   false
% 11.68/1.99  --bmc1_aig_witness_out                  false
% 11.68/1.99  --bmc1_verbose                          false
% 11.68/1.99  --bmc1_dump_clauses_tptp                false
% 11.68/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.68/1.99  --bmc1_dump_file                        -
% 11.68/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.68/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.68/1.99  --bmc1_ucm_extend_mode                  1
% 11.68/1.99  --bmc1_ucm_init_mode                    2
% 11.68/1.99  --bmc1_ucm_cone_mode                    none
% 11.68/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.68/1.99  --bmc1_ucm_relax_model                  4
% 11.68/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.68/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.68/1.99  --bmc1_ucm_layered_model                none
% 11.68/1.99  --bmc1_ucm_max_lemma_size               10
% 11.68/1.99  
% 11.68/1.99  ------ AIG Options
% 11.68/1.99  
% 11.68/1.99  --aig_mode                              false
% 11.68/1.99  
% 11.68/1.99  ------ Instantiation Options
% 11.68/1.99  
% 11.68/1.99  --instantiation_flag                    true
% 11.68/1.99  --inst_sos_flag                         true
% 11.68/1.99  --inst_sos_phase                        true
% 11.68/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel_side                     num_symb
% 11.68/1.99  --inst_solver_per_active                1400
% 11.68/1.99  --inst_solver_calls_frac                1.
% 11.68/1.99  --inst_passive_queue_type               priority_queues
% 11.68/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.68/1.99  --inst_passive_queues_freq              [25;2]
% 11.68/1.99  --inst_dismatching                      true
% 11.68/1.99  --inst_eager_unprocessed_to_passive     true
% 11.68/1.99  --inst_prop_sim_given                   true
% 11.68/1.99  --inst_prop_sim_new                     false
% 11.68/1.99  --inst_subs_new                         false
% 11.68/1.99  --inst_eq_res_simp                      false
% 11.68/1.99  --inst_subs_given                       false
% 11.68/1.99  --inst_orphan_elimination               true
% 11.68/1.99  --inst_learning_loop_flag               true
% 11.68/1.99  --inst_learning_start                   3000
% 11.68/1.99  --inst_learning_factor                  2
% 11.68/1.99  --inst_start_prop_sim_after_learn       3
% 11.68/1.99  --inst_sel_renew                        solver
% 11.68/1.99  --inst_lit_activity_flag                true
% 11.68/1.99  --inst_restr_to_given                   false
% 11.68/1.99  --inst_activity_threshold               500
% 11.68/1.99  --inst_out_proof                        true
% 11.68/1.99  
% 11.68/1.99  ------ Resolution Options
% 11.68/1.99  
% 11.68/1.99  --resolution_flag                       true
% 11.68/1.99  --res_lit_sel                           adaptive
% 11.68/1.99  --res_lit_sel_side                      none
% 11.68/1.99  --res_ordering                          kbo
% 11.68/1.99  --res_to_prop_solver                    active
% 11.68/1.99  --res_prop_simpl_new                    false
% 11.68/1.99  --res_prop_simpl_given                  true
% 11.68/1.99  --res_passive_queue_type                priority_queues
% 11.68/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.68/1.99  --res_passive_queues_freq               [15;5]
% 11.68/1.99  --res_forward_subs                      full
% 11.68/1.99  --res_backward_subs                     full
% 11.68/1.99  --res_forward_subs_resolution           true
% 11.68/1.99  --res_backward_subs_resolution          true
% 11.68/1.99  --res_orphan_elimination                true
% 11.68/1.99  --res_time_limit                        2.
% 11.68/1.99  --res_out_proof                         true
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Options
% 11.68/1.99  
% 11.68/1.99  --superposition_flag                    true
% 11.68/1.99  --sup_passive_queue_type                priority_queues
% 11.68/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.68/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.68/1.99  --demod_completeness_check              fast
% 11.68/1.99  --demod_use_ground                      true
% 11.68/1.99  --sup_to_prop_solver                    passive
% 11.68/1.99  --sup_prop_simpl_new                    true
% 11.68/1.99  --sup_prop_simpl_given                  true
% 11.68/1.99  --sup_fun_splitting                     true
% 11.68/1.99  --sup_smt_interval                      50000
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Simplification Setup
% 11.68/1.99  
% 11.68/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.68/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.68/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_immed_triv                        [TrivRules]
% 11.68/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_bw_main                     []
% 11.68/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.68/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_input_bw                          []
% 11.68/1.99  
% 11.68/1.99  ------ Combination Options
% 11.68/1.99  
% 11.68/1.99  --comb_res_mult                         3
% 11.68/1.99  --comb_sup_mult                         2
% 11.68/1.99  --comb_inst_mult                        10
% 11.68/1.99  
% 11.68/1.99  ------ Debug Options
% 11.68/1.99  
% 11.68/1.99  --dbg_backtrace                         false
% 11.68/1.99  --dbg_dump_prop_clauses                 false
% 11.68/1.99  --dbg_dump_prop_clauses_file            -
% 11.68/1.99  --dbg_out_stat                          false
% 11.68/1.99  ------ Parsing...
% 11.68/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.68/1.99  ------ Proving...
% 11.68/1.99  ------ Problem Properties 
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  clauses                                 19
% 11.68/1.99  conjectures                             5
% 11.68/1.99  EPR                                     5
% 11.68/1.99  Horn                                    16
% 11.68/1.99  unary                                   5
% 11.68/1.99  binary                                  6
% 11.68/1.99  lits                                    43
% 11.68/1.99  lits eq                                 7
% 11.68/1.99  fd_pure                                 0
% 11.68/1.99  fd_pseudo                               0
% 11.68/1.99  fd_cond                                 0
% 11.68/1.99  fd_pseudo_cond                          3
% 11.68/1.99  AC symbols                              0
% 11.68/1.99  
% 11.68/1.99  ------ Schedule dynamic 5 is on 
% 11.68/1.99  
% 11.68/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  ------ 
% 11.68/1.99  Current options:
% 11.68/1.99  ------ 
% 11.68/1.99  
% 11.68/1.99  ------ Input Options
% 11.68/1.99  
% 11.68/1.99  --out_options                           all
% 11.68/1.99  --tptp_safe_out                         true
% 11.68/1.99  --problem_path                          ""
% 11.68/1.99  --include_path                          ""
% 11.68/1.99  --clausifier                            res/vclausify_rel
% 11.68/1.99  --clausifier_options                    ""
% 11.68/1.99  --stdin                                 false
% 11.68/1.99  --stats_out                             all
% 11.68/1.99  
% 11.68/1.99  ------ General Options
% 11.68/1.99  
% 11.68/1.99  --fof                                   false
% 11.68/1.99  --time_out_real                         305.
% 11.68/1.99  --time_out_virtual                      -1.
% 11.68/1.99  --symbol_type_check                     false
% 11.68/1.99  --clausify_out                          false
% 11.68/1.99  --sig_cnt_out                           false
% 11.68/1.99  --trig_cnt_out                          false
% 11.68/1.99  --trig_cnt_out_tolerance                1.
% 11.68/1.99  --trig_cnt_out_sk_spl                   false
% 11.68/1.99  --abstr_cl_out                          false
% 11.68/1.99  
% 11.68/1.99  ------ Global Options
% 11.68/1.99  
% 11.68/1.99  --schedule                              default
% 11.68/1.99  --add_important_lit                     false
% 11.68/1.99  --prop_solver_per_cl                    1000
% 11.68/1.99  --min_unsat_core                        false
% 11.68/1.99  --soft_assumptions                      false
% 11.68/1.99  --soft_lemma_size                       3
% 11.68/1.99  --prop_impl_unit_size                   0
% 11.68/1.99  --prop_impl_unit                        []
% 11.68/1.99  --share_sel_clauses                     true
% 11.68/1.99  --reset_solvers                         false
% 11.68/1.99  --bc_imp_inh                            [conj_cone]
% 11.68/1.99  --conj_cone_tolerance                   3.
% 11.68/1.99  --extra_neg_conj                        none
% 11.68/1.99  --large_theory_mode                     true
% 11.68/1.99  --prolific_symb_bound                   200
% 11.68/1.99  --lt_threshold                          2000
% 11.68/1.99  --clause_weak_htbl                      true
% 11.68/1.99  --gc_record_bc_elim                     false
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing Options
% 11.68/1.99  
% 11.68/1.99  --preprocessing_flag                    true
% 11.68/1.99  --time_out_prep_mult                    0.1
% 11.68/1.99  --splitting_mode                        input
% 11.68/1.99  --splitting_grd                         true
% 11.68/1.99  --splitting_cvd                         false
% 11.68/1.99  --splitting_cvd_svl                     false
% 11.68/1.99  --splitting_nvd                         32
% 11.68/1.99  --sub_typing                            true
% 11.68/1.99  --prep_gs_sim                           true
% 11.68/1.99  --prep_unflatten                        true
% 11.68/1.99  --prep_res_sim                          true
% 11.68/1.99  --prep_upred                            true
% 11.68/1.99  --prep_sem_filter                       exhaustive
% 11.68/1.99  --prep_sem_filter_out                   false
% 11.68/1.99  --pred_elim                             true
% 11.68/1.99  --res_sim_input                         true
% 11.68/1.99  --eq_ax_congr_red                       true
% 11.68/1.99  --pure_diseq_elim                       true
% 11.68/1.99  --brand_transform                       false
% 11.68/1.99  --non_eq_to_eq                          false
% 11.68/1.99  --prep_def_merge                        true
% 11.68/1.99  --prep_def_merge_prop_impl              false
% 11.68/1.99  --prep_def_merge_mbd                    true
% 11.68/1.99  --prep_def_merge_tr_red                 false
% 11.68/1.99  --prep_def_merge_tr_cl                  false
% 11.68/1.99  --smt_preprocessing                     true
% 11.68/1.99  --smt_ac_axioms                         fast
% 11.68/1.99  --preprocessed_out                      false
% 11.68/1.99  --preprocessed_stats                    false
% 11.68/1.99  
% 11.68/1.99  ------ Abstraction refinement Options
% 11.68/1.99  
% 11.68/1.99  --abstr_ref                             []
% 11.68/1.99  --abstr_ref_prep                        false
% 11.68/1.99  --abstr_ref_until_sat                   false
% 11.68/1.99  --abstr_ref_sig_restrict                funpre
% 11.68/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.68/1.99  --abstr_ref_under                       []
% 11.68/1.99  
% 11.68/1.99  ------ SAT Options
% 11.68/1.99  
% 11.68/1.99  --sat_mode                              false
% 11.68/1.99  --sat_fm_restart_options                ""
% 11.68/1.99  --sat_gr_def                            false
% 11.68/1.99  --sat_epr_types                         true
% 11.68/1.99  --sat_non_cyclic_types                  false
% 11.68/1.99  --sat_finite_models                     false
% 11.68/1.99  --sat_fm_lemmas                         false
% 11.68/1.99  --sat_fm_prep                           false
% 11.68/1.99  --sat_fm_uc_incr                        true
% 11.68/1.99  --sat_out_model                         small
% 11.68/1.99  --sat_out_clauses                       false
% 11.68/1.99  
% 11.68/1.99  ------ QBF Options
% 11.68/1.99  
% 11.68/1.99  --qbf_mode                              false
% 11.68/1.99  --qbf_elim_univ                         false
% 11.68/1.99  --qbf_dom_inst                          none
% 11.68/1.99  --qbf_dom_pre_inst                      false
% 11.68/1.99  --qbf_sk_in                             false
% 11.68/1.99  --qbf_pred_elim                         true
% 11.68/1.99  --qbf_split                             512
% 11.68/1.99  
% 11.68/1.99  ------ BMC1 Options
% 11.68/1.99  
% 11.68/1.99  --bmc1_incremental                      false
% 11.68/1.99  --bmc1_axioms                           reachable_all
% 11.68/1.99  --bmc1_min_bound                        0
% 11.68/1.99  --bmc1_max_bound                        -1
% 11.68/1.99  --bmc1_max_bound_default                -1
% 11.68/1.99  --bmc1_symbol_reachability              true
% 11.68/1.99  --bmc1_property_lemmas                  false
% 11.68/1.99  --bmc1_k_induction                      false
% 11.68/1.99  --bmc1_non_equiv_states                 false
% 11.68/1.99  --bmc1_deadlock                         false
% 11.68/1.99  --bmc1_ucm                              false
% 11.68/1.99  --bmc1_add_unsat_core                   none
% 11.68/1.99  --bmc1_unsat_core_children              false
% 11.68/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.68/1.99  --bmc1_out_stat                         full
% 11.68/1.99  --bmc1_ground_init                      false
% 11.68/1.99  --bmc1_pre_inst_next_state              false
% 11.68/1.99  --bmc1_pre_inst_state                   false
% 11.68/1.99  --bmc1_pre_inst_reach_state             false
% 11.68/1.99  --bmc1_out_unsat_core                   false
% 11.68/1.99  --bmc1_aig_witness_out                  false
% 11.68/1.99  --bmc1_verbose                          false
% 11.68/1.99  --bmc1_dump_clauses_tptp                false
% 11.68/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.68/1.99  --bmc1_dump_file                        -
% 11.68/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.68/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.68/1.99  --bmc1_ucm_extend_mode                  1
% 11.68/1.99  --bmc1_ucm_init_mode                    2
% 11.68/1.99  --bmc1_ucm_cone_mode                    none
% 11.68/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.68/1.99  --bmc1_ucm_relax_model                  4
% 11.68/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.68/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.68/1.99  --bmc1_ucm_layered_model                none
% 11.68/1.99  --bmc1_ucm_max_lemma_size               10
% 11.68/1.99  
% 11.68/1.99  ------ AIG Options
% 11.68/1.99  
% 11.68/1.99  --aig_mode                              false
% 11.68/1.99  
% 11.68/1.99  ------ Instantiation Options
% 11.68/1.99  
% 11.68/1.99  --instantiation_flag                    true
% 11.68/1.99  --inst_sos_flag                         true
% 11.68/1.99  --inst_sos_phase                        true
% 11.68/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel_side                     none
% 11.68/1.99  --inst_solver_per_active                1400
% 11.68/1.99  --inst_solver_calls_frac                1.
% 11.68/1.99  --inst_passive_queue_type               priority_queues
% 11.68/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.68/1.99  --inst_passive_queues_freq              [25;2]
% 11.68/1.99  --inst_dismatching                      true
% 11.68/1.99  --inst_eager_unprocessed_to_passive     true
% 11.68/1.99  --inst_prop_sim_given                   true
% 11.68/1.99  --inst_prop_sim_new                     false
% 11.68/1.99  --inst_subs_new                         false
% 11.68/1.99  --inst_eq_res_simp                      false
% 11.68/1.99  --inst_subs_given                       false
% 11.68/1.99  --inst_orphan_elimination               true
% 11.68/1.99  --inst_learning_loop_flag               true
% 11.68/1.99  --inst_learning_start                   3000
% 11.68/1.99  --inst_learning_factor                  2
% 11.68/1.99  --inst_start_prop_sim_after_learn       3
% 11.68/1.99  --inst_sel_renew                        solver
% 11.68/1.99  --inst_lit_activity_flag                true
% 11.68/1.99  --inst_restr_to_given                   false
% 11.68/1.99  --inst_activity_threshold               500
% 11.68/1.99  --inst_out_proof                        true
% 11.68/1.99  
% 11.68/1.99  ------ Resolution Options
% 11.68/1.99  
% 11.68/1.99  --resolution_flag                       false
% 11.68/1.99  --res_lit_sel                           adaptive
% 11.68/1.99  --res_lit_sel_side                      none
% 11.68/1.99  --res_ordering                          kbo
% 11.68/1.99  --res_to_prop_solver                    active
% 11.68/1.99  --res_prop_simpl_new                    false
% 11.68/1.99  --res_prop_simpl_given                  true
% 11.68/1.99  --res_passive_queue_type                priority_queues
% 11.68/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.68/1.99  --res_passive_queues_freq               [15;5]
% 11.68/1.99  --res_forward_subs                      full
% 11.68/1.99  --res_backward_subs                     full
% 11.68/1.99  --res_forward_subs_resolution           true
% 11.68/1.99  --res_backward_subs_resolution          true
% 11.68/1.99  --res_orphan_elimination                true
% 11.68/1.99  --res_time_limit                        2.
% 11.68/1.99  --res_out_proof                         true
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Options
% 11.68/1.99  
% 11.68/1.99  --superposition_flag                    true
% 11.68/1.99  --sup_passive_queue_type                priority_queues
% 11.68/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.68/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.68/1.99  --demod_completeness_check              fast
% 11.68/1.99  --demod_use_ground                      true
% 11.68/1.99  --sup_to_prop_solver                    passive
% 11.68/1.99  --sup_prop_simpl_new                    true
% 11.68/1.99  --sup_prop_simpl_given                  true
% 11.68/1.99  --sup_fun_splitting                     true
% 11.68/1.99  --sup_smt_interval                      50000
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Simplification Setup
% 11.68/1.99  
% 11.68/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.68/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.68/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_immed_triv                        [TrivRules]
% 11.68/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_bw_main                     []
% 11.68/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.68/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_input_bw                          []
% 11.68/1.99  
% 11.68/1.99  ------ Combination Options
% 11.68/1.99  
% 11.68/1.99  --comb_res_mult                         3
% 11.68/1.99  --comb_sup_mult                         2
% 11.68/1.99  --comb_inst_mult                        10
% 11.68/1.99  
% 11.68/1.99  ------ Debug Options
% 11.68/1.99  
% 11.68/1.99  --dbg_backtrace                         false
% 11.68/1.99  --dbg_dump_prop_clauses                 false
% 11.68/1.99  --dbg_dump_prop_clauses_file            -
% 11.68/1.99  --dbg_out_stat                          false
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  ------ Proving...
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  % SZS status Theorem for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  fof(f4,axiom,(
% 11.68/1.99    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 11.68/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f13,plain,(
% 11.68/1.99    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 11.68/1.99    inference(ennf_transformation,[],[f4])).
% 11.68/1.99  
% 11.68/1.99  fof(f26,plain,(
% 11.68/1.99    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 11.68/1.99    inference(nnf_transformation,[],[f13])).
% 11.68/1.99  
% 11.68/1.99  fof(f27,plain,(
% 11.68/1.99    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 11.68/1.99    inference(rectify,[],[f26])).
% 11.68/1.99  
% 11.68/1.99  fof(f29,plain,(
% 11.68/1.99    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f28,plain,(
% 11.68/1.99    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f30,plain,(
% 11.68/1.99    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f29,f28])).
% 11.68/1.99  
% 11.68/1.99  fof(f43,plain,(
% 11.68/1.99    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f30])).
% 11.68/1.99  
% 11.68/1.99  fof(f8,conjecture,(
% 11.68/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 11.68/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f9,negated_conjecture,(
% 11.68/1.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 11.68/1.99    inference(negated_conjecture,[],[f8])).
% 11.68/1.99  
% 11.68/1.99  fof(f19,plain,(
% 11.68/1.99    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 11.68/1.99    inference(ennf_transformation,[],[f9])).
% 11.68/1.99  
% 11.68/1.99  fof(f20,plain,(
% 11.68/1.99    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 11.68/1.99    inference(flattening,[],[f19])).
% 11.68/1.99  
% 11.68/1.99  fof(f32,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK7)) & r1_tarski(X0,X1) & r1_tarski(X2,sK7) & v1_relat_1(sK7))) )),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f31,plain,(
% 11.68/1.99    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X3)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,X3) & v1_relat_1(X3)) & v1_relat_1(sK6))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f33,plain,(
% 11.68/1.99    (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,sK7) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f20,f32,f31])).
% 11.68/1.99  
% 11.68/1.99  fof(f48,plain,(
% 11.68/1.99    v1_relat_1(sK6)),
% 11.68/1.99    inference(cnf_transformation,[],[f33])).
% 11.68/1.99  
% 11.68/1.99  fof(f5,axiom,(
% 11.68/1.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 11.68/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f14,plain,(
% 11.68/1.99    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f5])).
% 11.68/1.99  
% 11.68/1.99  fof(f45,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f14])).
% 11.68/1.99  
% 11.68/1.99  fof(f3,axiom,(
% 11.68/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.68/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f12,plain,(
% 11.68/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f3])).
% 11.68/1.99  
% 11.68/1.99  fof(f41,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f12])).
% 11.68/1.99  
% 11.68/1.99  fof(f1,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.68/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f21,plain,(
% 11.68/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.68/1.99    inference(nnf_transformation,[],[f1])).
% 11.68/1.99  
% 11.68/1.99  fof(f22,plain,(
% 11.68/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.68/1.99    inference(flattening,[],[f21])).
% 11.68/1.99  
% 11.68/1.99  fof(f23,plain,(
% 11.68/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.68/1.99    inference(rectify,[],[f22])).
% 11.68/1.99  
% 11.68/1.99  fof(f24,plain,(
% 11.68/1.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f25,plain,(
% 11.68/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 11.68/1.99  
% 11.68/1.99  fof(f35,plain,(
% 11.68/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.68/1.99    inference(cnf_transformation,[],[f25])).
% 11.68/1.99  
% 11.68/1.99  fof(f54,plain,(
% 11.68/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 11.68/1.99    inference(equality_resolution,[],[f35])).
% 11.68/1.99  
% 11.68/1.99  fof(f42,plain,(
% 11.68/1.99    ( ! [X4,X0] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f30])).
% 11.68/1.99  
% 11.68/1.99  fof(f51,plain,(
% 11.68/1.99    r1_tarski(sK4,sK5)),
% 11.68/1.99    inference(cnf_transformation,[],[f33])).
% 11.68/1.99  
% 11.68/1.99  fof(f6,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 11.68/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f15,plain,(
% 11.68/1.99    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 11.68/1.99    inference(ennf_transformation,[],[f6])).
% 11.68/1.99  
% 11.68/1.99  fof(f16,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 11.68/1.99    inference(flattening,[],[f15])).
% 11.68/1.99  
% 11.68/1.99  fof(f46,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f16])).
% 11.68/1.99  
% 11.68/1.99  fof(f49,plain,(
% 11.68/1.99    v1_relat_1(sK7)),
% 11.68/1.99    inference(cnf_transformation,[],[f33])).
% 11.68/1.99  
% 11.68/1.99  fof(f50,plain,(
% 11.68/1.99    r1_tarski(sK6,sK7)),
% 11.68/1.99    inference(cnf_transformation,[],[f33])).
% 11.68/1.99  
% 11.68/1.99  fof(f52,plain,(
% 11.68/1.99    ~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),
% 11.68/1.99    inference(cnf_transformation,[],[f33])).
% 11.68/1.99  
% 11.68/1.99  fof(f2,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.68/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f10,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.68/1.99    inference(ennf_transformation,[],[f2])).
% 11.68/1.99  
% 11.68/1.99  fof(f11,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.68/1.99    inference(flattening,[],[f10])).
% 11.68/1.99  
% 11.68/1.99  fof(f40,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f11])).
% 11.68/1.99  
% 11.68/1.99  fof(f7,axiom,(
% 11.68/1.99    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 11.68/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f17,plain,(
% 11.68/1.99    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f7])).
% 11.68/1.99  
% 11.68/1.99  fof(f18,plain,(
% 11.68/1.99    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(flattening,[],[f17])).
% 11.68/1.99  
% 11.68/1.99  fof(f47,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f18])).
% 11.68/1.99  
% 11.68/1.99  fof(f44,plain,(
% 11.68/1.99    ( ! [X2,X0,X3] : (v1_relat_1(X0) | k4_tarski(X2,X3) != sK1(X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f30])).
% 11.68/1.99  
% 11.68/1.99  cnf(c_9,plain,
% 11.68/1.99      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_527,plain,
% 11.68/1.99      ( r2_hidden(sK1(X0),X0) = iProver_top
% 11.68/1.99      | v1_relat_1(X0) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_18,negated_conjecture,
% 11.68/1.99      ( v1_relat_1(sK6) ),
% 11.68/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_518,plain,
% 11.68/1.99      ( v1_relat_1(sK6) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_11,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(X0,X1),X1) | ~ v1_relat_1(X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_525,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
% 11.68/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_529,plain,
% 11.68/1.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_978,plain,
% 11.68/1.99      ( k3_xboole_0(k8_relat_1(X0,X1),X1) = k8_relat_1(X0,X1)
% 11.68/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_525,c_529]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1393,plain,
% 11.68/1.99      ( k3_xboole_0(k8_relat_1(X0,sK6),sK6) = k8_relat_1(X0,sK6) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_518,c_978]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4,plain,
% 11.68/1.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_532,plain,
% 11.68/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.68/1.99      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1495,plain,
% 11.68/1.99      ( r2_hidden(X0,k8_relat_1(X1,sK6)) != iProver_top
% 11.68/1.99      | r2_hidden(X0,sK6) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1393,c_532]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2895,plain,
% 11.68/1.99      ( r2_hidden(sK1(k8_relat_1(X0,sK6)),sK6) = iProver_top
% 11.68/1.99      | v1_relat_1(k8_relat_1(X0,sK6)) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_527,c_1495]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_10,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,X1)
% 11.68/1.99      | ~ v1_relat_1(X1)
% 11.68/1.99      | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_526,plain,
% 11.68/1.99      ( k4_tarski(sK2(X0),sK3(X0)) = X0
% 11.68/1.99      | r2_hidden(X0,X1) != iProver_top
% 11.68/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4701,plain,
% 11.68/1.99      ( k4_tarski(sK2(sK1(k8_relat_1(X0,sK6))),sK3(sK1(k8_relat_1(X0,sK6)))) = sK1(k8_relat_1(X0,sK6))
% 11.68/1.99      | v1_relat_1(k8_relat_1(X0,sK6)) = iProver_top
% 11.68/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2895,c_526]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_19,plain,
% 11.68/1.99      ( v1_relat_1(sK6) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_44223,plain,
% 11.68/1.99      ( v1_relat_1(k8_relat_1(X0,sK6)) = iProver_top
% 11.68/1.99      | k4_tarski(sK2(sK1(k8_relat_1(X0,sK6))),sK3(sK1(k8_relat_1(X0,sK6)))) = sK1(k8_relat_1(X0,sK6)) ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_4701,c_19]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_44224,plain,
% 11.68/1.99      ( k4_tarski(sK2(sK1(k8_relat_1(X0,sK6))),sK3(sK1(k8_relat_1(X0,sK6)))) = sK1(k8_relat_1(X0,sK6))
% 11.68/1.99      | v1_relat_1(k8_relat_1(X0,sK6)) = iProver_top ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_44223]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_15,negated_conjecture,
% 11.68/1.99      ( r1_tarski(sK4,sK5) ),
% 11.68/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_521,plain,
% 11.68/1.99      ( r1_tarski(sK4,sK5) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_12,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1)
% 11.68/1.99      | ~ v1_relat_1(X2)
% 11.68/1.99      | k8_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,X2) ),
% 11.68/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_524,plain,
% 11.68/1.99      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
% 11.68/1.99      | r1_tarski(X1,X0) != iProver_top
% 11.68/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1620,plain,
% 11.68/1.99      ( k8_relat_1(sK5,k8_relat_1(sK4,X0)) = k8_relat_1(sK4,X0)
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_521,c_524]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2093,plain,
% 11.68/1.99      ( k8_relat_1(sK5,k8_relat_1(sK4,sK6)) = k8_relat_1(sK4,sK6) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_518,c_1620]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2284,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK4,sK6)) = iProver_top
% 11.68/1.99      | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2093,c_525]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_17,negated_conjecture,
% 11.68/1.99      ( v1_relat_1(sK7) ),
% 11.68/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_20,plain,
% 11.68/1.99      ( v1_relat_1(sK7) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_16,negated_conjecture,
% 11.68/1.99      ( r1_tarski(sK6,sK7) ),
% 11.68/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_21,plain,
% 11.68/1.99      ( r1_tarski(sK6,sK7) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_14,negated_conjecture,
% 11.68/1.99      ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_561,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,k8_relat_1(sK5,sK7))
% 11.68/1.99      | ~ r1_tarski(k8_relat_1(sK4,sK6),X0)
% 11.68/1.99      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_579,plain,
% 11.68/1.99      ( ~ r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7))
% 11.68/1.99      | ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0))
% 11.68/1.99      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_561]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_580,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7)) != iProver_top
% 11.68/1.99      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0)) != iProver_top
% 11.68/1.99      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_582,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7)) != iProver_top
% 11.68/1.99      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) = iProver_top
% 11.68/1.99      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) != iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_580]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_13,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1)
% 11.68/1.99      | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
% 11.68/1.99      | ~ v1_relat_1(X0)
% 11.68/1.99      | ~ v1_relat_1(X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_618,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,sK7)
% 11.68/1.99      | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7))
% 11.68/1.99      | ~ v1_relat_1(X0)
% 11.68/1.99      | ~ v1_relat_1(sK7) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_619,plain,
% 11.68/1.99      ( r1_tarski(X0,sK7) != iProver_top
% 11.68/1.99      | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7)) = iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top
% 11.68/1.99      | v1_relat_1(sK7) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_621,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7)) = iProver_top
% 11.68/1.99      | r1_tarski(sK6,sK7) != iProver_top
% 11.68/1.99      | v1_relat_1(sK7) != iProver_top
% 11.68/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_619]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_973,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(sK4,sK6),sK6) | ~ v1_relat_1(sK6) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_974,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(sK4,sK6),sK6) = iProver_top
% 11.68/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_523,plain,
% 11.68/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.68/1.99      | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1)) = iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top
% 11.68/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2285,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(sK4,sK6),X0) != iProver_top
% 11.68/1.99      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0)) = iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top
% 11.68/1.99      | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2093,c_523]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2289,plain,
% 11.68/1.99      ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) = iProver_top
% 11.68/1.99      | r1_tarski(k8_relat_1(sK4,sK6),sK6) != iProver_top
% 11.68/1.99      | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top
% 11.68/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_2285]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3204,plain,
% 11.68/1.99      ( v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_2284,c_19,c_20,c_21,c_23,c_582,c_621,c_974,c_2289]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_44251,plain,
% 11.68/1.99      ( k4_tarski(sK2(sK1(k8_relat_1(sK4,sK6))),sK3(sK1(k8_relat_1(sK4,sK6)))) = sK1(k8_relat_1(sK4,sK6)) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_44224,c_3204]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8,plain,
% 11.68/1.99      ( v1_relat_1(X0) | k4_tarski(X1,X2) != sK1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1634,plain,
% 11.68/1.99      ( v1_relat_1(k8_relat_1(X0,X1))
% 11.68/1.99      | k4_tarski(X2,X3) != sK1(k8_relat_1(X0,X1)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7366,plain,
% 11.68/1.99      ( v1_relat_1(k8_relat_1(X0,X1))
% 11.68/1.99      | k4_tarski(sK2(sK1(k8_relat_1(X0,X1))),sK3(sK1(k8_relat_1(X0,X1)))) != sK1(k8_relat_1(X0,X1)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_1634]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_18762,plain,
% 11.68/2.00      ( v1_relat_1(k8_relat_1(sK4,sK6))
% 11.68/2.00      | k4_tarski(sK2(sK1(k8_relat_1(sK4,sK6))),sK3(sK1(k8_relat_1(sK4,sK6)))) != sK1(k8_relat_1(sK4,sK6)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_7366]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2288,plain,
% 11.68/2.00      ( ~ r1_tarski(k8_relat_1(sK4,sK6),X0)
% 11.68/2.00      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0))
% 11.68/2.00      | ~ v1_relat_1(X0)
% 11.68/2.00      | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
% 11.68/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2285]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_2290,plain,
% 11.68/2.00      ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6))
% 11.68/2.00      | ~ r1_tarski(k8_relat_1(sK4,sK6),sK6)
% 11.68/2.00      | ~ v1_relat_1(k8_relat_1(sK4,sK6))
% 11.68/2.00      | ~ v1_relat_1(sK6) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_2288]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_620,plain,
% 11.68/2.00      ( r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7))
% 11.68/2.00      | ~ r1_tarski(sK6,sK7)
% 11.68/2.00      | ~ v1_relat_1(sK7)
% 11.68/2.00      | ~ v1_relat_1(sK6) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_618]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(c_581,plain,
% 11.68/2.00      ( ~ r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7))
% 11.68/2.00      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
% 11.68/2.00      | ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) ),
% 11.68/2.00      inference(instantiation,[status(thm)],[c_579]) ).
% 11.68/2.00  
% 11.68/2.00  cnf(contradiction,plain,
% 11.68/2.00      ( $false ),
% 11.68/2.00      inference(minisat,
% 11.68/2.00                [status(thm)],
% 11.68/2.00                [c_44251,c_18762,c_2290,c_973,c_620,c_581,c_14,c_16,c_17,
% 11.68/2.00                 c_18]) ).
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.68/2.00  
% 11.68/2.00  ------                               Statistics
% 11.68/2.00  
% 11.68/2.00  ------ General
% 11.68/2.00  
% 11.68/2.00  abstr_ref_over_cycles:                  0
% 11.68/2.00  abstr_ref_under_cycles:                 0
% 11.68/2.00  gc_basic_clause_elim:                   0
% 11.68/2.00  forced_gc_time:                         0
% 11.68/2.00  parsing_time:                           0.007
% 11.68/2.00  unif_index_cands_time:                  0.
% 11.68/2.00  unif_index_add_time:                    0.
% 11.68/2.00  orderings_time:                         0.
% 11.68/2.00  out_proof_time:                         0.009
% 11.68/2.00  total_time:                             1.307
% 11.68/2.00  num_of_symbols:                         45
% 11.68/2.00  num_of_terms:                           45758
% 11.68/2.00  
% 11.68/2.00  ------ Preprocessing
% 11.68/2.00  
% 11.68/2.00  num_of_splits:                          0
% 11.68/2.00  num_of_split_atoms:                     0
% 11.68/2.00  num_of_reused_defs:                     0
% 11.68/2.00  num_eq_ax_congr_red:                    16
% 11.68/2.00  num_of_sem_filtered_clauses:            1
% 11.68/2.00  num_of_subtypes:                        0
% 11.68/2.00  monotx_restored_types:                  0
% 11.68/2.00  sat_num_of_epr_types:                   0
% 11.68/2.00  sat_num_of_non_cyclic_types:            0
% 11.68/2.00  sat_guarded_non_collapsed_types:        0
% 11.68/2.00  num_pure_diseq_elim:                    0
% 11.68/2.00  simp_replaced_by:                       0
% 11.68/2.00  res_preprocessed:                       72
% 11.68/2.00  prep_upred:                             0
% 11.68/2.00  prep_unflattend:                        0
% 11.68/2.00  smt_new_axioms:                         0
% 11.68/2.00  pred_elim_cands:                        3
% 11.68/2.00  pred_elim:                              0
% 11.68/2.00  pred_elim_cl:                           0
% 11.68/2.00  pred_elim_cycles:                       1
% 11.68/2.00  merged_defs:                            0
% 11.68/2.00  merged_defs_ncl:                        0
% 11.68/2.00  bin_hyper_res:                          0
% 11.68/2.00  prep_cycles:                            3
% 11.68/2.00  pred_elim_time:                         0.
% 11.68/2.00  splitting_time:                         0.
% 11.68/2.00  sem_filter_time:                        0.
% 11.68/2.00  monotx_time:                            0.
% 11.68/2.00  subtype_inf_time:                       0.
% 11.68/2.00  
% 11.68/2.00  ------ Problem properties
% 11.68/2.00  
% 11.68/2.00  clauses:                                19
% 11.68/2.00  conjectures:                            5
% 11.68/2.00  epr:                                    5
% 11.68/2.00  horn:                                   16
% 11.68/2.00  ground:                                 5
% 11.68/2.00  unary:                                  5
% 11.68/2.00  binary:                                 6
% 11.68/2.00  lits:                                   43
% 11.68/2.00  lits_eq:                                7
% 11.68/2.00  fd_pure:                                0
% 11.68/2.00  fd_pseudo:                              0
% 11.68/2.00  fd_cond:                                0
% 11.68/2.00  fd_pseudo_cond:                         3
% 11.68/2.00  ac_symbols:                             0
% 11.68/2.00  
% 11.68/2.00  ------ Propositional Solver
% 11.68/2.00  
% 11.68/2.00  prop_solver_calls:                      29
% 11.68/2.00  prop_fast_solver_calls:                 1516
% 11.68/2.00  smt_solver_calls:                       0
% 11.68/2.00  smt_fast_solver_calls:                  0
% 11.68/2.00  prop_num_of_clauses:                    16172
% 11.68/2.00  prop_preprocess_simplified:             24369
% 11.68/2.00  prop_fo_subsumed:                       71
% 11.68/2.00  prop_solver_time:                       0.
% 11.68/2.00  smt_solver_time:                        0.
% 11.68/2.00  smt_fast_solver_time:                   0.
% 11.68/2.00  prop_fast_solver_time:                  0.
% 11.68/2.00  prop_unsat_core_time:                   0.001
% 11.68/2.00  
% 11.68/2.00  ------ QBF
% 11.68/2.00  
% 11.68/2.00  qbf_q_res:                              0
% 11.68/2.00  qbf_num_tautologies:                    0
% 11.68/2.00  qbf_prep_cycles:                        0
% 11.68/2.00  
% 11.68/2.00  ------ BMC1
% 11.68/2.00  
% 11.68/2.00  bmc1_current_bound:                     -1
% 11.68/2.00  bmc1_last_solved_bound:                 -1
% 11.68/2.00  bmc1_unsat_core_size:                   -1
% 11.68/2.00  bmc1_unsat_core_parents_size:           -1
% 11.68/2.00  bmc1_merge_next_fun:                    0
% 11.68/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.68/2.00  
% 11.68/2.00  ------ Instantiation
% 11.68/2.00  
% 11.68/2.00  inst_num_of_clauses:                    3271
% 11.68/2.00  inst_num_in_passive:                    677
% 11.68/2.00  inst_num_in_active:                     1659
% 11.68/2.00  inst_num_in_unprocessed:                935
% 11.68/2.00  inst_num_of_loops:                      1780
% 11.68/2.00  inst_num_of_learning_restarts:          0
% 11.68/2.00  inst_num_moves_active_passive:          117
% 11.68/2.00  inst_lit_activity:                      0
% 11.68/2.00  inst_lit_activity_moves:                0
% 11.68/2.00  inst_num_tautologies:                   0
% 11.68/2.00  inst_num_prop_implied:                  0
% 11.68/2.00  inst_num_existing_simplified:           0
% 11.68/2.00  inst_num_eq_res_simplified:             0
% 11.68/2.00  inst_num_child_elim:                    0
% 11.68/2.00  inst_num_of_dismatching_blockings:      7511
% 11.68/2.00  inst_num_of_non_proper_insts:           7655
% 11.68/2.00  inst_num_of_duplicates:                 0
% 11.68/2.00  inst_inst_num_from_inst_to_res:         0
% 11.68/2.00  inst_dismatching_checking_time:         0.
% 11.68/2.00  
% 11.68/2.00  ------ Resolution
% 11.68/2.00  
% 11.68/2.00  res_num_of_clauses:                     0
% 11.68/2.00  res_num_in_passive:                     0
% 11.68/2.00  res_num_in_active:                      0
% 11.68/2.00  res_num_of_loops:                       75
% 11.68/2.00  res_forward_subset_subsumed:            332
% 11.68/2.00  res_backward_subset_subsumed:           0
% 11.68/2.00  res_forward_subsumed:                   0
% 11.68/2.00  res_backward_subsumed:                  0
% 11.68/2.00  res_forward_subsumption_resolution:     0
% 11.68/2.00  res_backward_subsumption_resolution:    0
% 11.68/2.00  res_clause_to_clause_subsumption:       20485
% 11.68/2.00  res_orphan_elimination:                 0
% 11.68/2.00  res_tautology_del:                      1336
% 11.68/2.00  res_num_eq_res_simplified:              0
% 11.68/2.00  res_num_sel_changes:                    0
% 11.68/2.00  res_moves_from_active_to_pass:          0
% 11.68/2.00  
% 11.68/2.00  ------ Superposition
% 11.68/2.00  
% 11.68/2.00  sup_time_total:                         0.
% 11.68/2.00  sup_time_generating:                    0.
% 11.68/2.00  sup_time_sim_full:                      0.
% 11.68/2.00  sup_time_sim_immed:                     0.
% 11.68/2.00  
% 11.68/2.00  sup_num_of_clauses:                     1871
% 11.68/2.00  sup_num_in_active:                      333
% 11.68/2.00  sup_num_in_passive:                     1538
% 11.68/2.00  sup_num_of_loops:                       354
% 11.68/2.00  sup_fw_superposition:                   1791
% 11.68/2.00  sup_bw_superposition:                   1992
% 11.68/2.00  sup_immediate_simplified:               1168
% 11.68/2.00  sup_given_eliminated:                   1
% 11.68/2.00  comparisons_done:                       0
% 11.68/2.00  comparisons_avoided:                    44
% 11.68/2.00  
% 11.68/2.00  ------ Simplifications
% 11.68/2.00  
% 11.68/2.00  
% 11.68/2.00  sim_fw_subset_subsumed:                 38
% 11.68/2.00  sim_bw_subset_subsumed:                 19
% 11.68/2.00  sim_fw_subsumed:                        660
% 11.68/2.00  sim_bw_subsumed:                        67
% 11.68/2.00  sim_fw_subsumption_res:                 0
% 11.68/2.00  sim_bw_subsumption_res:                 0
% 11.68/2.00  sim_tautology_del:                      357
% 11.68/2.00  sim_eq_tautology_del:                   16
% 11.68/2.00  sim_eq_res_simp:                        34
% 11.68/2.00  sim_fw_demodulated:                     348
% 11.68/2.00  sim_bw_demodulated:                     0
% 11.68/2.00  sim_light_normalised:                   448
% 11.68/2.00  sim_joinable_taut:                      0
% 11.68/2.00  sim_joinable_simp:                      0
% 11.68/2.00  sim_ac_normalised:                      0
% 11.68/2.00  sim_smt_subsumption:                    0
% 11.68/2.00  
%------------------------------------------------------------------------------
