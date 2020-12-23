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
% DateTime   : Thu Dec  3 11:23:27 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 233 expanded)
%              Number of clauses        :   41 (  76 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  233 ( 928 expanded)
%              Number of equality atoms :   80 ( 213 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k1_xboole_0 != sK2
      & r1_xboole_0(sK3,sK4)
      & r1_tarski(sK2,sK4)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k1_xboole_0 != sK2
    & r1_xboole_0(sK3,sK4)
    & r1_tarski(sK2,sK4)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f27])).

fof(f44,plain,(
    r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
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
    inference(rectify,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_514,plain,
    ( r1_tarski(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_521,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_173,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_174,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_511,plain,
    ( r2_hidden(X0,k3_xboole_0(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_11962,plain,
    ( k4_xboole_0(k3_xboole_0(sK3,sK4),X0) = X1
    | r2_hidden(sK0(k3_xboole_0(sK3,sK4),X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_521,c_511])).

cnf(c_11957,plain,
    ( k4_xboole_0(X0,X1) = k3_xboole_0(sK3,sK4)
    | r2_hidden(sK0(X0,X1,k3_xboole_0(sK3,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_521,c_511])).

cnf(c_14477,plain,
    ( k4_xboole_0(k3_xboole_0(sK3,sK4),X0) = k3_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_11957,c_511])).

cnf(c_14534,plain,
    ( k3_xboole_0(sK3,sK4) = X0
    | r2_hidden(sK0(k3_xboole_0(sK3,sK4),X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11962,c_14477])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_519,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1916,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_519])).

cnf(c_14473,plain,
    ( k4_xboole_0(X0,X1) = k3_xboole_0(sK3,sK4)
    | r2_hidden(sK0(X0,X1,k3_xboole_0(sK3,sK4)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11957,c_1916])).

cnf(c_14577,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_11957,c_14473])).

cnf(c_14624,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14577,c_511])).

cnf(c_14815,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_14624])).

cnf(c_14869,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14534,c_14815])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_516,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_819,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_10])).

cnf(c_931,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_6,c_819])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_517,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1233,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_xboole_0(X0,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_517])).

cnf(c_1895,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_516,c_1233])).

cnf(c_18885,plain,
    ( r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14869,c_1895])).

cnf(c_29019,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_514,c_18885])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_618,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_619,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29019,c_619,c_14,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.82/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/1.51  
% 7.82/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.51  
% 7.82/1.51  ------  iProver source info
% 7.82/1.51  
% 7.82/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.51  git: non_committed_changes: false
% 7.82/1.51  git: last_make_outside_of_git: false
% 7.82/1.51  
% 7.82/1.51  ------ 
% 7.82/1.51  
% 7.82/1.51  ------ Input Options
% 7.82/1.51  
% 7.82/1.51  --out_options                           all
% 7.82/1.51  --tptp_safe_out                         true
% 7.82/1.51  --problem_path                          ""
% 7.82/1.51  --include_path                          ""
% 7.82/1.51  --clausifier                            res/vclausify_rel
% 7.82/1.51  --clausifier_options                    --mode clausify
% 7.82/1.51  --stdin                                 false
% 7.82/1.51  --stats_out                             all
% 7.82/1.51  
% 7.82/1.51  ------ General Options
% 7.82/1.51  
% 7.82/1.51  --fof                                   false
% 7.82/1.51  --time_out_real                         305.
% 7.82/1.51  --time_out_virtual                      -1.
% 7.82/1.51  --symbol_type_check                     false
% 7.82/1.51  --clausify_out                          false
% 7.82/1.51  --sig_cnt_out                           false
% 7.82/1.51  --trig_cnt_out                          false
% 7.82/1.51  --trig_cnt_out_tolerance                1.
% 7.82/1.51  --trig_cnt_out_sk_spl                   false
% 7.82/1.51  --abstr_cl_out                          false
% 7.82/1.51  
% 7.82/1.51  ------ Global Options
% 7.82/1.51  
% 7.82/1.51  --schedule                              default
% 7.82/1.51  --add_important_lit                     false
% 7.82/1.51  --prop_solver_per_cl                    1000
% 7.82/1.51  --min_unsat_core                        false
% 7.82/1.51  --soft_assumptions                      false
% 7.82/1.51  --soft_lemma_size                       3
% 7.82/1.51  --prop_impl_unit_size                   0
% 7.82/1.51  --prop_impl_unit                        []
% 7.82/1.51  --share_sel_clauses                     true
% 7.82/1.51  --reset_solvers                         false
% 7.82/1.51  --bc_imp_inh                            [conj_cone]
% 7.82/1.51  --conj_cone_tolerance                   3.
% 7.82/1.51  --extra_neg_conj                        none
% 7.82/1.51  --large_theory_mode                     true
% 7.82/1.51  --prolific_symb_bound                   200
% 7.82/1.51  --lt_threshold                          2000
% 7.82/1.51  --clause_weak_htbl                      true
% 7.82/1.51  --gc_record_bc_elim                     false
% 7.82/1.51  
% 7.82/1.51  ------ Preprocessing Options
% 7.82/1.51  
% 7.82/1.51  --preprocessing_flag                    true
% 7.82/1.51  --time_out_prep_mult                    0.1
% 7.82/1.51  --splitting_mode                        input
% 7.82/1.51  --splitting_grd                         true
% 7.82/1.51  --splitting_cvd                         false
% 7.82/1.51  --splitting_cvd_svl                     false
% 7.82/1.51  --splitting_nvd                         32
% 7.82/1.51  --sub_typing                            true
% 7.82/1.51  --prep_gs_sim                           true
% 7.82/1.51  --prep_unflatten                        true
% 7.82/1.51  --prep_res_sim                          true
% 7.82/1.51  --prep_upred                            true
% 7.82/1.51  --prep_sem_filter                       exhaustive
% 7.82/1.51  --prep_sem_filter_out                   false
% 7.82/1.51  --pred_elim                             true
% 7.82/1.51  --res_sim_input                         true
% 7.82/1.51  --eq_ax_congr_red                       true
% 7.82/1.51  --pure_diseq_elim                       true
% 7.82/1.51  --brand_transform                       false
% 7.82/1.51  --non_eq_to_eq                          false
% 7.82/1.51  --prep_def_merge                        true
% 7.82/1.51  --prep_def_merge_prop_impl              false
% 7.82/1.51  --prep_def_merge_mbd                    true
% 7.82/1.51  --prep_def_merge_tr_red                 false
% 7.82/1.51  --prep_def_merge_tr_cl                  false
% 7.82/1.51  --smt_preprocessing                     true
% 7.82/1.51  --smt_ac_axioms                         fast
% 7.82/1.51  --preprocessed_out                      false
% 7.82/1.51  --preprocessed_stats                    false
% 7.82/1.51  
% 7.82/1.51  ------ Abstraction refinement Options
% 7.82/1.51  
% 7.82/1.51  --abstr_ref                             []
% 7.82/1.51  --abstr_ref_prep                        false
% 7.82/1.51  --abstr_ref_until_sat                   false
% 7.82/1.51  --abstr_ref_sig_restrict                funpre
% 7.82/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.51  --abstr_ref_under                       []
% 7.82/1.51  
% 7.82/1.51  ------ SAT Options
% 7.82/1.51  
% 7.82/1.51  --sat_mode                              false
% 7.82/1.51  --sat_fm_restart_options                ""
% 7.82/1.51  --sat_gr_def                            false
% 7.82/1.51  --sat_epr_types                         true
% 7.82/1.51  --sat_non_cyclic_types                  false
% 7.82/1.51  --sat_finite_models                     false
% 7.82/1.51  --sat_fm_lemmas                         false
% 7.82/1.51  --sat_fm_prep                           false
% 7.82/1.51  --sat_fm_uc_incr                        true
% 7.82/1.51  --sat_out_model                         small
% 7.82/1.51  --sat_out_clauses                       false
% 7.82/1.51  
% 7.82/1.51  ------ QBF Options
% 7.82/1.51  
% 7.82/1.51  --qbf_mode                              false
% 7.82/1.51  --qbf_elim_univ                         false
% 7.82/1.51  --qbf_dom_inst                          none
% 7.82/1.51  --qbf_dom_pre_inst                      false
% 7.82/1.51  --qbf_sk_in                             false
% 7.82/1.51  --qbf_pred_elim                         true
% 7.82/1.51  --qbf_split                             512
% 7.82/1.51  
% 7.82/1.51  ------ BMC1 Options
% 7.82/1.51  
% 7.82/1.51  --bmc1_incremental                      false
% 7.82/1.51  --bmc1_axioms                           reachable_all
% 7.82/1.51  --bmc1_min_bound                        0
% 7.82/1.51  --bmc1_max_bound                        -1
% 7.82/1.51  --bmc1_max_bound_default                -1
% 7.82/1.51  --bmc1_symbol_reachability              true
% 7.82/1.51  --bmc1_property_lemmas                  false
% 7.82/1.51  --bmc1_k_induction                      false
% 7.82/1.51  --bmc1_non_equiv_states                 false
% 7.82/1.51  --bmc1_deadlock                         false
% 7.82/1.51  --bmc1_ucm                              false
% 7.82/1.51  --bmc1_add_unsat_core                   none
% 7.82/1.51  --bmc1_unsat_core_children              false
% 7.82/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.51  --bmc1_out_stat                         full
% 7.82/1.51  --bmc1_ground_init                      false
% 7.82/1.51  --bmc1_pre_inst_next_state              false
% 7.82/1.51  --bmc1_pre_inst_state                   false
% 7.82/1.51  --bmc1_pre_inst_reach_state             false
% 7.82/1.51  --bmc1_out_unsat_core                   false
% 7.82/1.51  --bmc1_aig_witness_out                  false
% 7.82/1.51  --bmc1_verbose                          false
% 7.82/1.51  --bmc1_dump_clauses_tptp                false
% 7.82/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.51  --bmc1_dump_file                        -
% 7.82/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.51  --bmc1_ucm_extend_mode                  1
% 7.82/1.51  --bmc1_ucm_init_mode                    2
% 7.82/1.51  --bmc1_ucm_cone_mode                    none
% 7.82/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.51  --bmc1_ucm_relax_model                  4
% 7.82/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.51  --bmc1_ucm_layered_model                none
% 7.82/1.51  --bmc1_ucm_max_lemma_size               10
% 7.82/1.51  
% 7.82/1.51  ------ AIG Options
% 7.82/1.51  
% 7.82/1.51  --aig_mode                              false
% 7.82/1.51  
% 7.82/1.51  ------ Instantiation Options
% 7.82/1.51  
% 7.82/1.51  --instantiation_flag                    true
% 7.82/1.51  --inst_sos_flag                         false
% 7.82/1.51  --inst_sos_phase                        true
% 7.82/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.51  --inst_lit_sel_side                     num_symb
% 7.82/1.51  --inst_solver_per_active                1400
% 7.82/1.51  --inst_solver_calls_frac                1.
% 7.82/1.51  --inst_passive_queue_type               priority_queues
% 7.82/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.51  --inst_passive_queues_freq              [25;2]
% 7.82/1.51  --inst_dismatching                      true
% 7.82/1.51  --inst_eager_unprocessed_to_passive     true
% 7.82/1.51  --inst_prop_sim_given                   true
% 7.82/1.51  --inst_prop_sim_new                     false
% 7.82/1.51  --inst_subs_new                         false
% 7.82/1.51  --inst_eq_res_simp                      false
% 7.82/1.51  --inst_subs_given                       false
% 7.82/1.51  --inst_orphan_elimination               true
% 7.82/1.51  --inst_learning_loop_flag               true
% 7.82/1.51  --inst_learning_start                   3000
% 7.82/1.51  --inst_learning_factor                  2
% 7.82/1.51  --inst_start_prop_sim_after_learn       3
% 7.82/1.51  --inst_sel_renew                        solver
% 7.82/1.51  --inst_lit_activity_flag                true
% 7.82/1.51  --inst_restr_to_given                   false
% 7.82/1.51  --inst_activity_threshold               500
% 7.82/1.51  --inst_out_proof                        true
% 7.82/1.51  
% 7.82/1.51  ------ Resolution Options
% 7.82/1.51  
% 7.82/1.51  --resolution_flag                       true
% 7.82/1.51  --res_lit_sel                           adaptive
% 7.82/1.51  --res_lit_sel_side                      none
% 7.82/1.51  --res_ordering                          kbo
% 7.82/1.51  --res_to_prop_solver                    active
% 7.82/1.51  --res_prop_simpl_new                    false
% 7.82/1.51  --res_prop_simpl_given                  true
% 7.82/1.51  --res_passive_queue_type                priority_queues
% 7.82/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.51  --res_passive_queues_freq               [15;5]
% 7.82/1.51  --res_forward_subs                      full
% 7.82/1.51  --res_backward_subs                     full
% 7.82/1.51  --res_forward_subs_resolution           true
% 7.82/1.51  --res_backward_subs_resolution          true
% 7.82/1.51  --res_orphan_elimination                true
% 7.82/1.51  --res_time_limit                        2.
% 7.82/1.51  --res_out_proof                         true
% 7.82/1.51  
% 7.82/1.51  ------ Superposition Options
% 7.82/1.51  
% 7.82/1.51  --superposition_flag                    true
% 7.82/1.51  --sup_passive_queue_type                priority_queues
% 7.82/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.51  --demod_completeness_check              fast
% 7.82/1.51  --demod_use_ground                      true
% 7.82/1.51  --sup_to_prop_solver                    passive
% 7.82/1.51  --sup_prop_simpl_new                    true
% 7.82/1.51  --sup_prop_simpl_given                  true
% 7.82/1.51  --sup_fun_splitting                     false
% 7.82/1.51  --sup_smt_interval                      50000
% 7.82/1.51  
% 7.82/1.51  ------ Superposition Simplification Setup
% 7.82/1.51  
% 7.82/1.51  --sup_indices_passive                   []
% 7.82/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.51  --sup_full_bw                           [BwDemod]
% 7.82/1.51  --sup_immed_triv                        [TrivRules]
% 7.82/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.51  --sup_immed_bw_main                     []
% 7.82/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.51  
% 7.82/1.51  ------ Combination Options
% 7.82/1.51  
% 7.82/1.51  --comb_res_mult                         3
% 7.82/1.51  --comb_sup_mult                         2
% 7.82/1.51  --comb_inst_mult                        10
% 7.82/1.51  
% 7.82/1.51  ------ Debug Options
% 7.82/1.51  
% 7.82/1.51  --dbg_backtrace                         false
% 7.82/1.51  --dbg_dump_prop_clauses                 false
% 7.82/1.51  --dbg_dump_prop_clauses_file            -
% 7.82/1.51  --dbg_out_stat                          false
% 7.82/1.51  ------ Parsing...
% 7.82/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.51  
% 7.82/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.82/1.51  
% 7.82/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.51  
% 7.82/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.51  ------ Proving...
% 7.82/1.51  ------ Problem Properties 
% 7.82/1.51  
% 7.82/1.51  
% 7.82/1.51  clauses                                 17
% 7.82/1.51  conjectures                             3
% 7.82/1.51  EPR                                     4
% 7.82/1.51  Horn                                    13
% 7.82/1.51  unary                                   7
% 7.82/1.51  binary                                  5
% 7.82/1.51  lits                                    33
% 7.82/1.51  lits eq                                 8
% 7.82/1.51  fd_pure                                 0
% 7.82/1.51  fd_pseudo                               0
% 7.82/1.51  fd_cond                                 1
% 7.82/1.51  fd_pseudo_cond                          3
% 7.82/1.51  AC symbols                              0
% 7.82/1.51  
% 7.82/1.51  ------ Schedule dynamic 5 is on 
% 7.82/1.51  
% 7.82/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.82/1.51  
% 7.82/1.51  
% 7.82/1.51  ------ 
% 7.82/1.51  Current options:
% 7.82/1.51  ------ 
% 7.82/1.51  
% 7.82/1.51  ------ Input Options
% 7.82/1.51  
% 7.82/1.51  --out_options                           all
% 7.82/1.51  --tptp_safe_out                         true
% 7.82/1.51  --problem_path                          ""
% 7.82/1.51  --include_path                          ""
% 7.82/1.51  --clausifier                            res/vclausify_rel
% 7.82/1.51  --clausifier_options                    --mode clausify
% 7.82/1.51  --stdin                                 false
% 7.82/1.51  --stats_out                             all
% 7.82/1.51  
% 7.82/1.51  ------ General Options
% 7.82/1.51  
% 7.82/1.51  --fof                                   false
% 7.82/1.51  --time_out_real                         305.
% 7.82/1.51  --time_out_virtual                      -1.
% 7.82/1.51  --symbol_type_check                     false
% 7.82/1.51  --clausify_out                          false
% 7.82/1.51  --sig_cnt_out                           false
% 7.82/1.51  --trig_cnt_out                          false
% 7.82/1.51  --trig_cnt_out_tolerance                1.
% 7.82/1.51  --trig_cnt_out_sk_spl                   false
% 7.82/1.51  --abstr_cl_out                          false
% 7.82/1.51  
% 7.82/1.51  ------ Global Options
% 7.82/1.51  
% 7.82/1.51  --schedule                              default
% 7.82/1.51  --add_important_lit                     false
% 7.82/1.51  --prop_solver_per_cl                    1000
% 7.82/1.51  --min_unsat_core                        false
% 7.82/1.51  --soft_assumptions                      false
% 7.82/1.51  --soft_lemma_size                       3
% 7.82/1.51  --prop_impl_unit_size                   0
% 7.82/1.51  --prop_impl_unit                        []
% 7.82/1.51  --share_sel_clauses                     true
% 7.82/1.51  --reset_solvers                         false
% 7.82/1.51  --bc_imp_inh                            [conj_cone]
% 7.82/1.51  --conj_cone_tolerance                   3.
% 7.82/1.51  --extra_neg_conj                        none
% 7.82/1.51  --large_theory_mode                     true
% 7.82/1.51  --prolific_symb_bound                   200
% 7.82/1.51  --lt_threshold                          2000
% 7.82/1.51  --clause_weak_htbl                      true
% 7.82/1.51  --gc_record_bc_elim                     false
% 7.82/1.51  
% 7.82/1.51  ------ Preprocessing Options
% 7.82/1.51  
% 7.82/1.51  --preprocessing_flag                    true
% 7.82/1.51  --time_out_prep_mult                    0.1
% 7.82/1.51  --splitting_mode                        input
% 7.82/1.51  --splitting_grd                         true
% 7.82/1.51  --splitting_cvd                         false
% 7.82/1.51  --splitting_cvd_svl                     false
% 7.82/1.51  --splitting_nvd                         32
% 7.82/1.51  --sub_typing                            true
% 7.82/1.51  --prep_gs_sim                           true
% 7.82/1.51  --prep_unflatten                        true
% 7.82/1.51  --prep_res_sim                          true
% 7.82/1.51  --prep_upred                            true
% 7.82/1.51  --prep_sem_filter                       exhaustive
% 7.82/1.51  --prep_sem_filter_out                   false
% 7.82/1.51  --pred_elim                             true
% 7.82/1.51  --res_sim_input                         true
% 7.82/1.51  --eq_ax_congr_red                       true
% 7.82/1.51  --pure_diseq_elim                       true
% 7.82/1.51  --brand_transform                       false
% 7.82/1.51  --non_eq_to_eq                          false
% 7.82/1.51  --prep_def_merge                        true
% 7.82/1.51  --prep_def_merge_prop_impl              false
% 7.82/1.51  --prep_def_merge_mbd                    true
% 7.82/1.51  --prep_def_merge_tr_red                 false
% 7.82/1.51  --prep_def_merge_tr_cl                  false
% 7.82/1.51  --smt_preprocessing                     true
% 7.82/1.51  --smt_ac_axioms                         fast
% 7.82/1.51  --preprocessed_out                      false
% 7.82/1.51  --preprocessed_stats                    false
% 7.82/1.51  
% 7.82/1.51  ------ Abstraction refinement Options
% 7.82/1.51  
% 7.82/1.51  --abstr_ref                             []
% 7.82/1.51  --abstr_ref_prep                        false
% 7.82/1.51  --abstr_ref_until_sat                   false
% 7.82/1.51  --abstr_ref_sig_restrict                funpre
% 7.82/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.51  --abstr_ref_under                       []
% 7.82/1.51  
% 7.82/1.51  ------ SAT Options
% 7.82/1.51  
% 7.82/1.51  --sat_mode                              false
% 7.82/1.51  --sat_fm_restart_options                ""
% 7.82/1.51  --sat_gr_def                            false
% 7.82/1.51  --sat_epr_types                         true
% 7.82/1.51  --sat_non_cyclic_types                  false
% 7.82/1.51  --sat_finite_models                     false
% 7.82/1.51  --sat_fm_lemmas                         false
% 7.82/1.51  --sat_fm_prep                           false
% 7.82/1.51  --sat_fm_uc_incr                        true
% 7.82/1.51  --sat_out_model                         small
% 7.82/1.51  --sat_out_clauses                       false
% 7.82/1.51  
% 7.82/1.51  ------ QBF Options
% 7.82/1.51  
% 7.82/1.51  --qbf_mode                              false
% 7.82/1.51  --qbf_elim_univ                         false
% 7.82/1.51  --qbf_dom_inst                          none
% 7.82/1.51  --qbf_dom_pre_inst                      false
% 7.82/1.51  --qbf_sk_in                             false
% 7.82/1.51  --qbf_pred_elim                         true
% 7.82/1.51  --qbf_split                             512
% 7.82/1.51  
% 7.82/1.51  ------ BMC1 Options
% 7.82/1.51  
% 7.82/1.51  --bmc1_incremental                      false
% 7.82/1.51  --bmc1_axioms                           reachable_all
% 7.82/1.51  --bmc1_min_bound                        0
% 7.82/1.51  --bmc1_max_bound                        -1
% 7.82/1.51  --bmc1_max_bound_default                -1
% 7.82/1.51  --bmc1_symbol_reachability              true
% 7.82/1.51  --bmc1_property_lemmas                  false
% 7.82/1.51  --bmc1_k_induction                      false
% 7.82/1.51  --bmc1_non_equiv_states                 false
% 7.82/1.51  --bmc1_deadlock                         false
% 7.82/1.51  --bmc1_ucm                              false
% 7.82/1.51  --bmc1_add_unsat_core                   none
% 7.82/1.51  --bmc1_unsat_core_children              false
% 7.82/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.51  --bmc1_out_stat                         full
% 7.82/1.51  --bmc1_ground_init                      false
% 7.82/1.51  --bmc1_pre_inst_next_state              false
% 7.82/1.51  --bmc1_pre_inst_state                   false
% 7.82/1.51  --bmc1_pre_inst_reach_state             false
% 7.82/1.51  --bmc1_out_unsat_core                   false
% 7.82/1.51  --bmc1_aig_witness_out                  false
% 7.82/1.51  --bmc1_verbose                          false
% 7.82/1.51  --bmc1_dump_clauses_tptp                false
% 7.82/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.51  --bmc1_dump_file                        -
% 7.82/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.51  --bmc1_ucm_extend_mode                  1
% 7.82/1.51  --bmc1_ucm_init_mode                    2
% 7.82/1.51  --bmc1_ucm_cone_mode                    none
% 7.82/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.51  --bmc1_ucm_relax_model                  4
% 7.82/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.51  --bmc1_ucm_layered_model                none
% 7.82/1.51  --bmc1_ucm_max_lemma_size               10
% 7.82/1.51  
% 7.82/1.51  ------ AIG Options
% 7.82/1.51  
% 7.82/1.51  --aig_mode                              false
% 7.82/1.51  
% 7.82/1.51  ------ Instantiation Options
% 7.82/1.51  
% 7.82/1.51  --instantiation_flag                    true
% 7.82/1.51  --inst_sos_flag                         false
% 7.82/1.51  --inst_sos_phase                        true
% 7.82/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.51  --inst_lit_sel_side                     none
% 7.82/1.51  --inst_solver_per_active                1400
% 7.82/1.51  --inst_solver_calls_frac                1.
% 7.82/1.51  --inst_passive_queue_type               priority_queues
% 7.82/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.51  --inst_passive_queues_freq              [25;2]
% 7.82/1.51  --inst_dismatching                      true
% 7.82/1.51  --inst_eager_unprocessed_to_passive     true
% 7.82/1.51  --inst_prop_sim_given                   true
% 7.82/1.51  --inst_prop_sim_new                     false
% 7.82/1.51  --inst_subs_new                         false
% 7.82/1.51  --inst_eq_res_simp                      false
% 7.82/1.51  --inst_subs_given                       false
% 7.82/1.51  --inst_orphan_elimination               true
% 7.82/1.51  --inst_learning_loop_flag               true
% 7.82/1.51  --inst_learning_start                   3000
% 7.82/1.51  --inst_learning_factor                  2
% 7.82/1.51  --inst_start_prop_sim_after_learn       3
% 7.82/1.51  --inst_sel_renew                        solver
% 7.82/1.51  --inst_lit_activity_flag                true
% 7.82/1.51  --inst_restr_to_given                   false
% 7.82/1.51  --inst_activity_threshold               500
% 7.82/1.51  --inst_out_proof                        true
% 7.82/1.51  
% 7.82/1.51  ------ Resolution Options
% 7.82/1.51  
% 7.82/1.51  --resolution_flag                       false
% 7.82/1.51  --res_lit_sel                           adaptive
% 7.82/1.51  --res_lit_sel_side                      none
% 7.82/1.51  --res_ordering                          kbo
% 7.82/1.51  --res_to_prop_solver                    active
% 7.82/1.51  --res_prop_simpl_new                    false
% 7.82/1.51  --res_prop_simpl_given                  true
% 7.82/1.51  --res_passive_queue_type                priority_queues
% 7.82/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.51  --res_passive_queues_freq               [15;5]
% 7.82/1.51  --res_forward_subs                      full
% 7.82/1.51  --res_backward_subs                     full
% 7.82/1.51  --res_forward_subs_resolution           true
% 7.82/1.51  --res_backward_subs_resolution          true
% 7.82/1.51  --res_orphan_elimination                true
% 7.82/1.51  --res_time_limit                        2.
% 7.82/1.51  --res_out_proof                         true
% 7.82/1.51  
% 7.82/1.51  ------ Superposition Options
% 7.82/1.51  
% 7.82/1.51  --superposition_flag                    true
% 7.82/1.51  --sup_passive_queue_type                priority_queues
% 7.82/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.51  --demod_completeness_check              fast
% 7.82/1.51  --demod_use_ground                      true
% 7.82/1.51  --sup_to_prop_solver                    passive
% 7.82/1.51  --sup_prop_simpl_new                    true
% 7.82/1.51  --sup_prop_simpl_given                  true
% 7.82/1.51  --sup_fun_splitting                     false
% 7.82/1.51  --sup_smt_interval                      50000
% 7.82/1.51  
% 7.82/1.51  ------ Superposition Simplification Setup
% 7.82/1.51  
% 7.82/1.51  --sup_indices_passive                   []
% 7.82/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.51  --sup_full_bw                           [BwDemod]
% 7.82/1.51  --sup_immed_triv                        [TrivRules]
% 7.82/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.51  --sup_immed_bw_main                     []
% 7.82/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.51  
% 7.82/1.51  ------ Combination Options
% 7.82/1.51  
% 7.82/1.51  --comb_res_mult                         3
% 7.82/1.51  --comb_sup_mult                         2
% 7.82/1.51  --comb_inst_mult                        10
% 7.82/1.51  
% 7.82/1.51  ------ Debug Options
% 7.82/1.51  
% 7.82/1.51  --dbg_backtrace                         false
% 7.82/1.51  --dbg_dump_prop_clauses                 false
% 7.82/1.51  --dbg_dump_prop_clauses_file            -
% 7.82/1.51  --dbg_out_stat                          false
% 7.82/1.51  
% 7.82/1.51  
% 7.82/1.51  
% 7.82/1.51  
% 7.82/1.51  ------ Proving...
% 7.82/1.51  
% 7.82/1.51  
% 7.82/1.51  % SZS status Theorem for theBenchmark.p
% 7.82/1.51  
% 7.82/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.51  
% 7.82/1.51  fof(f9,conjecture,(
% 7.82/1.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 7.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.51  
% 7.82/1.51  fof(f10,negated_conjecture,(
% 7.82/1.51    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 7.82/1.51    inference(negated_conjecture,[],[f9])).
% 7.82/1.51  
% 7.82/1.51  fof(f18,plain,(
% 7.82/1.51    ? [X0,X1,X2] : (k1_xboole_0 != X0 & (r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)))),
% 7.82/1.51    inference(ennf_transformation,[],[f10])).
% 7.82/1.51  
% 7.82/1.51  fof(f19,plain,(
% 7.82/1.51    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1))),
% 7.82/1.51    inference(flattening,[],[f18])).
% 7.82/1.51  
% 7.82/1.51  fof(f27,plain,(
% 7.82/1.51    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => (k1_xboole_0 != sK2 & r1_xboole_0(sK3,sK4) & r1_tarski(sK2,sK4) & r1_tarski(sK2,sK3))),
% 7.82/1.51    introduced(choice_axiom,[])).
% 7.82/1.51  
% 7.82/1.51  fof(f28,plain,(
% 7.82/1.51    k1_xboole_0 != sK2 & r1_xboole_0(sK3,sK4) & r1_tarski(sK2,sK4) & r1_tarski(sK2,sK3)),
% 7.82/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f27])).
% 7.82/1.51  
% 7.82/1.51  fof(f44,plain,(
% 7.82/1.51    r1_tarski(sK2,sK4)),
% 7.82/1.51    inference(cnf_transformation,[],[f28])).
% 7.82/1.51  
% 7.82/1.51  fof(f1,axiom,(
% 7.82/1.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.51  
% 7.82/1.51  fof(f20,plain,(
% 7.82/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.82/1.51    inference(nnf_transformation,[],[f1])).
% 7.82/1.51  
% 7.82/1.51  fof(f21,plain,(
% 7.82/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.82/1.51    inference(flattening,[],[f20])).
% 7.82/1.51  
% 7.82/1.51  fof(f22,plain,(
% 7.82/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.82/1.51    inference(rectify,[],[f21])).
% 7.82/1.51  
% 7.82/1.51  fof(f23,plain,(
% 7.82/1.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.82/1.51    introduced(choice_axiom,[])).
% 7.82/1.51  
% 7.82/1.51  fof(f24,plain,(
% 7.82/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.82/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 7.82/1.51  
% 7.82/1.51  fof(f32,plain,(
% 7.82/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.82/1.51    inference(cnf_transformation,[],[f24])).
% 7.82/1.51  
% 7.82/1.51  fof(f3,axiom,(
% 7.82/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.51  
% 7.82/1.51  fof(f12,plain,(
% 7.82/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.82/1.51    inference(rectify,[],[f3])).
% 7.82/1.51  
% 7.82/1.51  fof(f13,plain,(
% 7.82/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.82/1.51    inference(ennf_transformation,[],[f12])).
% 7.82/1.51  
% 7.82/1.51  fof(f25,plain,(
% 7.82/1.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.82/1.51    introduced(choice_axiom,[])).
% 7.82/1.51  
% 7.82/1.51  fof(f26,plain,(
% 7.82/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.82/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f25])).
% 7.82/1.51  
% 7.82/1.51  fof(f37,plain,(
% 7.82/1.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.82/1.51    inference(cnf_transformation,[],[f26])).
% 7.82/1.51  
% 7.82/1.51  fof(f45,plain,(
% 7.82/1.51    r1_xboole_0(sK3,sK4)),
% 7.82/1.51    inference(cnf_transformation,[],[f28])).
% 7.82/1.51  
% 7.82/1.51  fof(f7,axiom,(
% 7.82/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.51  
% 7.82/1.51  fof(f41,plain,(
% 7.82/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.82/1.51    inference(cnf_transformation,[],[f7])).
% 7.82/1.51  
% 7.82/1.51  fof(f30,plain,(
% 7.82/1.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.82/1.51    inference(cnf_transformation,[],[f24])).
% 7.82/1.51  
% 7.82/1.51  fof(f48,plain,(
% 7.82/1.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.82/1.51    inference(equality_resolution,[],[f30])).
% 7.82/1.51  
% 7.82/1.51  fof(f6,axiom,(
% 7.82/1.51    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 7.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.51  
% 7.82/1.51  fof(f15,plain,(
% 7.82/1.51    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 7.82/1.51    inference(ennf_transformation,[],[f6])).
% 7.82/1.51  
% 7.82/1.51  fof(f16,plain,(
% 7.82/1.51    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 7.82/1.51    inference(flattening,[],[f15])).
% 7.82/1.51  
% 7.82/1.51  fof(f40,plain,(
% 7.82/1.51    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 7.82/1.51    inference(cnf_transformation,[],[f16])).
% 7.82/1.51  
% 7.82/1.51  fof(f2,axiom,(
% 7.82/1.51    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.51  
% 7.82/1.51  fof(f11,plain,(
% 7.82/1.51    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.82/1.51    inference(rectify,[],[f2])).
% 7.82/1.51  
% 7.82/1.51  fof(f35,plain,(
% 7.82/1.51    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.82/1.51    inference(cnf_transformation,[],[f11])).
% 7.82/1.51  
% 7.82/1.51  fof(f5,axiom,(
% 7.82/1.51    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 7.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.51  
% 7.82/1.51  fof(f39,plain,(
% 7.82/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 7.82/1.51    inference(cnf_transformation,[],[f5])).
% 7.82/1.51  
% 7.82/1.51  fof(f4,axiom,(
% 7.82/1.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.51  
% 7.82/1.51  fof(f14,plain,(
% 7.82/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.82/1.51    inference(ennf_transformation,[],[f4])).
% 7.82/1.51  
% 7.82/1.51  fof(f38,plain,(
% 7.82/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.82/1.51    inference(cnf_transformation,[],[f14])).
% 7.82/1.51  
% 7.82/1.51  fof(f8,axiom,(
% 7.82/1.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.51  
% 7.82/1.51  fof(f17,plain,(
% 7.82/1.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.82/1.51    inference(ennf_transformation,[],[f8])).
% 7.82/1.51  
% 7.82/1.51  fof(f42,plain,(
% 7.82/1.51    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.82/1.51    inference(cnf_transformation,[],[f17])).
% 7.82/1.51  
% 7.82/1.51  fof(f46,plain,(
% 7.82/1.51    k1_xboole_0 != sK2),
% 7.82/1.51    inference(cnf_transformation,[],[f28])).
% 7.82/1.51  
% 7.82/1.51  fof(f43,plain,(
% 7.82/1.51    r1_tarski(sK2,sK3)),
% 7.82/1.51    inference(cnf_transformation,[],[f28])).
% 7.82/1.51  
% 7.82/1.51  cnf(c_16,negated_conjecture,
% 7.82/1.51      ( r1_tarski(sK2,sK4) ),
% 7.82/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_514,plain,
% 7.82/1.51      ( r1_tarski(sK2,sK4) = iProver_top ),
% 7.82/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_2,plain,
% 7.82/1.51      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.82/1.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.82/1.51      | k4_xboole_0(X0,X1) = X2 ),
% 7.82/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_521,plain,
% 7.82/1.51      ( k4_xboole_0(X0,X1) = X2
% 7.82/1.51      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.82/1.51      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.82/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_7,plain,
% 7.82/1.51      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 7.82/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_15,negated_conjecture,
% 7.82/1.51      ( r1_xboole_0(sK3,sK4) ),
% 7.82/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_173,plain,
% 7.82/1.51      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | sK4 != X2 | sK3 != X1 ),
% 7.82/1.51      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_174,plain,
% 7.82/1.51      ( ~ r2_hidden(X0,k3_xboole_0(sK3,sK4)) ),
% 7.82/1.51      inference(unflattening,[status(thm)],[c_173]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_511,plain,
% 7.82/1.51      ( r2_hidden(X0,k3_xboole_0(sK3,sK4)) != iProver_top ),
% 7.82/1.51      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_11962,plain,
% 7.82/1.51      ( k4_xboole_0(k3_xboole_0(sK3,sK4),X0) = X1
% 7.82/1.51      | r2_hidden(sK0(k3_xboole_0(sK3,sK4),X0,X1),X1) = iProver_top ),
% 7.82/1.51      inference(superposition,[status(thm)],[c_521,c_511]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_11957,plain,
% 7.82/1.51      ( k4_xboole_0(X0,X1) = k3_xboole_0(sK3,sK4)
% 7.82/1.51      | r2_hidden(sK0(X0,X1,k3_xboole_0(sK3,sK4)),X0) = iProver_top ),
% 7.82/1.51      inference(superposition,[status(thm)],[c_521,c_511]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_14477,plain,
% 7.82/1.51      ( k4_xboole_0(k3_xboole_0(sK3,sK4),X0) = k3_xboole_0(sK3,sK4) ),
% 7.82/1.51      inference(superposition,[status(thm)],[c_11957,c_511]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_14534,plain,
% 7.82/1.51      ( k3_xboole_0(sK3,sK4) = X0
% 7.82/1.51      | r2_hidden(sK0(k3_xboole_0(sK3,sK4),X1,X0),X0) = iProver_top ),
% 7.82/1.51      inference(demodulation,[status(thm)],[c_11962,c_14477]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_12,plain,
% 7.82/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.82/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_4,plain,
% 7.82/1.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.82/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_519,plain,
% 7.82/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.82/1.51      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.82/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_1916,plain,
% 7.82/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.82/1.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.82/1.51      inference(superposition,[status(thm)],[c_12,c_519]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_14473,plain,
% 7.82/1.51      ( k4_xboole_0(X0,X1) = k3_xboole_0(sK3,sK4)
% 7.82/1.51      | r2_hidden(sK0(X0,X1,k3_xboole_0(sK3,sK4)),k1_xboole_0) != iProver_top ),
% 7.82/1.51      inference(superposition,[status(thm)],[c_11957,c_1916]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_14577,plain,
% 7.82/1.51      ( k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(sK3,sK4) ),
% 7.82/1.51      inference(superposition,[status(thm)],[c_11957,c_14473]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_14624,plain,
% 7.82/1.51      ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1)) != iProver_top ),
% 7.82/1.51      inference(superposition,[status(thm)],[c_14577,c_511]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_14815,plain,
% 7.82/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.82/1.51      inference(superposition,[status(thm)],[c_12,c_14624]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_14869,plain,
% 7.82/1.51      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 7.82/1.51      inference(superposition,[status(thm)],[c_14534,c_14815]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_11,plain,
% 7.82/1.51      ( ~ r1_tarski(X0,X1)
% 7.82/1.51      | ~ r1_tarski(X2,X3)
% 7.82/1.51      | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) ),
% 7.82/1.51      inference(cnf_transformation,[],[f40]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_516,plain,
% 8.04/1.51      ( r1_tarski(X0,X1) != iProver_top
% 8.04/1.51      | r1_tarski(X2,X3) != iProver_top
% 8.04/1.51      | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_6,plain,
% 8.04/1.51      ( k2_xboole_0(X0,X0) = X0 ),
% 8.04/1.51      inference(cnf_transformation,[],[f35]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_10,plain,
% 8.04/1.51      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 8.04/1.51      inference(cnf_transformation,[],[f39]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_819,plain,
% 8.04/1.51      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_6,c_10]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_931,plain,
% 8.04/1.51      ( k2_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_6,c_819]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_9,plain,
% 8.04/1.51      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 8.04/1.51      inference(cnf_transformation,[],[f38]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_517,plain,
% 8.04/1.51      ( r1_tarski(X0,X1) = iProver_top
% 8.04/1.51      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1233,plain,
% 8.04/1.51      ( r1_tarski(X0,X1) = iProver_top
% 8.04/1.51      | r1_tarski(k3_xboole_0(X0,X0),X1) != iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_931,c_517]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_1895,plain,
% 8.04/1.51      ( r1_tarski(X0,X1) != iProver_top
% 8.04/1.51      | r1_tarski(X0,X2) != iProver_top
% 8.04/1.51      | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_516,c_1233]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_18885,plain,
% 8.04/1.51      ( r1_tarski(X0,sK4) != iProver_top
% 8.04/1.51      | r1_tarski(X0,sK3) != iProver_top
% 8.04/1.51      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_14869,c_1895]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_29019,plain,
% 8.04/1.51      ( r1_tarski(sK2,sK3) != iProver_top
% 8.04/1.51      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 8.04/1.51      inference(superposition,[status(thm)],[c_514,c_18885]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_13,plain,
% 8.04/1.51      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 8.04/1.51      inference(cnf_transformation,[],[f42]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_618,plain,
% 8.04/1.51      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 8.04/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_619,plain,
% 8.04/1.51      ( k1_xboole_0 = sK2 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_14,negated_conjecture,
% 8.04/1.51      ( k1_xboole_0 != sK2 ),
% 8.04/1.51      inference(cnf_transformation,[],[f46]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_17,negated_conjecture,
% 8.04/1.51      ( r1_tarski(sK2,sK3) ),
% 8.04/1.51      inference(cnf_transformation,[],[f43]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(c_18,plain,
% 8.04/1.51      ( r1_tarski(sK2,sK3) = iProver_top ),
% 8.04/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.04/1.51  
% 8.04/1.51  cnf(contradiction,plain,
% 8.04/1.51      ( $false ),
% 8.04/1.51      inference(minisat,[status(thm)],[c_29019,c_619,c_14,c_18]) ).
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 8.04/1.51  
% 8.04/1.51  ------                               Statistics
% 8.04/1.51  
% 8.04/1.51  ------ General
% 8.04/1.51  
% 8.04/1.51  abstr_ref_over_cycles:                  0
% 8.04/1.51  abstr_ref_under_cycles:                 0
% 8.04/1.51  gc_basic_clause_elim:                   0
% 8.04/1.51  forced_gc_time:                         0
% 8.04/1.51  parsing_time:                           0.01
% 8.04/1.51  unif_index_cands_time:                  0.
% 8.04/1.51  unif_index_add_time:                    0.
% 8.04/1.51  orderings_time:                         0.
% 8.04/1.51  out_proof_time:                         0.007
% 8.04/1.51  total_time:                             0.863
% 8.04/1.51  num_of_symbols:                         43
% 8.04/1.51  num_of_terms:                           42273
% 8.04/1.51  
% 8.04/1.51  ------ Preprocessing
% 8.04/1.51  
% 8.04/1.51  num_of_splits:                          0
% 8.04/1.51  num_of_split_atoms:                     0
% 8.04/1.51  num_of_reused_defs:                     0
% 8.04/1.51  num_eq_ax_congr_red:                    21
% 8.04/1.51  num_of_sem_filtered_clauses:            1
% 8.04/1.51  num_of_subtypes:                        0
% 8.04/1.51  monotx_restored_types:                  0
% 8.04/1.51  sat_num_of_epr_types:                   0
% 8.04/1.51  sat_num_of_non_cyclic_types:            0
% 8.04/1.51  sat_guarded_non_collapsed_types:        0
% 8.04/1.51  num_pure_diseq_elim:                    0
% 8.04/1.51  simp_replaced_by:                       0
% 8.04/1.51  res_preprocessed:                       84
% 8.04/1.51  prep_upred:                             0
% 8.04/1.51  prep_unflattend:                        2
% 8.04/1.51  smt_new_axioms:                         0
% 8.04/1.51  pred_elim_cands:                        2
% 8.04/1.51  pred_elim:                              1
% 8.04/1.51  pred_elim_cl:                           1
% 8.04/1.51  pred_elim_cycles:                       3
% 8.04/1.51  merged_defs:                            0
% 8.04/1.51  merged_defs_ncl:                        0
% 8.04/1.51  bin_hyper_res:                          0
% 8.04/1.51  prep_cycles:                            4
% 8.04/1.51  pred_elim_time:                         0.001
% 8.04/1.51  splitting_time:                         0.
% 8.04/1.51  sem_filter_time:                        0.
% 8.04/1.51  monotx_time:                            0.
% 8.04/1.51  subtype_inf_time:                       0.
% 8.04/1.51  
% 8.04/1.51  ------ Problem properties
% 8.04/1.51  
% 8.04/1.51  clauses:                                17
% 8.04/1.51  conjectures:                            3
% 8.04/1.51  epr:                                    4
% 8.04/1.51  horn:                                   13
% 8.04/1.51  ground:                                 3
% 8.04/1.51  unary:                                  7
% 8.04/1.51  binary:                                 5
% 8.04/1.51  lits:                                   33
% 8.04/1.51  lits_eq:                                8
% 8.04/1.51  fd_pure:                                0
% 8.04/1.51  fd_pseudo:                              0
% 8.04/1.51  fd_cond:                                1
% 8.04/1.51  fd_pseudo_cond:                         3
% 8.04/1.51  ac_symbols:                             0
% 8.04/1.51  
% 8.04/1.51  ------ Propositional Solver
% 8.04/1.51  
% 8.04/1.51  prop_solver_calls:                      29
% 8.04/1.51  prop_fast_solver_calls:                 720
% 8.04/1.51  smt_solver_calls:                       0
% 8.04/1.51  smt_fast_solver_calls:                  0
% 8.04/1.51  prop_num_of_clauses:                    11062
% 8.04/1.51  prop_preprocess_simplified:             9795
% 8.04/1.51  prop_fo_subsumed:                       2
% 8.04/1.51  prop_solver_time:                       0.
% 8.04/1.51  smt_solver_time:                        0.
% 8.04/1.51  smt_fast_solver_time:                   0.
% 8.04/1.51  prop_fast_solver_time:                  0.
% 8.04/1.51  prop_unsat_core_time:                   0.
% 8.04/1.51  
% 8.04/1.51  ------ QBF
% 8.04/1.51  
% 8.04/1.51  qbf_q_res:                              0
% 8.04/1.51  qbf_num_tautologies:                    0
% 8.04/1.51  qbf_prep_cycles:                        0
% 8.04/1.51  
% 8.04/1.51  ------ BMC1
% 8.04/1.51  
% 8.04/1.51  bmc1_current_bound:                     -1
% 8.04/1.51  bmc1_last_solved_bound:                 -1
% 8.04/1.51  bmc1_unsat_core_size:                   -1
% 8.04/1.51  bmc1_unsat_core_parents_size:           -1
% 8.04/1.51  bmc1_merge_next_fun:                    0
% 8.04/1.51  bmc1_unsat_core_clauses_time:           0.
% 8.04/1.51  
% 8.04/1.51  ------ Instantiation
% 8.04/1.51  
% 8.04/1.51  inst_num_of_clauses:                    1523
% 8.04/1.51  inst_num_in_passive:                    279
% 8.04/1.51  inst_num_in_active:                     742
% 8.04/1.51  inst_num_in_unprocessed:                502
% 8.04/1.51  inst_num_of_loops:                      820
% 8.04/1.51  inst_num_of_learning_restarts:          0
% 8.04/1.51  inst_num_moves_active_passive:          76
% 8.04/1.51  inst_lit_activity:                      0
% 8.04/1.51  inst_lit_activity_moves:                1
% 8.04/1.51  inst_num_tautologies:                   0
% 8.04/1.51  inst_num_prop_implied:                  0
% 8.04/1.51  inst_num_existing_simplified:           0
% 8.04/1.51  inst_num_eq_res_simplified:             0
% 8.04/1.51  inst_num_child_elim:                    0
% 8.04/1.51  inst_num_of_dismatching_blockings:      904
% 8.04/1.51  inst_num_of_non_proper_insts:           1002
% 8.04/1.51  inst_num_of_duplicates:                 0
% 8.04/1.51  inst_inst_num_from_inst_to_res:         0
% 8.04/1.51  inst_dismatching_checking_time:         0.
% 8.04/1.51  
% 8.04/1.51  ------ Resolution
% 8.04/1.51  
% 8.04/1.51  res_num_of_clauses:                     0
% 8.04/1.51  res_num_in_passive:                     0
% 8.04/1.51  res_num_in_active:                      0
% 8.04/1.51  res_num_of_loops:                       88
% 8.04/1.51  res_forward_subset_subsumed:            28
% 8.04/1.51  res_backward_subset_subsumed:           0
% 8.04/1.51  res_forward_subsumed:                   0
% 8.04/1.51  res_backward_subsumed:                  0
% 8.04/1.51  res_forward_subsumption_resolution:     0
% 8.04/1.51  res_backward_subsumption_resolution:    0
% 8.04/1.51  res_clause_to_clause_subsumption:       36856
% 8.04/1.51  res_orphan_elimination:                 0
% 8.04/1.51  res_tautology_del:                      14
% 8.04/1.51  res_num_eq_res_simplified:              0
% 8.04/1.51  res_num_sel_changes:                    0
% 8.04/1.51  res_moves_from_active_to_pass:          0
% 8.04/1.51  
% 8.04/1.51  ------ Superposition
% 8.04/1.51  
% 8.04/1.51  sup_time_total:                         0.
% 8.04/1.51  sup_time_generating:                    0.
% 8.04/1.51  sup_time_sim_full:                      0.
% 8.04/1.51  sup_time_sim_immed:                     0.
% 8.04/1.51  
% 8.04/1.51  sup_num_of_clauses:                     2426
% 8.04/1.51  sup_num_in_active:                      146
% 8.04/1.51  sup_num_in_passive:                     2280
% 8.04/1.51  sup_num_of_loops:                       162
% 8.04/1.51  sup_fw_superposition:                   2155
% 8.04/1.51  sup_bw_superposition:                   1326
% 8.04/1.51  sup_immediate_simplified:               1560
% 8.04/1.51  sup_given_eliminated:                   1
% 8.04/1.51  comparisons_done:                       0
% 8.04/1.51  comparisons_avoided:                    0
% 8.04/1.51  
% 8.04/1.51  ------ Simplifications
% 8.04/1.51  
% 8.04/1.51  
% 8.04/1.51  sim_fw_subset_subsumed:                 23
% 8.04/1.51  sim_bw_subset_subsumed:                 0
% 8.04/1.51  sim_fw_subsumed:                        272
% 8.04/1.51  sim_bw_subsumed:                        74
% 8.04/1.51  sim_fw_subsumption_res:                 0
% 8.04/1.51  sim_bw_subsumption_res:                 0
% 8.04/1.51  sim_tautology_del:                      12
% 8.04/1.51  sim_eq_tautology_del:                   53
% 8.04/1.51  sim_eq_res_simp:                        1
% 8.04/1.51  sim_fw_demodulated:                     1184
% 8.04/1.51  sim_bw_demodulated:                     53
% 8.04/1.51  sim_light_normalised:                   474
% 8.04/1.51  sim_joinable_taut:                      0
% 8.04/1.51  sim_joinable_simp:                      0
% 8.04/1.51  sim_ac_normalised:                      0
% 8.04/1.51  sim_smt_subsumption:                    0
% 8.04/1.51  
%------------------------------------------------------------------------------
