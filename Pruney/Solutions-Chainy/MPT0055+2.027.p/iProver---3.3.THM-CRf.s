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
% DateTime   : Thu Dec  3 11:22:53 EST 2020

% Result     : Theorem 55.29s
% Output     : CNFRefutation 55.29s
% Verified   : 
% Statistics : Number of formulae       :  226 (74408 expanded)
%              Number of clauses        :  182 (37105 expanded)
%              Number of leaves         :   14 (18609 expanded)
%              Depth                    :   50
%              Number of atoms          :  378 (75885 expanded)
%              Number of equality atoms :  231 (74448 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
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

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

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
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f24])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f10,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)
   => k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k3_xboole_0(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k3_xboole_0(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f26])).

fof(f45,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k3_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_16,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_790,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_15])).

cnf(c_1138,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_14,c_790])).

cnf(c_1144,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1138,c_790])).

cnf(c_1561,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_16,c_1144])).

cnf(c_1583,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1561,c_16])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_418,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_419,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_422,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3508,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_422])).

cnf(c_93150,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_418,c_3508])).

cnf(c_97854,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_93150])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_424,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_417,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6368,plain,
    ( k3_xboole_0(X0,X1) = k4_xboole_0(X2,X3)
    | r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK0(X2,X3,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_417])).

cnf(c_1139,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_790,c_14])).

cnf(c_1142,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1139,c_14])).

cnf(c_1289,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1142,c_15])).

cnf(c_12,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_531,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_13,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_592,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_531,c_13])).

cnf(c_937,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_592,c_16])).

cnf(c_681,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_531,c_14])).

cnf(c_683,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_681,c_531])).

cnf(c_942,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_937,c_683])).

cnf(c_793,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_531,c_15])).

cnf(c_1005,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_942,c_793])).

cnf(c_1295,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1289,c_1005])).

cnf(c_1438,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1295])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_421,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2196,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_421])).

cnf(c_794,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_15,c_14])).

cnf(c_799,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_794,c_14])).

cnf(c_1290,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1142,c_799])).

cnf(c_948,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_793,c_14])).

cnf(c_950,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_948,c_12])).

cnf(c_995,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_950,c_14])).

cnf(c_1292,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1290,c_995])).

cnf(c_1591,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1292])).

cnf(c_2014,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13,c_1591])).

cnf(c_2056,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2014,c_13])).

cnf(c_1463,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_1438])).

cnf(c_2257,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2056,c_1463])).

cnf(c_2263,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2257,c_16])).

cnf(c_3524,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2263,c_422])).

cnf(c_15641,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2196,c_3524])).

cnf(c_324143,plain,
    ( k3_xboole_0(X0,X1) = k4_xboole_0(k1_xboole_0,X2)
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6368,c_15641])).

cnf(c_324218,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_324143,c_942])).

cnf(c_333592,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_97854,c_324218])).

cnf(c_1469,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1438,c_14])).

cnf(c_1471,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1469,c_12])).

cnf(c_1968,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1471])).

cnf(c_2737,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_14,c_1968])).

cnf(c_2789,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2737,c_1968])).

cnf(c_2973,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_16,c_2789])).

cnf(c_3048,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2973,c_13])).

cnf(c_3555,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_16,c_3048])).

cnf(c_337632,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_333592,c_3555])).

cnf(c_792,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_2253,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,k3_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2056,c_792])).

cnf(c_2268,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_2253,c_16])).

cnf(c_337675,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_337632,c_2268])).

cnf(c_3564,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k2_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1438,c_3048])).

cnf(c_4644,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3564,c_531])).

cnf(c_2412,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2263,c_14])).

cnf(c_2416,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2412,c_12])).

cnf(c_2445,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2416,c_1591])).

cnf(c_2465,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2445,c_2416])).

cnf(c_10245,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2268,c_2465])).

cnf(c_1983,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1471,c_0])).

cnf(c_3554,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_15,c_3048])).

cnf(c_10611,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3554,c_1968])).

cnf(c_1713,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1463])).

cnf(c_3002,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2789,c_0])).

cnf(c_2980,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1295,c_2789])).

cnf(c_2760,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1968,c_0])).

cnf(c_3036,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2980,c_2760])).

cnf(c_3276,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3002,c_3036])).

cnf(c_3355,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3276,c_3036])).

cnf(c_4548,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1713,c_3355])).

cnf(c_4586,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_4548,c_3036])).

cnf(c_10673,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_10611,c_4586])).

cnf(c_43411,plain,
    ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10673,c_1295])).

cnf(c_43815,plain,
    ( k4_xboole_0(k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1983,c_43411])).

cnf(c_44311,plain,
    ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_43815,c_1591])).

cnf(c_44757,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X0))) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_44311,c_10245])).

cnf(c_45026,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_44757,c_13,c_683])).

cnf(c_48004,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1142,c_45026])).

cnf(c_48578,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X1) = k3_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_48004,c_1968,c_2760,c_45026])).

cnf(c_51011,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)),k3_xboole_0(k2_xboole_0(X1,X0),X1)) = k3_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_48578,c_10245])).

cnf(c_1341,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_792])).

cnf(c_51324,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_51011,c_15,c_1341])).

cnf(c_10207,plain,
    ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
    inference(superposition,[status(thm)],[c_15,c_2268])).

cnf(c_10393,plain,
    ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_10207,c_15,c_1341])).

cnf(c_58081,plain,
    ( k4_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k3_xboole_0(k2_xboole_0(X1,X0),X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X1)),k3_xboole_0(k2_xboole_0(X1,X0),X1))) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X1)),k3_xboole_0(k2_xboole_0(X1,X0),X1))) ),
    inference(superposition,[status(thm)],[c_51324,c_10393])).

cnf(c_10248,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2268,c_2263])).

cnf(c_14095,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_790,c_10248])).

cnf(c_14300,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14095,c_792])).

cnf(c_58352,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k3_xboole_0(k2_xboole_0(X1,X0),X1)) = k3_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(demodulation,[status(thm)],[c_58081,c_683,c_14300])).

cnf(c_58092,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X0),k3_xboole_0(k2_xboole_0(X0,X1),X0))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_51324,c_3554])).

cnf(c_58326,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X0),k3_xboole_0(k2_xboole_0(X0,X1),X0))) = k3_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_58092,c_51324])).

cnf(c_58328,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k3_xboole_0(k2_xboole_0(X1,X0),X1))) = k3_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(light_normalisation,[status(thm)],[c_58326,c_14300])).

cnf(c_58353,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(demodulation,[status(thm)],[c_58352,c_58328])).

cnf(c_1447,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1295,c_792])).

cnf(c_1451,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1447,c_1295])).

cnf(c_1453,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1451,c_683])).

cnf(c_6238,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1453,c_1968])).

cnf(c_3203,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_16,c_3002])).

cnf(c_3263,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3203,c_13])).

cnf(c_6274,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6238,c_3263])).

cnf(c_136956,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0),k1_xboole_0),k3_xboole_0(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_58353,c_6274])).

cnf(c_137018,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0),k3_xboole_0(k2_xboole_0(X1,X0),X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_136956,c_12])).

cnf(c_181425,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k3_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_0,c_137018])).

cnf(c_10221,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6238,c_2268])).

cnf(c_1465,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_799,c_1438])).

cnf(c_10361,plain,
    ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10221,c_1465,c_6238])).

cnf(c_14093,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16,c_10248])).

cnf(c_16855,plain,
    ( k4_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k1_xboole_0),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10361,c_14093])).

cnf(c_17018,plain,
    ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16855,c_16,c_683])).

cnf(c_32165,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_17018,c_14])).

cnf(c_32168,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_32165,c_12,c_2056])).

cnf(c_32176,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_0,c_32168])).

cnf(c_136853,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k3_xboole_0(k2_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X1),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_58353,c_32176])).

cnf(c_4780,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3048,c_4644])).

cnf(c_137220,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_136853,c_12,c_4780])).

cnf(c_222516,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0)),k3_xboole_0(k2_xboole_0(X0,X1),X1)),k1_xboole_0) = k3_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_181425,c_137220])).

cnf(c_3559,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1005,c_3048])).

cnf(c_4066,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3559,c_531])).

cnf(c_222804,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k3_xboole_0(k2_xboole_0(X1,X0),X0)),k1_xboole_0) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_222516,c_13,c_4066])).

cnf(c_1137,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_13,c_790])).

cnf(c_1148,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1137,c_1005])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_423,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4883,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_423])).

cnf(c_221903,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4883,c_2196,c_3524])).

cnf(c_221904,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_221903])).

cnf(c_262367,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X1),k3_xboole_0(k2_xboole_0(X2,X1),X1))) = iProver_top
    | r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X2,X1),X1),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_222804,c_221904])).

cnf(c_3896,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_683,c_1583])).

cnf(c_3967,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3896,c_683])).

cnf(c_4289,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3967,c_422])).

cnf(c_262397,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X1),k3_xboole_0(k2_xboole_0(X2,X1),X1))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X2,X1),X1),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_222804,c_4289])).

cnf(c_262449,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X2),k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_262367,c_262397])).

cnf(c_263935,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10245,c_262449])).

cnf(c_264058,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_263935,c_4066])).

cnf(c_264085,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4644,c_264058])).

cnf(c_264561,plain,
    ( r1_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_264085])).

cnf(c_333657,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_264561,c_324218])).

cnf(c_1726,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1463,c_14])).

cnf(c_1728,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1726,c_12])).

cnf(c_5121,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_2789,c_1728])).

cnf(c_5237,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5121,c_3355])).

cnf(c_32223,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0))) = k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5237,c_32168])).

cnf(c_2614,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_15,c_2465])).

cnf(c_6759,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3002,c_2614])).

cnf(c_6881,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_6759,c_3002])).

cnf(c_32544,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))),k1_xboole_0) = k3_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_32223,c_6881,c_32168])).

cnf(c_2431,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_15,c_2416])).

cnf(c_6559,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3002,c_2431])).

cnf(c_6727,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_6559,c_3002])).

cnf(c_32545,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_32544,c_6727])).

cnf(c_4280,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3967,c_1583])).

cnf(c_4308,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4280,c_3967])).

cnf(c_5900,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4308,c_422])).

cnf(c_245067,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5900,c_221904])).

cnf(c_245073,plain,
    ( r1_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_245067])).

cnf(c_252864,plain,
    ( r1_xboole_0(X0,k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_32545,c_245073])).

cnf(c_333673,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_252864,c_324218])).

cnf(c_333739,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_333657,c_333673])).

cnf(c_337676,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_337675,c_12,c_333739])).

cnf(c_17,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k3_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_339196,plain,
    ( k3_xboole_0(sK3,sK4) != k3_xboole_0(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_337676,c_17])).

cnf(c_339256,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_339196])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:02:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 55.29/7.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.29/7.51  
% 55.29/7.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.29/7.51  
% 55.29/7.51  ------  iProver source info
% 55.29/7.51  
% 55.29/7.51  git: date: 2020-06-30 10:37:57 +0100
% 55.29/7.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.29/7.51  git: non_committed_changes: false
% 55.29/7.51  git: last_make_outside_of_git: false
% 55.29/7.51  
% 55.29/7.51  ------ 
% 55.29/7.51  
% 55.29/7.51  ------ Input Options
% 55.29/7.51  
% 55.29/7.51  --out_options                           all
% 55.29/7.51  --tptp_safe_out                         true
% 55.29/7.51  --problem_path                          ""
% 55.29/7.51  --include_path                          ""
% 55.29/7.51  --clausifier                            res/vclausify_rel
% 55.29/7.51  --clausifier_options                    --mode clausify
% 55.29/7.51  --stdin                                 false
% 55.29/7.51  --stats_out                             all
% 55.29/7.51  
% 55.29/7.51  ------ General Options
% 55.29/7.51  
% 55.29/7.51  --fof                                   false
% 55.29/7.51  --time_out_real                         305.
% 55.29/7.51  --time_out_virtual                      -1.
% 55.29/7.51  --symbol_type_check                     false
% 55.29/7.51  --clausify_out                          false
% 55.29/7.51  --sig_cnt_out                           false
% 55.29/7.51  --trig_cnt_out                          false
% 55.29/7.51  --trig_cnt_out_tolerance                1.
% 55.29/7.51  --trig_cnt_out_sk_spl                   false
% 55.29/7.51  --abstr_cl_out                          false
% 55.29/7.51  
% 55.29/7.51  ------ Global Options
% 55.29/7.51  
% 55.29/7.51  --schedule                              default
% 55.29/7.51  --add_important_lit                     false
% 55.29/7.51  --prop_solver_per_cl                    1000
% 55.29/7.51  --min_unsat_core                        false
% 55.29/7.51  --soft_assumptions                      false
% 55.29/7.51  --soft_lemma_size                       3
% 55.29/7.51  --prop_impl_unit_size                   0
% 55.29/7.51  --prop_impl_unit                        []
% 55.29/7.51  --share_sel_clauses                     true
% 55.29/7.51  --reset_solvers                         false
% 55.29/7.51  --bc_imp_inh                            [conj_cone]
% 55.29/7.51  --conj_cone_tolerance                   3.
% 55.29/7.51  --extra_neg_conj                        none
% 55.29/7.51  --large_theory_mode                     true
% 55.29/7.51  --prolific_symb_bound                   200
% 55.29/7.51  --lt_threshold                          2000
% 55.29/7.51  --clause_weak_htbl                      true
% 55.29/7.51  --gc_record_bc_elim                     false
% 55.29/7.51  
% 55.29/7.51  ------ Preprocessing Options
% 55.29/7.51  
% 55.29/7.51  --preprocessing_flag                    true
% 55.29/7.51  --time_out_prep_mult                    0.1
% 55.29/7.51  --splitting_mode                        input
% 55.29/7.51  --splitting_grd                         true
% 55.29/7.51  --splitting_cvd                         false
% 55.29/7.51  --splitting_cvd_svl                     false
% 55.29/7.51  --splitting_nvd                         32
% 55.29/7.51  --sub_typing                            true
% 55.29/7.51  --prep_gs_sim                           true
% 55.29/7.51  --prep_unflatten                        true
% 55.29/7.51  --prep_res_sim                          true
% 55.29/7.51  --prep_upred                            true
% 55.29/7.51  --prep_sem_filter                       exhaustive
% 55.29/7.51  --prep_sem_filter_out                   false
% 55.29/7.51  --pred_elim                             true
% 55.29/7.51  --res_sim_input                         true
% 55.29/7.51  --eq_ax_congr_red                       true
% 55.29/7.51  --pure_diseq_elim                       true
% 55.29/7.51  --brand_transform                       false
% 55.29/7.51  --non_eq_to_eq                          false
% 55.29/7.51  --prep_def_merge                        true
% 55.29/7.51  --prep_def_merge_prop_impl              false
% 55.29/7.51  --prep_def_merge_mbd                    true
% 55.29/7.51  --prep_def_merge_tr_red                 false
% 55.29/7.51  --prep_def_merge_tr_cl                  false
% 55.29/7.51  --smt_preprocessing                     true
% 55.29/7.51  --smt_ac_axioms                         fast
% 55.29/7.51  --preprocessed_out                      false
% 55.29/7.51  --preprocessed_stats                    false
% 55.29/7.51  
% 55.29/7.51  ------ Abstraction refinement Options
% 55.29/7.51  
% 55.29/7.51  --abstr_ref                             []
% 55.29/7.51  --abstr_ref_prep                        false
% 55.29/7.51  --abstr_ref_until_sat                   false
% 55.29/7.51  --abstr_ref_sig_restrict                funpre
% 55.29/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 55.29/7.51  --abstr_ref_under                       []
% 55.29/7.51  
% 55.29/7.51  ------ SAT Options
% 55.29/7.51  
% 55.29/7.51  --sat_mode                              false
% 55.29/7.51  --sat_fm_restart_options                ""
% 55.29/7.51  --sat_gr_def                            false
% 55.29/7.51  --sat_epr_types                         true
% 55.29/7.51  --sat_non_cyclic_types                  false
% 55.29/7.51  --sat_finite_models                     false
% 55.29/7.51  --sat_fm_lemmas                         false
% 55.29/7.51  --sat_fm_prep                           false
% 55.29/7.51  --sat_fm_uc_incr                        true
% 55.29/7.51  --sat_out_model                         small
% 55.29/7.51  --sat_out_clauses                       false
% 55.29/7.51  
% 55.29/7.51  ------ QBF Options
% 55.29/7.51  
% 55.29/7.51  --qbf_mode                              false
% 55.29/7.51  --qbf_elim_univ                         false
% 55.29/7.51  --qbf_dom_inst                          none
% 55.29/7.51  --qbf_dom_pre_inst                      false
% 55.29/7.51  --qbf_sk_in                             false
% 55.29/7.51  --qbf_pred_elim                         true
% 55.29/7.51  --qbf_split                             512
% 55.29/7.51  
% 55.29/7.51  ------ BMC1 Options
% 55.29/7.51  
% 55.29/7.51  --bmc1_incremental                      false
% 55.29/7.51  --bmc1_axioms                           reachable_all
% 55.29/7.51  --bmc1_min_bound                        0
% 55.29/7.51  --bmc1_max_bound                        -1
% 55.29/7.51  --bmc1_max_bound_default                -1
% 55.29/7.51  --bmc1_symbol_reachability              true
% 55.29/7.51  --bmc1_property_lemmas                  false
% 55.29/7.51  --bmc1_k_induction                      false
% 55.29/7.51  --bmc1_non_equiv_states                 false
% 55.29/7.51  --bmc1_deadlock                         false
% 55.29/7.51  --bmc1_ucm                              false
% 55.29/7.51  --bmc1_add_unsat_core                   none
% 55.29/7.51  --bmc1_unsat_core_children              false
% 55.29/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 55.29/7.51  --bmc1_out_stat                         full
% 55.29/7.51  --bmc1_ground_init                      false
% 55.29/7.51  --bmc1_pre_inst_next_state              false
% 55.29/7.51  --bmc1_pre_inst_state                   false
% 55.29/7.51  --bmc1_pre_inst_reach_state             false
% 55.29/7.51  --bmc1_out_unsat_core                   false
% 55.29/7.51  --bmc1_aig_witness_out                  false
% 55.29/7.51  --bmc1_verbose                          false
% 55.29/7.51  --bmc1_dump_clauses_tptp                false
% 55.29/7.51  --bmc1_dump_unsat_core_tptp             false
% 55.29/7.51  --bmc1_dump_file                        -
% 55.29/7.51  --bmc1_ucm_expand_uc_limit              128
% 55.29/7.51  --bmc1_ucm_n_expand_iterations          6
% 55.29/7.51  --bmc1_ucm_extend_mode                  1
% 55.29/7.51  --bmc1_ucm_init_mode                    2
% 55.29/7.51  --bmc1_ucm_cone_mode                    none
% 55.29/7.51  --bmc1_ucm_reduced_relation_type        0
% 55.29/7.51  --bmc1_ucm_relax_model                  4
% 55.29/7.51  --bmc1_ucm_full_tr_after_sat            true
% 55.29/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 55.29/7.51  --bmc1_ucm_layered_model                none
% 55.29/7.51  --bmc1_ucm_max_lemma_size               10
% 55.29/7.51  
% 55.29/7.51  ------ AIG Options
% 55.29/7.51  
% 55.29/7.51  --aig_mode                              false
% 55.29/7.51  
% 55.29/7.51  ------ Instantiation Options
% 55.29/7.51  
% 55.29/7.51  --instantiation_flag                    true
% 55.29/7.51  --inst_sos_flag                         false
% 55.29/7.51  --inst_sos_phase                        true
% 55.29/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.29/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.29/7.51  --inst_lit_sel_side                     num_symb
% 55.29/7.51  --inst_solver_per_active                1400
% 55.29/7.51  --inst_solver_calls_frac                1.
% 55.29/7.51  --inst_passive_queue_type               priority_queues
% 55.29/7.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.29/7.51  --inst_passive_queues_freq              [25;2]
% 55.29/7.51  --inst_dismatching                      true
% 55.29/7.51  --inst_eager_unprocessed_to_passive     true
% 55.29/7.51  --inst_prop_sim_given                   true
% 55.29/7.51  --inst_prop_sim_new                     false
% 55.29/7.51  --inst_subs_new                         false
% 55.29/7.51  --inst_eq_res_simp                      false
% 55.29/7.51  --inst_subs_given                       false
% 55.29/7.51  --inst_orphan_elimination               true
% 55.29/7.51  --inst_learning_loop_flag               true
% 55.29/7.51  --inst_learning_start                   3000
% 55.29/7.51  --inst_learning_factor                  2
% 55.29/7.51  --inst_start_prop_sim_after_learn       3
% 55.29/7.51  --inst_sel_renew                        solver
% 55.29/7.51  --inst_lit_activity_flag                true
% 55.29/7.51  --inst_restr_to_given                   false
% 55.29/7.51  --inst_activity_threshold               500
% 55.29/7.51  --inst_out_proof                        true
% 55.29/7.51  
% 55.29/7.51  ------ Resolution Options
% 55.29/7.51  
% 55.29/7.51  --resolution_flag                       true
% 55.29/7.51  --res_lit_sel                           adaptive
% 55.29/7.51  --res_lit_sel_side                      none
% 55.29/7.51  --res_ordering                          kbo
% 55.29/7.51  --res_to_prop_solver                    active
% 55.29/7.51  --res_prop_simpl_new                    false
% 55.29/7.51  --res_prop_simpl_given                  true
% 55.29/7.51  --res_passive_queue_type                priority_queues
% 55.29/7.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.29/7.51  --res_passive_queues_freq               [15;5]
% 55.29/7.51  --res_forward_subs                      full
% 55.29/7.51  --res_backward_subs                     full
% 55.29/7.51  --res_forward_subs_resolution           true
% 55.29/7.51  --res_backward_subs_resolution          true
% 55.29/7.51  --res_orphan_elimination                true
% 55.29/7.51  --res_time_limit                        2.
% 55.29/7.51  --res_out_proof                         true
% 55.29/7.51  
% 55.29/7.51  ------ Superposition Options
% 55.29/7.51  
% 55.29/7.51  --superposition_flag                    true
% 55.29/7.51  --sup_passive_queue_type                priority_queues
% 55.29/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.29/7.51  --sup_passive_queues_freq               [8;1;4]
% 55.29/7.51  --demod_completeness_check              fast
% 55.29/7.51  --demod_use_ground                      true
% 55.29/7.51  --sup_to_prop_solver                    passive
% 55.29/7.51  --sup_prop_simpl_new                    true
% 55.29/7.51  --sup_prop_simpl_given                  true
% 55.29/7.51  --sup_fun_splitting                     false
% 55.29/7.51  --sup_smt_interval                      50000
% 55.29/7.51  
% 55.29/7.51  ------ Superposition Simplification Setup
% 55.29/7.51  
% 55.29/7.51  --sup_indices_passive                   []
% 55.29/7.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.29/7.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.29/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.29/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 55.29/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.29/7.51  --sup_full_bw                           [BwDemod]
% 55.29/7.51  --sup_immed_triv                        [TrivRules]
% 55.29/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.29/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.29/7.51  --sup_immed_bw_main                     []
% 55.29/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.29/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 55.29/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.29/7.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.29/7.51  
% 55.29/7.51  ------ Combination Options
% 55.29/7.51  
% 55.29/7.51  --comb_res_mult                         3
% 55.29/7.51  --comb_sup_mult                         2
% 55.29/7.51  --comb_inst_mult                        10
% 55.29/7.51  
% 55.29/7.51  ------ Debug Options
% 55.29/7.51  
% 55.29/7.51  --dbg_backtrace                         false
% 55.29/7.51  --dbg_dump_prop_clauses                 false
% 55.29/7.51  --dbg_dump_prop_clauses_file            -
% 55.29/7.51  --dbg_out_stat                          false
% 55.29/7.51  ------ Parsing...
% 55.29/7.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.29/7.51  
% 55.29/7.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.29/7.51  
% 55.29/7.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.29/7.51  
% 55.29/7.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.29/7.51  ------ Proving...
% 55.29/7.51  ------ Problem Properties 
% 55.29/7.51  
% 55.29/7.51  
% 55.29/7.51  clauses                                 18
% 55.29/7.51  conjectures                             1
% 55.29/7.51  EPR                                     1
% 55.29/7.51  Horn                                    11
% 55.29/7.51  unary                                   7
% 55.29/7.51  binary                                  6
% 55.29/7.51  lits                                    35
% 55.29/7.51  lits eq                                 10
% 55.29/7.51  fd_pure                                 0
% 55.29/7.51  fd_pseudo                               0
% 55.29/7.51  fd_cond                                 0
% 55.29/7.51  fd_pseudo_cond                          3
% 55.29/7.51  AC symbols                              0
% 55.29/7.51  
% 55.29/7.51  ------ Schedule dynamic 5 is on 
% 55.29/7.51  
% 55.29/7.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.29/7.51  
% 55.29/7.51  
% 55.29/7.51  ------ 
% 55.29/7.51  Current options:
% 55.29/7.51  ------ 
% 55.29/7.51  
% 55.29/7.51  ------ Input Options
% 55.29/7.51  
% 55.29/7.51  --out_options                           all
% 55.29/7.51  --tptp_safe_out                         true
% 55.29/7.51  --problem_path                          ""
% 55.29/7.51  --include_path                          ""
% 55.29/7.51  --clausifier                            res/vclausify_rel
% 55.29/7.51  --clausifier_options                    --mode clausify
% 55.29/7.51  --stdin                                 false
% 55.29/7.51  --stats_out                             all
% 55.29/7.51  
% 55.29/7.51  ------ General Options
% 55.29/7.51  
% 55.29/7.51  --fof                                   false
% 55.29/7.51  --time_out_real                         305.
% 55.29/7.51  --time_out_virtual                      -1.
% 55.29/7.51  --symbol_type_check                     false
% 55.29/7.51  --clausify_out                          false
% 55.29/7.51  --sig_cnt_out                           false
% 55.29/7.51  --trig_cnt_out                          false
% 55.29/7.51  --trig_cnt_out_tolerance                1.
% 55.29/7.51  --trig_cnt_out_sk_spl                   false
% 55.29/7.51  --abstr_cl_out                          false
% 55.29/7.51  
% 55.29/7.51  ------ Global Options
% 55.29/7.51  
% 55.29/7.51  --schedule                              default
% 55.29/7.51  --add_important_lit                     false
% 55.29/7.51  --prop_solver_per_cl                    1000
% 55.29/7.51  --min_unsat_core                        false
% 55.29/7.51  --soft_assumptions                      false
% 55.29/7.51  --soft_lemma_size                       3
% 55.29/7.51  --prop_impl_unit_size                   0
% 55.29/7.51  --prop_impl_unit                        []
% 55.29/7.51  --share_sel_clauses                     true
% 55.29/7.51  --reset_solvers                         false
% 55.29/7.51  --bc_imp_inh                            [conj_cone]
% 55.29/7.51  --conj_cone_tolerance                   3.
% 55.29/7.51  --extra_neg_conj                        none
% 55.29/7.51  --large_theory_mode                     true
% 55.29/7.51  --prolific_symb_bound                   200
% 55.29/7.51  --lt_threshold                          2000
% 55.29/7.51  --clause_weak_htbl                      true
% 55.29/7.51  --gc_record_bc_elim                     false
% 55.29/7.51  
% 55.29/7.51  ------ Preprocessing Options
% 55.29/7.51  
% 55.29/7.51  --preprocessing_flag                    true
% 55.29/7.51  --time_out_prep_mult                    0.1
% 55.29/7.51  --splitting_mode                        input
% 55.29/7.51  --splitting_grd                         true
% 55.29/7.51  --splitting_cvd                         false
% 55.29/7.51  --splitting_cvd_svl                     false
% 55.29/7.51  --splitting_nvd                         32
% 55.29/7.51  --sub_typing                            true
% 55.29/7.51  --prep_gs_sim                           true
% 55.29/7.51  --prep_unflatten                        true
% 55.29/7.51  --prep_res_sim                          true
% 55.29/7.51  --prep_upred                            true
% 55.29/7.51  --prep_sem_filter                       exhaustive
% 55.29/7.51  --prep_sem_filter_out                   false
% 55.29/7.51  --pred_elim                             true
% 55.29/7.51  --res_sim_input                         true
% 55.29/7.51  --eq_ax_congr_red                       true
% 55.29/7.51  --pure_diseq_elim                       true
% 55.29/7.51  --brand_transform                       false
% 55.29/7.51  --non_eq_to_eq                          false
% 55.29/7.51  --prep_def_merge                        true
% 55.29/7.51  --prep_def_merge_prop_impl              false
% 55.29/7.51  --prep_def_merge_mbd                    true
% 55.29/7.51  --prep_def_merge_tr_red                 false
% 55.29/7.51  --prep_def_merge_tr_cl                  false
% 55.29/7.51  --smt_preprocessing                     true
% 55.29/7.51  --smt_ac_axioms                         fast
% 55.29/7.51  --preprocessed_out                      false
% 55.29/7.51  --preprocessed_stats                    false
% 55.29/7.51  
% 55.29/7.51  ------ Abstraction refinement Options
% 55.29/7.51  
% 55.29/7.51  --abstr_ref                             []
% 55.29/7.51  --abstr_ref_prep                        false
% 55.29/7.51  --abstr_ref_until_sat                   false
% 55.29/7.51  --abstr_ref_sig_restrict                funpre
% 55.29/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 55.29/7.51  --abstr_ref_under                       []
% 55.29/7.51  
% 55.29/7.51  ------ SAT Options
% 55.29/7.51  
% 55.29/7.51  --sat_mode                              false
% 55.29/7.51  --sat_fm_restart_options                ""
% 55.29/7.51  --sat_gr_def                            false
% 55.29/7.51  --sat_epr_types                         true
% 55.29/7.51  --sat_non_cyclic_types                  false
% 55.29/7.51  --sat_finite_models                     false
% 55.29/7.51  --sat_fm_lemmas                         false
% 55.29/7.51  --sat_fm_prep                           false
% 55.29/7.51  --sat_fm_uc_incr                        true
% 55.29/7.51  --sat_out_model                         small
% 55.29/7.51  --sat_out_clauses                       false
% 55.29/7.51  
% 55.29/7.51  ------ QBF Options
% 55.29/7.51  
% 55.29/7.51  --qbf_mode                              false
% 55.29/7.51  --qbf_elim_univ                         false
% 55.29/7.51  --qbf_dom_inst                          none
% 55.29/7.51  --qbf_dom_pre_inst                      false
% 55.29/7.51  --qbf_sk_in                             false
% 55.29/7.51  --qbf_pred_elim                         true
% 55.29/7.51  --qbf_split                             512
% 55.29/7.51  
% 55.29/7.51  ------ BMC1 Options
% 55.29/7.51  
% 55.29/7.51  --bmc1_incremental                      false
% 55.29/7.51  --bmc1_axioms                           reachable_all
% 55.29/7.51  --bmc1_min_bound                        0
% 55.29/7.51  --bmc1_max_bound                        -1
% 55.29/7.51  --bmc1_max_bound_default                -1
% 55.29/7.51  --bmc1_symbol_reachability              true
% 55.29/7.51  --bmc1_property_lemmas                  false
% 55.29/7.51  --bmc1_k_induction                      false
% 55.29/7.51  --bmc1_non_equiv_states                 false
% 55.29/7.51  --bmc1_deadlock                         false
% 55.29/7.51  --bmc1_ucm                              false
% 55.29/7.51  --bmc1_add_unsat_core                   none
% 55.29/7.51  --bmc1_unsat_core_children              false
% 55.29/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 55.29/7.51  --bmc1_out_stat                         full
% 55.29/7.51  --bmc1_ground_init                      false
% 55.29/7.51  --bmc1_pre_inst_next_state              false
% 55.29/7.51  --bmc1_pre_inst_state                   false
% 55.29/7.51  --bmc1_pre_inst_reach_state             false
% 55.29/7.51  --bmc1_out_unsat_core                   false
% 55.29/7.51  --bmc1_aig_witness_out                  false
% 55.29/7.51  --bmc1_verbose                          false
% 55.29/7.51  --bmc1_dump_clauses_tptp                false
% 55.29/7.51  --bmc1_dump_unsat_core_tptp             false
% 55.29/7.51  --bmc1_dump_file                        -
% 55.29/7.51  --bmc1_ucm_expand_uc_limit              128
% 55.29/7.51  --bmc1_ucm_n_expand_iterations          6
% 55.29/7.51  --bmc1_ucm_extend_mode                  1
% 55.29/7.51  --bmc1_ucm_init_mode                    2
% 55.29/7.51  --bmc1_ucm_cone_mode                    none
% 55.29/7.51  --bmc1_ucm_reduced_relation_type        0
% 55.29/7.51  --bmc1_ucm_relax_model                  4
% 55.29/7.51  --bmc1_ucm_full_tr_after_sat            true
% 55.29/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 55.29/7.51  --bmc1_ucm_layered_model                none
% 55.29/7.51  --bmc1_ucm_max_lemma_size               10
% 55.29/7.51  
% 55.29/7.51  ------ AIG Options
% 55.29/7.51  
% 55.29/7.51  --aig_mode                              false
% 55.29/7.51  
% 55.29/7.51  ------ Instantiation Options
% 55.29/7.51  
% 55.29/7.51  --instantiation_flag                    true
% 55.29/7.51  --inst_sos_flag                         false
% 55.29/7.51  --inst_sos_phase                        true
% 55.29/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.29/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.29/7.51  --inst_lit_sel_side                     none
% 55.29/7.51  --inst_solver_per_active                1400
% 55.29/7.51  --inst_solver_calls_frac                1.
% 55.29/7.51  --inst_passive_queue_type               priority_queues
% 55.29/7.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.29/7.51  --inst_passive_queues_freq              [25;2]
% 55.29/7.51  --inst_dismatching                      true
% 55.29/7.51  --inst_eager_unprocessed_to_passive     true
% 55.29/7.51  --inst_prop_sim_given                   true
% 55.29/7.51  --inst_prop_sim_new                     false
% 55.29/7.51  --inst_subs_new                         false
% 55.29/7.51  --inst_eq_res_simp                      false
% 55.29/7.51  --inst_subs_given                       false
% 55.29/7.51  --inst_orphan_elimination               true
% 55.29/7.51  --inst_learning_loop_flag               true
% 55.29/7.51  --inst_learning_start                   3000
% 55.29/7.51  --inst_learning_factor                  2
% 55.29/7.51  --inst_start_prop_sim_after_learn       3
% 55.29/7.51  --inst_sel_renew                        solver
% 55.29/7.51  --inst_lit_activity_flag                true
% 55.29/7.51  --inst_restr_to_given                   false
% 55.29/7.51  --inst_activity_threshold               500
% 55.29/7.51  --inst_out_proof                        true
% 55.29/7.51  
% 55.29/7.51  ------ Resolution Options
% 55.29/7.51  
% 55.29/7.51  --resolution_flag                       false
% 55.29/7.51  --res_lit_sel                           adaptive
% 55.29/7.51  --res_lit_sel_side                      none
% 55.29/7.51  --res_ordering                          kbo
% 55.29/7.51  --res_to_prop_solver                    active
% 55.29/7.51  --res_prop_simpl_new                    false
% 55.29/7.51  --res_prop_simpl_given                  true
% 55.29/7.51  --res_passive_queue_type                priority_queues
% 55.29/7.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.29/7.51  --res_passive_queues_freq               [15;5]
% 55.29/7.51  --res_forward_subs                      full
% 55.29/7.51  --res_backward_subs                     full
% 55.29/7.51  --res_forward_subs_resolution           true
% 55.29/7.51  --res_backward_subs_resolution          true
% 55.29/7.51  --res_orphan_elimination                true
% 55.29/7.51  --res_time_limit                        2.
% 55.29/7.51  --res_out_proof                         true
% 55.29/7.51  
% 55.29/7.51  ------ Superposition Options
% 55.29/7.51  
% 55.29/7.51  --superposition_flag                    true
% 55.29/7.51  --sup_passive_queue_type                priority_queues
% 55.29/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.29/7.51  --sup_passive_queues_freq               [8;1;4]
% 55.29/7.51  --demod_completeness_check              fast
% 55.29/7.51  --demod_use_ground                      true
% 55.29/7.51  --sup_to_prop_solver                    passive
% 55.29/7.51  --sup_prop_simpl_new                    true
% 55.29/7.51  --sup_prop_simpl_given                  true
% 55.29/7.51  --sup_fun_splitting                     false
% 55.29/7.51  --sup_smt_interval                      50000
% 55.29/7.51  
% 55.29/7.51  ------ Superposition Simplification Setup
% 55.29/7.51  
% 55.29/7.51  --sup_indices_passive                   []
% 55.29/7.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.29/7.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.29/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.29/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 55.29/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.29/7.51  --sup_full_bw                           [BwDemod]
% 55.29/7.51  --sup_immed_triv                        [TrivRules]
% 55.29/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.29/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.29/7.51  --sup_immed_bw_main                     []
% 55.29/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.29/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 55.29/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.29/7.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.29/7.51  
% 55.29/7.51  ------ Combination Options
% 55.29/7.51  
% 55.29/7.51  --comb_res_mult                         3
% 55.29/7.51  --comb_sup_mult                         2
% 55.29/7.51  --comb_inst_mult                        10
% 55.29/7.51  
% 55.29/7.51  ------ Debug Options
% 55.29/7.51  
% 55.29/7.51  --dbg_backtrace                         false
% 55.29/7.51  --dbg_dump_prop_clauses                 false
% 55.29/7.51  --dbg_dump_prop_clauses_file            -
% 55.29/7.51  --dbg_out_stat                          false
% 55.29/7.51  
% 55.29/7.51  
% 55.29/7.51  
% 55.29/7.51  
% 55.29/7.51  ------ Proving...
% 55.29/7.51  
% 55.29/7.51  
% 55.29/7.51  % SZS status Theorem for theBenchmark.p
% 55.29/7.51  
% 55.29/7.51   Resolution empty clause
% 55.29/7.51  
% 55.29/7.51  % SZS output start CNFRefutation for theBenchmark.p
% 55.29/7.51  
% 55.29/7.51  fof(f9,axiom,(
% 55.29/7.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f44,plain,(
% 55.29/7.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.29/7.51    inference(cnf_transformation,[],[f9])).
% 55.29/7.51  
% 55.29/7.51  fof(f7,axiom,(
% 55.29/7.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f42,plain,(
% 55.29/7.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 55.29/7.51    inference(cnf_transformation,[],[f7])).
% 55.29/7.51  
% 55.29/7.51  fof(f1,axiom,(
% 55.29/7.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f28,plain,(
% 55.29/7.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 55.29/7.51    inference(cnf_transformation,[],[f1])).
% 55.29/7.51  
% 55.29/7.51  fof(f8,axiom,(
% 55.29/7.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f43,plain,(
% 55.29/7.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 55.29/7.51    inference(cnf_transformation,[],[f8])).
% 55.29/7.51  
% 55.29/7.51  fof(f3,axiom,(
% 55.29/7.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f12,plain,(
% 55.29/7.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 55.29/7.51    inference(rectify,[],[f3])).
% 55.29/7.51  
% 55.29/7.51  fof(f14,plain,(
% 55.29/7.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 55.29/7.51    inference(ennf_transformation,[],[f12])).
% 55.29/7.51  
% 55.29/7.51  fof(f22,plain,(
% 55.29/7.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 55.29/7.51    introduced(choice_axiom,[])).
% 55.29/7.51  
% 55.29/7.51  fof(f23,plain,(
% 55.29/7.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 55.29/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f22])).
% 55.29/7.51  
% 55.29/7.51  fof(f35,plain,(
% 55.29/7.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 55.29/7.51    inference(cnf_transformation,[],[f23])).
% 55.29/7.51  
% 55.29/7.51  fof(f36,plain,(
% 55.29/7.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 55.29/7.51    inference(cnf_transformation,[],[f23])).
% 55.29/7.51  
% 55.29/7.51  fof(f2,axiom,(
% 55.29/7.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f17,plain,(
% 55.29/7.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.29/7.51    inference(nnf_transformation,[],[f2])).
% 55.29/7.51  
% 55.29/7.51  fof(f18,plain,(
% 55.29/7.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.29/7.51    inference(flattening,[],[f17])).
% 55.29/7.51  
% 55.29/7.51  fof(f19,plain,(
% 55.29/7.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.29/7.51    inference(rectify,[],[f18])).
% 55.29/7.51  
% 55.29/7.51  fof(f20,plain,(
% 55.29/7.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 55.29/7.51    introduced(choice_axiom,[])).
% 55.29/7.51  
% 55.29/7.51  fof(f21,plain,(
% 55.29/7.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.29/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 55.29/7.51  
% 55.29/7.51  fof(f30,plain,(
% 55.29/7.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 55.29/7.51    inference(cnf_transformation,[],[f21])).
% 55.29/7.51  
% 55.29/7.51  fof(f47,plain,(
% 55.29/7.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 55.29/7.51    inference(equality_resolution,[],[f30])).
% 55.29/7.51  
% 55.29/7.51  fof(f32,plain,(
% 55.29/7.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 55.29/7.51    inference(cnf_transformation,[],[f21])).
% 55.29/7.51  
% 55.29/7.51  fof(f4,axiom,(
% 55.29/7.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f13,plain,(
% 55.29/7.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.29/7.51    inference(rectify,[],[f4])).
% 55.29/7.51  
% 55.29/7.51  fof(f15,plain,(
% 55.29/7.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.29/7.51    inference(ennf_transformation,[],[f13])).
% 55.29/7.51  
% 55.29/7.51  fof(f24,plain,(
% 55.29/7.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 55.29/7.51    introduced(choice_axiom,[])).
% 55.29/7.51  
% 55.29/7.51  fof(f25,plain,(
% 55.29/7.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.29/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f24])).
% 55.29/7.51  
% 55.29/7.51  fof(f39,plain,(
% 55.29/7.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 55.29/7.51    inference(cnf_transformation,[],[f25])).
% 55.29/7.51  
% 55.29/7.51  fof(f5,axiom,(
% 55.29/7.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f40,plain,(
% 55.29/7.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.29/7.51    inference(cnf_transformation,[],[f5])).
% 55.29/7.51  
% 55.29/7.51  fof(f6,axiom,(
% 55.29/7.51    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f41,plain,(
% 55.29/7.51    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 55.29/7.51    inference(cnf_transformation,[],[f6])).
% 55.29/7.51  
% 55.29/7.51  fof(f29,plain,(
% 55.29/7.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 55.29/7.51    inference(cnf_transformation,[],[f21])).
% 55.29/7.51  
% 55.29/7.51  fof(f48,plain,(
% 55.29/7.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 55.29/7.51    inference(equality_resolution,[],[f29])).
% 55.29/7.51  
% 55.29/7.51  fof(f31,plain,(
% 55.29/7.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 55.29/7.51    inference(cnf_transformation,[],[f21])).
% 55.29/7.51  
% 55.29/7.51  fof(f46,plain,(
% 55.29/7.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 55.29/7.51    inference(equality_resolution,[],[f31])).
% 55.29/7.51  
% 55.29/7.51  fof(f10,conjecture,(
% 55.29/7.51    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 55.29/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.29/7.51  
% 55.29/7.51  fof(f11,negated_conjecture,(
% 55.29/7.51    ~! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 55.29/7.51    inference(negated_conjecture,[],[f10])).
% 55.29/7.51  
% 55.29/7.51  fof(f16,plain,(
% 55.29/7.51    ? [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)),
% 55.29/7.51    inference(ennf_transformation,[],[f11])).
% 55.29/7.51  
% 55.29/7.51  fof(f26,plain,(
% 55.29/7.51    ? [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) => k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k3_xboole_0(sK3,sK4)),
% 55.29/7.51    introduced(choice_axiom,[])).
% 55.29/7.51  
% 55.29/7.51  fof(f27,plain,(
% 55.29/7.51    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k3_xboole_0(sK3,sK4)),
% 55.29/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f26])).
% 55.29/7.51  
% 55.29/7.51  fof(f45,plain,(
% 55.29/7.51    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k3_xboole_0(sK3,sK4)),
% 55.29/7.51    inference(cnf_transformation,[],[f27])).
% 55.29/7.51  
% 55.29/7.51  cnf(c_16,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 55.29/7.51      inference(cnf_transformation,[],[f44]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_14,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(cnf_transformation,[],[f42]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_0,plain,
% 55.29/7.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(cnf_transformation,[],[f28]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_15,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 55.29/7.51      inference(cnf_transformation,[],[f43]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_790,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_0,c_15]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1138,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_14,c_790]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1144,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_1138,c_790]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1561,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_16,c_1144]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1583,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_1561,c_16]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_9,plain,
% 55.29/7.51      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 55.29/7.51      inference(cnf_transformation,[],[f35]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_418,plain,
% 55.29/7.51      ( r1_xboole_0(X0,X1) = iProver_top
% 55.29/7.51      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 55.29/7.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_8,plain,
% 55.29/7.51      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 55.29/7.51      inference(cnf_transformation,[],[f36]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_419,plain,
% 55.29/7.51      ( r1_xboole_0(X0,X1) = iProver_top
% 55.29/7.51      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 55.29/7.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_5,plain,
% 55.29/7.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 55.29/7.51      inference(cnf_transformation,[],[f47]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_422,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) != iProver_top
% 55.29/7.51      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 55.29/7.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3508,plain,
% 55.29/7.51      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 55.29/7.51      | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_419,c_422]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_93150,plain,
% 55.29/7.51      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_418,c_3508]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_97854,plain,
% 55.29/7.51      ( r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1583,c_93150]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3,plain,
% 55.29/7.51      ( r2_hidden(sK0(X0,X1,X2),X0)
% 55.29/7.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 55.29/7.51      | k4_xboole_0(X0,X1) = X2 ),
% 55.29/7.51      inference(cnf_transformation,[],[f32]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_424,plain,
% 55.29/7.51      ( k4_xboole_0(X0,X1) = X2
% 55.29/7.51      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 55.29/7.51      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 55.29/7.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_10,plain,
% 55.29/7.51      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(cnf_transformation,[],[f39]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_417,plain,
% 55.29/7.51      ( r1_xboole_0(X0,X1) != iProver_top
% 55.29/7.51      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 55.29/7.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_6368,plain,
% 55.29/7.51      ( k3_xboole_0(X0,X1) = k4_xboole_0(X2,X3)
% 55.29/7.51      | r1_xboole_0(X0,X1) != iProver_top
% 55.29/7.51      | r2_hidden(sK0(X2,X3,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_424,c_417]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1139,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_790,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1142,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_1139,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1289,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1142,c_15]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_12,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.29/7.51      inference(cnf_transformation,[],[f40]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_531,plain,
% 55.29/7.51      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_13,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 55.29/7.51      inference(cnf_transformation,[],[f41]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_592,plain,
% 55.29/7.51      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_531,c_13]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_937,plain,
% 55.29/7.51      ( k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_592,c_16]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_681,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_531,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_683,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_681,c_531]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_942,plain,
% 55.29/7.51      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_937,c_683]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_793,plain,
% 55.29/7.51      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_531,c_15]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1005,plain,
% 55.29/7.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_942,c_793]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1295,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_1289,c_1005]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1438,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_0,c_1295]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_6,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 55.29/7.51      inference(cnf_transformation,[],[f48]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_421,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) = iProver_top
% 55.29/7.51      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 55.29/7.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2196,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) = iProver_top
% 55.29/7.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1438,c_421]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_794,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_15,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_799,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_794,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1290,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1142,c_799]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_948,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_793,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_950,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_948,c_12]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_995,plain,
% 55.29/7.51      ( k2_xboole_0(X0,X0) = X0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_950,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1292,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_1290,c_995]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1591,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_0,c_1292]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2014,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_13,c_1591]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2056,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_2014,c_13]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1463,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_14,c_1438]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2257,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_2056,c_1463]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2263,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_2257,c_16]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3524,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) != iProver_top
% 55.29/7.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_2263,c_422]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_15641,plain,
% 55.29/7.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.29/7.51      inference(global_propositional_subsumption,[status(thm)],[c_2196,c_3524]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_324143,plain,
% 55.29/7.51      ( k3_xboole_0(X0,X1) = k4_xboole_0(k1_xboole_0,X2)
% 55.29/7.51      | r1_xboole_0(X0,X1) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_6368,c_15641]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_324218,plain,
% 55.29/7.51      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_324143,c_942]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_333592,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_97854,c_324218]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1469,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1438,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1471,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_1469,c_12]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1968,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_0,c_1471]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2737,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_14,c_1968]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2789,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_2737,c_1968]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2973,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_16,c_2789]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3048,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_2973,c_13]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3555,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_16,c_3048]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_337632,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) = k3_xboole_0(X0,X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_333592,c_3555]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_792,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2253,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,k3_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_2056,c_792]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2268,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_2253,c_16]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_337675,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) = k3_xboole_0(X0,X1) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_337632,c_2268]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3564,plain,
% 55.29/7.51      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k2_xboole_0(X1,X0))) = X0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1438,c_3048]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4644,plain,
% 55.29/7.51      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_3564,c_531]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2412,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_2263,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2416,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_2412,c_12]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2445,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_2416,c_1591]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2465,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_2445,c_2416]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_10245,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_2268,c_2465]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1983,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1471,c_0]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3554,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_15,c_3048]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_10611,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_3554,c_1968]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1713,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_0,c_1463]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3002,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_2789,c_0]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2980,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1295,c_2789]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2760,plain,
% 55.29/7.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1968,c_0]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3036,plain,
% 55.29/7.51      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_2980,c_2760]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3276,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_3002,c_3036]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3355,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_3276,c_3036]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4548,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1713,c_3355]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4586,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_4548,c_3036]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_10673,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_10611,c_4586]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_43411,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_10673,c_1295]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_43815,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1983,c_43411]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_44311,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_43815,c_1591]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_44757,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X0))) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X0)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_44311,c_10245]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_45026,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_44757,c_13,c_683]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_48004,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k2_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1142,c_45026]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_48578,plain,
% 55.29/7.51      ( k3_xboole_0(k2_xboole_0(X0,X1),X1) = k3_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 55.29/7.51      inference(light_normalisation,
% 55.29/7.51                [status(thm)],
% 55.29/7.51                [c_48004,c_1968,c_2760,c_45026]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_51011,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)),k3_xboole_0(k2_xboole_0(X1,X0),X1)) = k3_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_48578,c_10245]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1341,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_0,c_792]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_51324,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_51011,c_15,c_1341]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_10207,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_15,c_2268]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_10393,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_10207,c_15,c_1341]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_58081,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k3_xboole_0(k2_xboole_0(X1,X0),X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X1)),k3_xboole_0(k2_xboole_0(X1,X0),X1))) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X1)),k3_xboole_0(k2_xboole_0(X1,X0),X1))) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_51324,c_10393]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_10248,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_2268,c_2263]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_14095,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_790,c_10248]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_14300,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_14095,c_792]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_58352,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k3_xboole_0(k2_xboole_0(X1,X0),X1)) = k3_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_58081,c_683,c_14300]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_58092,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X0),k3_xboole_0(k2_xboole_0(X0,X1),X0))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_51324,c_3554]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_58326,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),X0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X0),k3_xboole_0(k2_xboole_0(X0,X1),X0))) = k3_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_58092,c_51324]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_58328,plain,
% 55.29/7.51      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k3_xboole_0(k2_xboole_0(X1,X0),X1))) = k3_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_58326,c_14300]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_58353,plain,
% 55.29/7.51      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_58352,c_58328]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1447,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1295,c_792]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1451,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_1447,c_1295]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1453,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_1451,c_683]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_6238,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_1453,c_1968]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3203,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_16,c_3002]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3263,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_3203,c_13]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_6274,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_6238,c_3263]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_136956,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0),k1_xboole_0),k3_xboole_0(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_58353,c_6274]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_137018,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0),k3_xboole_0(k2_xboole_0(X1,X0),X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_136956,c_12]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_181425,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k3_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_0,c_137018]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_10221,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_6238,c_2268]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1465,plain,
% 55.29/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_799,c_1438]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_10361,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_10221,c_1465,c_6238]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_14093,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_16,c_10248]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_16855,plain,
% 55.29/7.51      ( k4_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k1_xboole_0),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_10361,c_14093]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_17018,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0))) = k1_xboole_0 ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_16855,c_16,c_683]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_32165,plain,
% 55.29/7.51      ( k2_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)),k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_17018,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_32168,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_32165,c_12,c_2056]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_32176,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_0,c_32168]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_136853,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k3_xboole_0(k2_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X1),k1_xboole_0),k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_58353,c_32176]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4780,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_3048,c_4644]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_137220,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k1_xboole_0) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X0),k1_xboole_0) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_136853,c_12,c_4780]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_222516,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0)),k3_xboole_0(k2_xboole_0(X0,X1),X1)),k1_xboole_0) = k3_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)),k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_181425,c_137220]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3559,plain,
% 55.29/7.51      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1005,c_3048]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4066,plain,
% 55.29/7.51      ( k3_xboole_0(X0,X0) = X0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_3559,c_531]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_222804,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),k3_xboole_0(k2_xboole_0(X1,X0),X0)),k1_xboole_0) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X0),X0),k1_xboole_0) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_222516,c_13,c_4066]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1137,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_13,c_790]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1148,plain,
% 55.29/7.51      ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_1137,c_1005]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4,plain,
% 55.29/7.51      ( ~ r2_hidden(X0,X1)
% 55.29/7.51      | r2_hidden(X0,X2)
% 55.29/7.51      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 55.29/7.51      inference(cnf_transformation,[],[f46]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_423,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) != iProver_top
% 55.29/7.51      | r2_hidden(X0,X2) = iProver_top
% 55.29/7.51      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 55.29/7.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4883,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) = iProver_top
% 55.29/7.51      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 55.29/7.51      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1148,c_423]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_221903,plain,
% 55.29/7.51      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 55.29/7.51      | r2_hidden(X0,X1) = iProver_top ),
% 55.29/7.51      inference(global_propositional_subsumption,
% 55.29/7.51                [status(thm)],
% 55.29/7.51                [c_4883,c_2196,c_3524]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_221904,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) = iProver_top
% 55.29/7.51      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 55.29/7.51      inference(renaming,[status(thm)],[c_221903]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_262367,plain,
% 55.29/7.51      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X1),k3_xboole_0(k2_xboole_0(X2,X1),X1))) = iProver_top
% 55.29/7.51      | r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X2,X1),X1),k1_xboole_0)) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_222804,c_221904]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3896,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_683,c_1583]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_3967,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_3896,c_683]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4289,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) != iProver_top
% 55.29/7.51      | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_3967,c_422]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_262397,plain,
% 55.29/7.51      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X1),k3_xboole_0(k2_xboole_0(X2,X1),X1))) != iProver_top
% 55.29/7.51      | r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X2,X1),X1),k1_xboole_0)) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_222804,c_4289]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_262449,plain,
% 55.29/7.51      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X2),k1_xboole_0)) != iProver_top ),
% 55.29/7.51      inference(forward_subsumption_resolution,
% 55.29/7.51                [status(thm)],
% 55.29/7.51                [c_262367,c_262397]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_263935,plain,
% 55.29/7.51      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)),k1_xboole_0)) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_10245,c_262449]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_264058,plain,
% 55.29/7.51      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)) != iProver_top ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_263935,c_4066]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_264085,plain,
% 55.29/7.51      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_4644,c_264058]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_264561,plain,
% 55.29/7.51      ( r1_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_419,c_264085]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_333657,plain,
% 55.29/7.51      ( k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_264561,c_324218]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1726,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_1463,c_14]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_1728,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_1726,c_12]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_5121,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_2789,c_1728]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_5237,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_5121,c_3355]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_32223,plain,
% 55.29/7.51      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0))) = k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_5237,c_32168]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2614,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_15,c_2465]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_6759,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_3002,c_2614]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_6881,plain,
% 55.29/7.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_6759,c_3002]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_32544,plain,
% 55.29/7.51      ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))),k1_xboole_0) = k3_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_32223,c_6881,c_32168]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_2431,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_15,c_2416]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_6559,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_3002,c_2431]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_6727,plain,
% 55.29/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_6559,c_3002]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_32545,plain,
% 55.29/7.51      ( k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_32544,c_6727]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4280,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_3967,c_1583]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_4308,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 55.29/7.51      inference(light_normalisation,[status(thm)],[c_4280,c_3967]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_5900,plain,
% 55.29/7.51      ( r2_hidden(X0,X1) != iProver_top
% 55.29/7.51      | r2_hidden(X0,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) != iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_4308,c_422]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_245067,plain,
% 55.29/7.51      ( r2_hidden(X0,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) != iProver_top ),
% 55.29/7.51      inference(forward_subsumption_resolution,[status(thm)],[c_5900,c_221904]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_245073,plain,
% 55.29/7.51      ( r1_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_419,c_245067]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_252864,plain,
% 55.29/7.51      ( r1_xboole_0(X0,k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0))) = iProver_top ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_32545,c_245073]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_333673,plain,
% 55.29/7.51      ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0))) = k1_xboole_0 ),
% 55.29/7.51      inference(superposition,[status(thm)],[c_252864,c_324218]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_333739,plain,
% 55.29/7.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_333657,c_333673]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_337676,plain,
% 55.29/7.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_337675,c_12,c_333739]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_17,negated_conjecture,
% 55.29/7.51      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) != k3_xboole_0(sK3,sK4) ),
% 55.29/7.51      inference(cnf_transformation,[],[f45]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_339196,plain,
% 55.29/7.51      ( k3_xboole_0(sK3,sK4) != k3_xboole_0(sK3,sK4) ),
% 55.29/7.51      inference(demodulation,[status(thm)],[c_337676,c_17]) ).
% 55.29/7.51  
% 55.29/7.51  cnf(c_339256,plain,
% 55.29/7.51      ( $false ),
% 55.29/7.51      inference(equality_resolution_simp,[status(thm)],[c_339196]) ).
% 55.29/7.51  
% 55.29/7.51  
% 55.29/7.51  % SZS output end CNFRefutation for theBenchmark.p
% 55.29/7.51  
% 55.29/7.51  ------                               Statistics
% 55.29/7.51  
% 55.29/7.51  ------ General
% 55.29/7.51  
% 55.29/7.51  abstr_ref_over_cycles:                  0
% 55.29/7.51  abstr_ref_under_cycles:                 0
% 55.29/7.51  gc_basic_clause_elim:                   0
% 55.29/7.51  forced_gc_time:                         0
% 55.29/7.51  parsing_time:                           0.01
% 55.29/7.51  unif_index_cands_time:                  0.
% 55.29/7.51  unif_index_add_time:                    0.
% 55.29/7.51  orderings_time:                         0.
% 55.29/7.51  out_proof_time:                         0.018
% 55.29/7.51  total_time:                             6.888
% 55.29/7.51  num_of_symbols:                         42
% 55.29/7.51  num_of_terms:                           355161
% 55.29/7.51  
% 55.29/7.51  ------ Preprocessing
% 55.29/7.51  
% 55.29/7.51  num_of_splits:                          0
% 55.29/7.51  num_of_split_atoms:                     0
% 55.29/7.51  num_of_reused_defs:                     0
% 55.29/7.51  num_eq_ax_congr_red:                    20
% 55.29/7.51  num_of_sem_filtered_clauses:            1
% 55.29/7.51  num_of_subtypes:                        0
% 55.29/7.51  monotx_restored_types:                  0
% 55.29/7.51  sat_num_of_epr_types:                   0
% 55.29/7.51  sat_num_of_non_cyclic_types:            0
% 55.29/7.51  sat_guarded_non_collapsed_types:        0
% 55.29/7.51  num_pure_diseq_elim:                    0
% 55.29/7.51  simp_replaced_by:                       0
% 55.29/7.51  res_preprocessed:                       67
% 55.29/7.51  prep_upred:                             0
% 55.29/7.51  prep_unflattend:                        0
% 55.29/7.51  smt_new_axioms:                         0
% 55.29/7.51  pred_elim_cands:                        2
% 55.29/7.51  pred_elim:                              0
% 55.29/7.51  pred_elim_cl:                           0
% 55.29/7.51  pred_elim_cycles:                       1
% 55.29/7.51  merged_defs:                            0
% 55.29/7.51  merged_defs_ncl:                        0
% 55.29/7.51  bin_hyper_res:                          0
% 55.29/7.51  prep_cycles:                            3
% 55.29/7.51  pred_elim_time:                         0.001
% 55.29/7.51  splitting_time:                         0.
% 55.29/7.51  sem_filter_time:                        0.
% 55.29/7.51  monotx_time:                            0.
% 55.29/7.51  subtype_inf_time:                       0.
% 55.29/7.51  
% 55.29/7.51  ------ Problem properties
% 55.29/7.51  
% 55.29/7.51  clauses:                                18
% 55.29/7.51  conjectures:                            1
% 55.29/7.51  epr:                                    1
% 55.29/7.51  horn:                                   11
% 55.29/7.51  ground:                                 1
% 55.29/7.51  unary:                                  7
% 55.29/7.51  binary:                                 6
% 55.29/7.51  lits:                                   35
% 55.29/7.51  lits_eq:                                10
% 55.29/7.51  fd_pure:                                0
% 55.29/7.51  fd_pseudo:                              0
% 55.29/7.51  fd_cond:                                0
% 55.29/7.51  fd_pseudo_cond:                         3
% 55.29/7.51  ac_symbols:                             0
% 55.29/7.51  
% 55.29/7.51  ------ Propositional Solver
% 55.29/7.51  
% 55.29/7.51  prop_solver_calls:                      37
% 55.29/7.51  prop_fast_solver_calls:                 949
% 55.29/7.51  smt_solver_calls:                       0
% 55.29/7.51  smt_fast_solver_calls:                  0
% 55.29/7.51  prop_num_of_clauses:                    36798
% 55.29/7.51  prop_preprocess_simplified:             41473
% 55.29/7.51  prop_fo_subsumed:                       6
% 55.29/7.51  prop_solver_time:                       0.
% 55.29/7.51  smt_solver_time:                        0.
% 55.29/7.51  smt_fast_solver_time:                   0.
% 55.29/7.51  prop_fast_solver_time:                  0.
% 55.29/7.51  prop_unsat_core_time:                   0.
% 55.29/7.51  
% 55.29/7.51  ------ QBF
% 55.29/7.51  
% 55.29/7.51  qbf_q_res:                              0
% 55.29/7.51  qbf_num_tautologies:                    0
% 55.29/7.51  qbf_prep_cycles:                        0
% 55.29/7.51  
% 55.29/7.51  ------ BMC1
% 55.29/7.51  
% 55.29/7.51  bmc1_current_bound:                     -1
% 55.29/7.51  bmc1_last_solved_bound:                 -1
% 55.29/7.51  bmc1_unsat_core_size:                   -1
% 55.29/7.51  bmc1_unsat_core_parents_size:           -1
% 55.29/7.51  bmc1_merge_next_fun:                    0
% 55.29/7.51  bmc1_unsat_core_clauses_time:           0.
% 55.29/7.51  
% 55.29/7.51  ------ Instantiation
% 55.29/7.51  
% 55.29/7.51  inst_num_of_clauses:                    5604
% 55.29/7.51  inst_num_in_passive:                    2155
% 55.29/7.51  inst_num_in_active:                     1293
% 55.29/7.51  inst_num_in_unprocessed:                2156
% 55.29/7.51  inst_num_of_loops:                      2310
% 55.29/7.51  inst_num_of_learning_restarts:          0
% 55.29/7.51  inst_num_moves_active_passive:          1013
% 55.29/7.51  inst_lit_activity:                      0
% 55.29/7.51  inst_lit_activity_moves:                1
% 55.29/7.51  inst_num_tautologies:                   0
% 55.29/7.51  inst_num_prop_implied:                  0
% 55.29/7.51  inst_num_existing_simplified:           0
% 55.29/7.51  inst_num_eq_res_simplified:             0
% 55.29/7.51  inst_num_child_elim:                    0
% 55.29/7.51  inst_num_of_dismatching_blockings:      21666
% 55.29/7.51  inst_num_of_non_proper_insts:           10152
% 55.29/7.51  inst_num_of_duplicates:                 0
% 55.29/7.51  inst_inst_num_from_inst_to_res:         0
% 55.29/7.51  inst_dismatching_checking_time:         0.
% 55.29/7.51  
% 55.29/7.51  ------ Resolution
% 55.29/7.51  
% 55.29/7.51  res_num_of_clauses:                     0
% 55.29/7.51  res_num_in_passive:                     0
% 55.29/7.51  res_num_in_active:                      0
% 55.29/7.51  res_num_of_loops:                       70
% 55.29/7.51  res_forward_subset_subsumed:            662
% 55.29/7.51  res_backward_subset_subsumed:           0
% 55.29/7.51  res_forward_subsumed:                   0
% 55.29/7.51  res_backward_subsumed:                  0
% 55.29/7.51  res_forward_subsumption_resolution:     0
% 55.29/7.51  res_backward_subsumption_resolution:    0
% 55.29/7.51  res_clause_to_clause_subsumption:       276597
% 55.29/7.51  res_orphan_elimination:                 0
% 55.29/7.51  res_tautology_del:                      861
% 55.29/7.51  res_num_eq_res_simplified:              0
% 55.29/7.51  res_num_sel_changes:                    0
% 55.29/7.51  res_moves_from_active_to_pass:          0
% 55.29/7.51  
% 55.29/7.51  ------ Superposition
% 55.29/7.51  
% 55.29/7.51  sup_time_total:                         0.
% 55.29/7.51  sup_time_generating:                    0.
% 55.29/7.51  sup_time_sim_full:                      0.
% 55.29/7.51  sup_time_sim_immed:                     0.
% 55.29/7.51  
% 55.29/7.51  sup_num_of_clauses:                     9207
% 55.29/7.51  sup_num_in_active:                      242
% 55.29/7.51  sup_num_in_passive:                     8965
% 55.29/7.51  sup_num_of_loops:                       461
% 55.29/7.51  sup_fw_superposition:                   64016
% 55.29/7.51  sup_bw_superposition:                   35349
% 55.29/7.51  sup_immediate_simplified:               73021
% 55.29/7.51  sup_given_eliminated:                   5
% 55.29/7.51  comparisons_done:                       0
% 55.29/7.51  comparisons_avoided:                    0
% 55.29/7.51  
% 55.29/7.51  ------ Simplifications
% 55.29/7.51  
% 55.29/7.51  
% 55.29/7.51  sim_fw_subset_subsumed:                 328
% 55.29/7.51  sim_bw_subset_subsumed:                 34
% 55.29/7.51  sim_fw_subsumed:                        14149
% 55.29/7.51  sim_bw_subsumed:                        67
% 55.29/7.51  sim_fw_subsumption_res:                 5
% 55.29/7.51  sim_bw_subsumption_res:                 1
% 55.29/7.51  sim_tautology_del:                      273
% 55.29/7.51  sim_eq_tautology_del:                   17023
% 55.29/7.51  sim_eq_res_simp:                        3
% 55.29/7.51  sim_fw_demodulated:                     33027
% 55.29/7.51  sim_bw_demodulated:                     1454
% 55.29/7.51  sim_light_normalised:                   46247
% 55.29/7.51  sim_joinable_taut:                      0
% 55.29/7.51  sim_joinable_simp:                      0
% 55.29/7.51  sim_ac_normalised:                      0
% 55.29/7.51  sim_smt_subsumption:                    0
% 55.29/7.51  
%------------------------------------------------------------------------------
