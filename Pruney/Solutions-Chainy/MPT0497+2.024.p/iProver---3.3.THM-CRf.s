%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:50 EST 2020

% Result     : Theorem 31.19s
% Output     : CNFRefutation 31.19s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_6269)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f16,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
        | k1_xboole_0 != k7_relat_1(sK2,sK1) )
      & ( r1_xboole_0(k1_relat_1(sK2),sK1)
        | k1_xboole_0 = k7_relat_1(sK2,sK1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
      | k1_xboole_0 != k7_relat_1(sK2,sK1) )
    & ( r1_xboole_0(k1_relat_1(sK2),sK1)
      | k1_xboole_0 = k7_relat_1(sK2,sK1) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f32])).

fof(f56,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f55,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_767,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_768,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_756,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_770,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1442,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_770])).

cnf(c_1532,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_770])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_771,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2035,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1532,c_771])).

cnf(c_6,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_766,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1441,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_766,c_770])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_764,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1790,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1441,c_764])).

cnf(c_2969,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k4_xboole_0(k4_xboole_0(k1_relat_1(sK2),sK1),k1_xboole_0) = k4_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(superposition,[status(thm)],[c_2035,c_1790])).

cnf(c_1533,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,k1_relat_1(sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_1442,c_764])).

cnf(c_2038,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k1_relat_1(sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1442,c_771])).

cnf(c_2385,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1533,c_2038])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_758,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2819,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_758])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2839,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0
    | r2_hidden(X0,sK1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2819,c_12])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1457,plain,
    ( r1_xboole_0(k1_xboole_0,X0)
    | ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[status(thm)],[c_0,c_8])).

cnf(c_961,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[status(thm)],[c_2,c_6])).

cnf(c_1689,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1457,c_961])).

cnf(c_1864,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3,c_1689])).

cnf(c_1865,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1864])).

cnf(c_3452,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2839,c_1865])).

cnf(c_3457,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_3452])).

cnf(c_5482,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3457,c_771])).

cnf(c_772,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6205,plain,
    ( k4_xboole_0(X0,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5482,c_772])).

cnf(c_7455,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK2),sK1) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),sK1),k4_xboole_0(k4_xboole_0(k1_relat_1(sK2),sK1),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2969,c_6205])).

cnf(c_1542,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1532])).

cnf(c_267,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_266,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3023,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_267,c_266])).

cnf(c_272,plain,
    ( X0 != X1
    | X2 != X3
    | k7_relat_1(X0,X2) = k7_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_3535,plain,
    ( X0 != X1
    | X2 != X3
    | k7_relat_1(X1,X3) = k7_relat_1(X0,X2) ),
    inference(resolution,[status(thm)],[c_3023,c_272])).

cnf(c_3021,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | X0 != k7_relat_1(sK2,sK1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_267,c_19])).

cnf(c_107526,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | sK1 != X0
    | sK2 != X1
    | k1_xboole_0 = k7_relat_1(X1,X0) ),
    inference(resolution,[status(thm)],[c_3535,c_3021])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_285,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_916,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2813,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1209,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,X0))
    | k1_relat_1(k7_relat_1(sK2,X0)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_79663,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1209])).

cnf(c_1223,plain,
    ( X0 != X1
    | X0 = k7_relat_1(sK2,X2)
    | k7_relat_1(sK2,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_79668,plain,
    ( k7_relat_1(sK2,sK1) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1223])).

cnf(c_79669,plain,
    ( k7_relat_1(sK2,sK1) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK2,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_79668])).

cnf(c_755,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_759,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2059,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),k1_relat_1(X0)) = iProver_top
    | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_767,c_759])).

cnf(c_769,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6992,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),X3) != iProver_top
    | r1_xboole_0(X3,k1_relat_1(X0)) != iProver_top
    | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2059,c_769])).

cnf(c_66640,plain,
    ( r1_xboole_0(X0,k1_relat_1(X1)) != iProver_top
    | r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_6992])).

cnf(c_99244,plain,
    ( r1_xboole_0(X0,k1_relat_1(X1)) != iProver_top
    | r1_xboole_0(X0,k1_relat_1(k7_relat_1(X1,X2))) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_66640,c_770])).

cnf(c_104015,plain,
    ( k4_xboole_0(X0,k1_relat_1(k7_relat_1(X1,X2))) = X0
    | r1_xboole_0(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_99244,c_764])).

cnf(c_104143,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_relat_1(X1)),k1_relat_1(k7_relat_1(X1,X2))) = k4_xboole_0(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_766,c_104015])).

cnf(c_104612,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,X1))) = k4_xboole_0(X0,k1_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_755,c_104143])).

cnf(c_105004,plain,
    ( k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),k4_xboole_0(X1,k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_104612,c_1790])).

cnf(c_1302,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(sK2),sK1) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_756,c_764])).

cnf(c_1525,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),X1) = iProver_top
    | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_767,c_758])).

cnf(c_3984,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),X3) != iProver_top
    | r1_xboole_0(X3,X1) != iProver_top
    | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_769])).

cnf(c_15634,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k1_relat_1(k7_relat_1(X2,X1)),X0) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_3984])).

cnf(c_26152,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15634,c_770])).

cnf(c_30301,plain,
    ( k4_xboole_0(X0,k1_relat_1(k7_relat_1(X1,X2))) = X0
    | r1_xboole_0(X0,X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_26152,c_764])).

cnf(c_30348,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k1_relat_1(k7_relat_1(X2,X1))) = k4_xboole_0(X0,X1)
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_766,c_30301])).

cnf(c_30815,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k1_relat_1(k7_relat_1(sK2,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_755,c_30348])).

cnf(c_30929,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_30815,c_1441])).

cnf(c_31833,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_30929])).

cnf(c_58216,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k4_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_31833,c_771])).

cnf(c_105786,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_105004,c_58216])).

cnf(c_107904,plain,
    ( sK1 != X0
    | sK2 != X1
    | k1_xboole_0 = k7_relat_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_107526,c_20,c_18,c_285,c_2813,c_79663,c_79669,c_105786])).

cnf(c_108546,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | sK1 != sK1
    | sK2 != sK2 ),
    inference(resolution,[status(thm)],[c_107904,c_18])).

cnf(c_108547,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_108546])).

cnf(c_118876,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7455,c_20,c_18,c_285,c_2813,c_6269,c_79663,c_79669,c_105786])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_760,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_118897,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_118876,c_760])).

cnf(c_119317,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_118897,c_12])).

cnf(c_23,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_270,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_275,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_3377,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X2,k1_relat_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_270,c_275])).

cnf(c_12597,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1(sK2),sK1)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_3377,c_19])).

cnf(c_13015,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X0,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_12597,c_15])).

cnf(c_18053,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | ~ r2_hidden(X0,sK1)
    | r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X0,k1_relat_1(sK2))
    | X1 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13015,c_20])).

cnf(c_18054,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X0,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1)
    | X1 != X0 ),
    inference(renaming,[status(thm)],[c_18053])).

cnf(c_18539,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X0,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(resolution,[status(thm)],[c_18054,c_266])).

cnf(c_18540,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18539])).

cnf(c_3530,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3023,c_19])).

cnf(c_12613,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1(sK2),sK1)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_3377,c_3530])).

cnf(c_15307,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(resolution,[status(thm)],[c_12613,c_266])).

cnf(c_268,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3339,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | r1_xboole_0(X2,k1_relat_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_268,c_275])).

cnf(c_10872,plain,
    ( r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r1_xboole_0(X1,k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1(sK2),sK1)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_3339,c_3530])).

cnf(c_13828,plain,
    ( r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r1_xboole_0(X0,k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(resolution,[status(thm)],[c_10872,c_266])).

cnf(c_3325,plain,
    ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0))
    | ~ r1_xboole_0(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_268,c_12])).

cnf(c_2078,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1864,c_4])).

cnf(c_5571,plain,
    ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0))
    | X0 != X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3325,c_2078])).

cnf(c_20306,plain,
    ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_5571,c_266])).

cnf(c_25447,plain,
    ( r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13828,c_20306])).

cnf(c_25469,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(resolution,[status(thm)],[c_25447,c_3])).

cnf(c_27573,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15307,c_25469])).

cnf(c_27574,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27573])).

cnf(c_119502,plain,
    ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_119317,c_20,c_23,c_285,c_2813,c_18540,c_27574,c_79663,c_79669,c_105786])).

cnf(c_119508,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK2)),sK1) != iProver_top
    | r1_xboole_0(X0,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_119502])).

cnf(c_120434,plain,
    ( r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_767,c_119508])).

cnf(c_1389,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | ~ r1_xboole_0(sK1,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1390,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top
    | r1_xboole_0(sK1,k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_120434,c_108547,c_1390,c_23,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:21:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.19/4.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.19/4.50  
% 31.19/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.19/4.50  
% 31.19/4.50  ------  iProver source info
% 31.19/4.50  
% 31.19/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.19/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.19/4.50  git: non_committed_changes: false
% 31.19/4.50  git: last_make_outside_of_git: false
% 31.19/4.50  
% 31.19/4.50  ------ 
% 31.19/4.50  ------ Parsing...
% 31.19/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.19/4.50  
% 31.19/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.19/4.50  
% 31.19/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.19/4.50  
% 31.19/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.19/4.50  ------ Proving...
% 31.19/4.50  ------ Problem Properties 
% 31.19/4.50  
% 31.19/4.50  
% 31.19/4.50  clauses                                 21
% 31.19/4.50  conjectures                             3
% 31.19/4.50  EPR                                     3
% 31.19/4.50  Horn                                    18
% 31.19/4.50  unary                                   5
% 31.19/4.50  binary                                  10
% 31.19/4.50  lits                                    44
% 31.19/4.50  lits eq                                 13
% 31.19/4.50  fd_pure                                 0
% 31.19/4.50  fd_pseudo                               0
% 31.19/4.50  fd_cond                                 2
% 31.19/4.50  fd_pseudo_cond                          0
% 31.19/4.50  AC symbols                              0
% 31.19/4.50  
% 31.19/4.50  ------ Input Options Time Limit: Unbounded
% 31.19/4.50  
% 31.19/4.50  
% 31.19/4.50  ------ 
% 31.19/4.50  Current options:
% 31.19/4.50  ------ 
% 31.19/4.50  
% 31.19/4.50  
% 31.19/4.50  
% 31.19/4.50  
% 31.19/4.50  ------ Proving...
% 31.19/4.50  
% 31.19/4.50  
% 31.19/4.50  % SZS status Theorem for theBenchmark.p
% 31.19/4.50  
% 31.19/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.19/4.50  
% 31.19/4.50  fof(f3,axiom,(
% 31.19/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f16,plain,(
% 31.19/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 31.19/4.50    inference(rectify,[],[f3])).
% 31.19/4.50  
% 31.19/4.50  fof(f18,plain,(
% 31.19/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 31.19/4.50    inference(ennf_transformation,[],[f16])).
% 31.19/4.50  
% 31.19/4.50  fof(f25,plain,(
% 31.19/4.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 31.19/4.50    introduced(choice_axiom,[])).
% 31.19/4.50  
% 31.19/4.50  fof(f26,plain,(
% 31.19/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 31.19/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).
% 31.19/4.50  
% 31.19/4.50  fof(f37,plain,(
% 31.19/4.50    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f26])).
% 31.19/4.50  
% 31.19/4.50  fof(f38,plain,(
% 31.19/4.50    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f26])).
% 31.19/4.50  
% 31.19/4.50  fof(f14,conjecture,(
% 31.19/4.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f15,negated_conjecture,(
% 31.19/4.50    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 31.19/4.50    inference(negated_conjecture,[],[f14])).
% 31.19/4.50  
% 31.19/4.50  fof(f23,plain,(
% 31.19/4.50    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 31.19/4.50    inference(ennf_transformation,[],[f15])).
% 31.19/4.50  
% 31.19/4.50  fof(f30,plain,(
% 31.19/4.50    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 31.19/4.50    inference(nnf_transformation,[],[f23])).
% 31.19/4.50  
% 31.19/4.50  fof(f31,plain,(
% 31.19/4.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 31.19/4.50    inference(flattening,[],[f30])).
% 31.19/4.50  
% 31.19/4.50  fof(f32,plain,(
% 31.19/4.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)) & (r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 31.19/4.50    introduced(choice_axiom,[])).
% 31.19/4.50  
% 31.19/4.50  fof(f33,plain,(
% 31.19/4.50    (~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)) & (r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 31.19/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f32])).
% 31.19/4.50  
% 31.19/4.50  fof(f56,plain,(
% 31.19/4.50    r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)),
% 31.19/4.50    inference(cnf_transformation,[],[f33])).
% 31.19/4.50  
% 31.19/4.50  fof(f2,axiom,(
% 31.19/4.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f17,plain,(
% 31.19/4.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 31.19/4.50    inference(ennf_transformation,[],[f2])).
% 31.19/4.50  
% 31.19/4.50  fof(f36,plain,(
% 31.19/4.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f17])).
% 31.19/4.50  
% 31.19/4.50  fof(f1,axiom,(
% 31.19/4.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f24,plain,(
% 31.19/4.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 31.19/4.50    inference(nnf_transformation,[],[f1])).
% 31.19/4.50  
% 31.19/4.50  fof(f34,plain,(
% 31.19/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f24])).
% 31.19/4.50  
% 31.19/4.50  fof(f4,axiom,(
% 31.19/4.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f40,plain,(
% 31.19/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.19/4.50    inference(cnf_transformation,[],[f4])).
% 31.19/4.50  
% 31.19/4.50  fof(f60,plain,(
% 31.19/4.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 31.19/4.50    inference(definition_unfolding,[],[f34,f40])).
% 31.19/4.50  
% 31.19/4.50  fof(f5,axiom,(
% 31.19/4.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f41,plain,(
% 31.19/4.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f5])).
% 31.19/4.50  
% 31.19/4.50  fof(f6,axiom,(
% 31.19/4.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f27,plain,(
% 31.19/4.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 31.19/4.50    inference(nnf_transformation,[],[f6])).
% 31.19/4.50  
% 31.19/4.50  fof(f42,plain,(
% 31.19/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f27])).
% 31.19/4.50  
% 31.19/4.50  fof(f13,axiom,(
% 31.19/4.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f22,plain,(
% 31.19/4.50    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 31.19/4.50    inference(ennf_transformation,[],[f13])).
% 31.19/4.50  
% 31.19/4.50  fof(f28,plain,(
% 31.19/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 31.19/4.50    inference(nnf_transformation,[],[f22])).
% 31.19/4.50  
% 31.19/4.50  fof(f29,plain,(
% 31.19/4.50    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 31.19/4.50    inference(flattening,[],[f28])).
% 31.19/4.50  
% 31.19/4.50  fof(f52,plain,(
% 31.19/4.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f29])).
% 31.19/4.50  
% 31.19/4.50  fof(f11,axiom,(
% 31.19/4.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f48,plain,(
% 31.19/4.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 31.19/4.50    inference(cnf_transformation,[],[f11])).
% 31.19/4.50  
% 31.19/4.50  fof(f39,plain,(
% 31.19/4.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f26])).
% 31.19/4.50  
% 31.19/4.50  fof(f35,plain,(
% 31.19/4.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 31.19/4.50    inference(cnf_transformation,[],[f24])).
% 31.19/4.50  
% 31.19/4.50  fof(f59,plain,(
% 31.19/4.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.19/4.50    inference(definition_unfolding,[],[f35,f40])).
% 31.19/4.50  
% 31.19/4.50  fof(f55,plain,(
% 31.19/4.50    v1_relat_1(sK2)),
% 31.19/4.50    inference(cnf_transformation,[],[f33])).
% 31.19/4.50  
% 31.19/4.50  fof(f57,plain,(
% 31.19/4.50    ~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)),
% 31.19/4.50    inference(cnf_transformation,[],[f33])).
% 31.19/4.50  
% 31.19/4.50  fof(f10,axiom,(
% 31.19/4.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f19,plain,(
% 31.19/4.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 31.19/4.50    inference(ennf_transformation,[],[f10])).
% 31.19/4.50  
% 31.19/4.50  fof(f47,plain,(
% 31.19/4.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f19])).
% 31.19/4.50  
% 31.19/4.50  fof(f12,axiom,(
% 31.19/4.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 31.19/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.19/4.50  
% 31.19/4.50  fof(f20,plain,(
% 31.19/4.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 31.19/4.50    inference(ennf_transformation,[],[f12])).
% 31.19/4.50  
% 31.19/4.50  fof(f21,plain,(
% 31.19/4.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 31.19/4.50    inference(flattening,[],[f20])).
% 31.19/4.50  
% 31.19/4.50  fof(f50,plain,(
% 31.19/4.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f21])).
% 31.19/4.50  
% 31.19/4.50  fof(f53,plain,(
% 31.19/4.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f29])).
% 31.19/4.50  
% 31.19/4.50  fof(f54,plain,(
% 31.19/4.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 31.19/4.50    inference(cnf_transformation,[],[f29])).
% 31.19/4.50  
% 31.19/4.50  cnf(c_5,plain,
% 31.19/4.50      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 31.19/4.50      inference(cnf_transformation,[],[f37]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_767,plain,
% 31.19/4.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 31.19/4.50      | r1_xboole_0(X0,X1) = iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_4,plain,
% 31.19/4.50      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 31.19/4.50      inference(cnf_transformation,[],[f38]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_768,plain,
% 31.19/4.50      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 31.19/4.50      | r1_xboole_0(X0,X1) = iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_19,negated_conjecture,
% 31.19/4.50      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
% 31.19/4.50      inference(cnf_transformation,[],[f56]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_756,plain,
% 31.19/4.50      ( k1_xboole_0 = k7_relat_1(sK2,sK1)
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2,plain,
% 31.19/4.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 31.19/4.50      inference(cnf_transformation,[],[f36]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_770,plain,
% 31.19/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.19/4.50      | r1_xboole_0(X1,X0) = iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1442,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_756,c_770]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1532,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_1442,c_770]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1,plain,
% 31.19/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.19/4.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 31.19/4.50      inference(cnf_transformation,[],[f60]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_771,plain,
% 31.19/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 31.19/4.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2035,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),sK1)) = k1_xboole_0 ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_1532,c_771]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_6,plain,
% 31.19/4.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 31.19/4.50      inference(cnf_transformation,[],[f41]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_766,plain,
% 31.19/4.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1441,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_766,c_770]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_8,plain,
% 31.19/4.50      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 31.19/4.50      inference(cnf_transformation,[],[f42]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_764,plain,
% 31.19/4.50      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1790,plain,
% 31.19/4.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_1441,c_764]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2969,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | k4_xboole_0(k4_xboole_0(k1_relat_1(sK2),sK1),k1_xboole_0) = k4_xboole_0(k1_relat_1(sK2),sK1) ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_2035,c_1790]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1533,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | k4_xboole_0(sK1,k1_relat_1(sK2)) = sK1 ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_1442,c_764]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2038,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,k1_relat_1(sK2))) = k1_xboole_0 ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_1442,c_771]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2385,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_1533,c_2038]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_17,plain,
% 31.19/4.50      ( r2_hidden(X0,X1)
% 31.19/4.50      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 31.19/4.50      | ~ v1_relat_1(X2) ),
% 31.19/4.50      inference(cnf_transformation,[],[f52]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_758,plain,
% 31.19/4.50      ( r2_hidden(X0,X1) = iProver_top
% 31.19/4.50      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 31.19/4.50      | v1_relat_1(X2) != iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2819,plain,
% 31.19/4.50      ( k4_xboole_0(sK1,sK1) = k1_xboole_0
% 31.19/4.50      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 31.19/4.50      | r2_hidden(X0,sK1) = iProver_top
% 31.19/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_2385,c_758]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_12,plain,
% 31.19/4.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 31.19/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2839,plain,
% 31.19/4.50      ( k4_xboole_0(sK1,sK1) = k1_xboole_0
% 31.19/4.50      | r2_hidden(X0,sK1) = iProver_top
% 31.19/4.50      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 31.19/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.19/4.50      inference(light_normalisation,[status(thm)],[c_2819,c_12]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 31.19/4.50      inference(cnf_transformation,[],[f39]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_0,plain,
% 31.19/4.50      ( r1_xboole_0(X0,X1)
% 31.19/4.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 31.19/4.50      inference(cnf_transformation,[],[f59]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1457,plain,
% 31.19/4.50      ( r1_xboole_0(k1_xboole_0,X0)
% 31.19/4.50      | ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_0,c_8]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_961,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_2,c_6]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1689,plain,
% 31.19/4.50      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_1457,c_961]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1864,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_3,c_1689]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1865,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_1864]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3452,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 31.19/4.50      inference(global_propositional_subsumption,
% 31.19/4.50                [status(thm)],
% 31.19/4.50                [c_2839,c_1865]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3457,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_768,c_3452]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_5482,plain,
% 31.19/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_3457,c_771]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_772,plain,
% 31.19/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 31.19/4.50      | r1_xboole_0(X0,X1) = iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_6205,plain,
% 31.19/4.50      ( k4_xboole_0(X0,k1_xboole_0) != k1_xboole_0
% 31.19/4.50      | r1_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_5482,c_772]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_7455,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | k4_xboole_0(k1_relat_1(sK2),sK1) != k1_xboole_0
% 31.19/4.50      | r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),sK1),k4_xboole_0(k4_xboole_0(k1_relat_1(sK2),sK1),k1_xboole_0)) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_2969,c_6205]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1542,plain,
% 31.19/4.50      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
% 31.19/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_1532]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_267,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_266,plain,( X0 = X0 ),theory(equality) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3023,plain,
% 31.19/4.50      ( X0 != X1 | X1 = X0 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_267,c_266]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_272,plain,
% 31.19/4.50      ( X0 != X1 | X2 != X3 | k7_relat_1(X0,X2) = k7_relat_1(X1,X3) ),
% 31.19/4.50      theory(equality) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3535,plain,
% 31.19/4.50      ( X0 != X1 | X2 != X3 | k7_relat_1(X1,X3) = k7_relat_1(X0,X2) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_3023,c_272]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3021,plain,
% 31.19/4.50      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | X0 != k7_relat_1(sK2,sK1)
% 31.19/4.50      | k1_xboole_0 = X0 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_267,c_19]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_107526,plain,
% 31.19/4.50      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | sK1 != X0
% 31.19/4.50      | sK2 != X1
% 31.19/4.50      | k1_xboole_0 = k7_relat_1(X1,X0) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_3535,c_3021]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_20,negated_conjecture,
% 31.19/4.50      ( v1_relat_1(sK2) ),
% 31.19/4.50      inference(cnf_transformation,[],[f55]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_18,negated_conjecture,
% 31.19/4.50      ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
% 31.19/4.50      inference(cnf_transformation,[],[f57]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_285,plain,
% 31.19/4.50      ( k1_xboole_0 = k1_xboole_0 ),
% 31.19/4.50      inference(instantiation,[status(thm)],[c_266]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_10,plain,
% 31.19/4.50      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 31.19/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_916,plain,
% 31.19/4.50      ( v1_relat_1(k7_relat_1(sK2,X0)) | ~ v1_relat_1(sK2) ),
% 31.19/4.50      inference(instantiation,[status(thm)],[c_10]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2813,plain,
% 31.19/4.50      ( v1_relat_1(k7_relat_1(sK2,sK1)) | ~ v1_relat_1(sK2) ),
% 31.19/4.50      inference(instantiation,[status(thm)],[c_916]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_14,plain,
% 31.19/4.50      ( ~ v1_relat_1(X0)
% 31.19/4.50      | k1_relat_1(X0) != k1_xboole_0
% 31.19/4.50      | k1_xboole_0 = X0 ),
% 31.19/4.50      inference(cnf_transformation,[],[f50]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1209,plain,
% 31.19/4.50      ( ~ v1_relat_1(k7_relat_1(sK2,X0))
% 31.19/4.50      | k1_relat_1(k7_relat_1(sK2,X0)) != k1_xboole_0
% 31.19/4.50      | k1_xboole_0 = k7_relat_1(sK2,X0) ),
% 31.19/4.50      inference(instantiation,[status(thm)],[c_14]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_79663,plain,
% 31.19/4.50      ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
% 31.19/4.50      | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_xboole_0
% 31.19/4.50      | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
% 31.19/4.50      inference(instantiation,[status(thm)],[c_1209]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1223,plain,
% 31.19/4.50      ( X0 != X1 | X0 = k7_relat_1(sK2,X2) | k7_relat_1(sK2,X2) != X1 ),
% 31.19/4.50      inference(instantiation,[status(thm)],[c_267]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_79668,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) != X0
% 31.19/4.50      | k1_xboole_0 != X0
% 31.19/4.50      | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
% 31.19/4.50      inference(instantiation,[status(thm)],[c_1223]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_79669,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) != k1_xboole_0
% 31.19/4.50      | k1_xboole_0 = k7_relat_1(sK2,sK1)
% 31.19/4.50      | k1_xboole_0 != k1_xboole_0 ),
% 31.19/4.50      inference(instantiation,[status(thm)],[c_79668]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_755,plain,
% 31.19/4.50      ( v1_relat_1(sK2) = iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_16,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_relat_1(X1))
% 31.19/4.50      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 31.19/4.50      | ~ v1_relat_1(X1) ),
% 31.19/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_759,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 31.19/4.50      | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
% 31.19/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2059,plain,
% 31.19/4.50      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),k1_relat_1(X0)) = iProver_top
% 31.19/4.50      | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
% 31.19/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_767,c_759]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_769,plain,
% 31.19/4.50      ( r2_hidden(X0,X1) != iProver_top
% 31.19/4.50      | r2_hidden(X0,X2) != iProver_top
% 31.19/4.50      | r1_xboole_0(X2,X1) != iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_6992,plain,
% 31.19/4.50      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),X3) != iProver_top
% 31.19/4.50      | r1_xboole_0(X3,k1_relat_1(X0)) != iProver_top
% 31.19/4.50      | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
% 31.19/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_2059,c_769]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_66640,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_relat_1(X1)) != iProver_top
% 31.19/4.50      | r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X0) = iProver_top
% 31.19/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_768,c_6992]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_99244,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_relat_1(X1)) != iProver_top
% 31.19/4.50      | r1_xboole_0(X0,k1_relat_1(k7_relat_1(X1,X2))) = iProver_top
% 31.19/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_66640,c_770]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_104015,plain,
% 31.19/4.50      ( k4_xboole_0(X0,k1_relat_1(k7_relat_1(X1,X2))) = X0
% 31.19/4.50      | r1_xboole_0(X0,k1_relat_1(X1)) != iProver_top
% 31.19/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_99244,c_764]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_104143,plain,
% 31.19/4.50      ( k4_xboole_0(k4_xboole_0(X0,k1_relat_1(X1)),k1_relat_1(k7_relat_1(X1,X2))) = k4_xboole_0(X0,k1_relat_1(X1))
% 31.19/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_766,c_104015]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_104612,plain,
% 31.19/4.50      ( k4_xboole_0(k4_xboole_0(X0,k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,X1))) = k4_xboole_0(X0,k1_relat_1(sK2)) ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_755,c_104143]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_105004,plain,
% 31.19/4.50      ( k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),k4_xboole_0(X1,k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_104612,c_1790]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1302,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | k4_xboole_0(k1_relat_1(sK2),sK1) = k1_relat_1(sK2) ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_756,c_764]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1525,plain,
% 31.19/4.50      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),X1) = iProver_top
% 31.19/4.50      | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
% 31.19/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_767,c_758]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3984,plain,
% 31.19/4.50      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(X0,X1)),X2),X3) != iProver_top
% 31.19/4.50      | r1_xboole_0(X3,X1) != iProver_top
% 31.19/4.50      | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = iProver_top
% 31.19/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_1525,c_769]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_15634,plain,
% 31.19/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.19/4.50      | r1_xboole_0(k1_relat_1(k7_relat_1(X2,X1)),X0) = iProver_top
% 31.19/4.50      | v1_relat_1(X2) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_768,c_3984]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_26152,plain,
% 31.19/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.19/4.50      | r1_xboole_0(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
% 31.19/4.50      | v1_relat_1(X2) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_15634,c_770]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_30301,plain,
% 31.19/4.50      ( k4_xboole_0(X0,k1_relat_1(k7_relat_1(X1,X2))) = X0
% 31.19/4.50      | r1_xboole_0(X0,X2) != iProver_top
% 31.19/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_26152,c_764]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_30348,plain,
% 31.19/4.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k1_relat_1(k7_relat_1(X2,X1))) = k4_xboole_0(X0,X1)
% 31.19/4.50      | v1_relat_1(X2) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_766,c_30301]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_30815,plain,
% 31.19/4.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k1_relat_1(k7_relat_1(sK2,X1))) = k4_xboole_0(X0,X1) ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_755,c_30348]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_30929,plain,
% 31.19/4.50      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),k4_xboole_0(X1,X0)) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_30815,c_1441]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_31833,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_1302,c_30929]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_58216,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | k4_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2))) = k1_xboole_0 ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_31833,c_771]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_105786,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 31.19/4.50      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_105004,c_58216]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_107904,plain,
% 31.19/4.50      ( sK1 != X0 | sK2 != X1 | k1_xboole_0 = k7_relat_1(X1,X0) ),
% 31.19/4.50      inference(global_propositional_subsumption,
% 31.19/4.50                [status(thm)],
% 31.19/4.50                [c_107526,c_20,c_18,c_285,c_2813,c_79663,c_79669,
% 31.19/4.50                 c_105786]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_108546,plain,
% 31.19/4.50      ( ~ r1_xboole_0(k1_relat_1(sK2),sK1) | sK1 != sK1 | sK2 != sK2 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_107904,c_18]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_108547,plain,
% 31.19/4.50      ( ~ r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 31.19/4.50      inference(equality_resolution_simp,[status(thm)],[c_108546]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_118876,plain,
% 31.19/4.50      ( k7_relat_1(sK2,sK1) = k1_xboole_0 ),
% 31.19/4.50      inference(global_propositional_subsumption,
% 31.19/4.50                [status(thm)],
% 31.19/4.50                [c_7455,c_20,c_18,c_285,c_2813,c_6269,c_79663,c_79669,
% 31.19/4.50                 c_105786]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_15,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,X1)
% 31.19/4.50      | ~ r2_hidden(X0,k1_relat_1(X2))
% 31.19/4.50      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 31.19/4.50      | ~ v1_relat_1(X2) ),
% 31.19/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_760,plain,
% 31.19/4.50      ( r2_hidden(X0,X1) != iProver_top
% 31.19/4.50      | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
% 31.19/4.50      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) = iProver_top
% 31.19/4.50      | v1_relat_1(X2) != iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_118897,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 31.19/4.50      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top
% 31.19/4.50      | r2_hidden(X0,sK1) != iProver_top
% 31.19/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_118876,c_760]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_119317,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 31.19/4.50      | r2_hidden(X0,sK1) != iProver_top
% 31.19/4.50      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 31.19/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.19/4.50      inference(light_normalisation,[status(thm)],[c_118897,c_12]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_23,plain,
% 31.19/4.50      ( k1_xboole_0 != k7_relat_1(sK2,sK1)
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_270,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.19/4.50      theory(equality) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_275,plain,
% 31.19/4.50      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 31.19/4.50      theory(equality) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3377,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 31.19/4.50      | r2_hidden(X2,k1_relat_1(X3))
% 31.19/4.50      | X2 != X0
% 31.19/4.50      | X3 != X1 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_270,c_275]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_12597,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
% 31.19/4.50      | r2_hidden(X1,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | X1 != X0 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_3377,c_19]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_13015,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,k1_relat_1(sK2))
% 31.19/4.50      | r2_hidden(X1,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | ~ r2_hidden(X0,sK1)
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | ~ v1_relat_1(sK2)
% 31.19/4.50      | X1 != X0 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_12597,c_15]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_18053,plain,
% 31.19/4.50      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | ~ r2_hidden(X0,sK1)
% 31.19/4.50      | r2_hidden(X1,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | ~ r2_hidden(X0,k1_relat_1(sK2))
% 31.19/4.50      | X1 != X0 ),
% 31.19/4.50      inference(global_propositional_subsumption,
% 31.19/4.50                [status(thm)],
% 31.19/4.50                [c_13015,c_20]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_18054,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,k1_relat_1(sK2))
% 31.19/4.50      | r2_hidden(X1,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | ~ r2_hidden(X0,sK1)
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | X1 != X0 ),
% 31.19/4.50      inference(renaming,[status(thm)],[c_18053]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_18539,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,k1_relat_1(sK2))
% 31.19/4.50      | r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | ~ r2_hidden(X0,sK1)
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_18054,c_266]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_18540,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 31.19/4.50      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top
% 31.19/4.50      | r2_hidden(X0,sK1) != iProver_top
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_18539]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3530,plain,
% 31.19/4.50      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_3023,c_19]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_12613,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
% 31.19/4.50      | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | X0 != X1 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_3377,c_3530]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_15307,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
% 31.19/4.50      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_12613,c_266]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_268,plain,
% 31.19/4.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.19/4.50      theory(equality) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3339,plain,
% 31.19/4.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 31.19/4.50      | r1_xboole_0(X2,k1_relat_1(X3))
% 31.19/4.50      | X2 != X0
% 31.19/4.50      | X3 != X1 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_268,c_275]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_10872,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
% 31.19/4.50      | ~ r1_xboole_0(X1,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | X0 != X1 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_3339,c_3530]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_13828,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
% 31.19/4.50      | ~ r1_xboole_0(X0,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_10872,c_266]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_3325,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | ~ r1_xboole_0(X1,k1_xboole_0)
% 31.19/4.50      | X0 != X1 ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_268,c_12]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_2078,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_1864,c_4]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_5571,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) | X0 != X1 ),
% 31.19/4.50      inference(forward_subsumption_resolution,
% 31.19/4.50                [status(thm)],
% 31.19/4.50                [c_3325,c_2078]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_20306,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_5571,c_266]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_25447,plain,
% 31.19/4.50      ( r1_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 31.19/4.50      inference(global_propositional_subsumption,
% 31.19/4.50                [status(thm)],
% 31.19/4.50                [c_13828,c_20306]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_25469,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,X1)
% 31.19/4.50      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK1)))
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 31.19/4.50      inference(resolution,[status(thm)],[c_25447,c_3]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_27573,plain,
% 31.19/4.50      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 31.19/4.50      inference(forward_subsumption_resolution,
% 31.19/4.50                [status(thm)],
% 31.19/4.50                [c_15307,c_25469]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_27574,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 31.19/4.50      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_27573]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_119502,plain,
% 31.19/4.50      ( r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 31.19/4.50      | r2_hidden(X0,sK1) != iProver_top ),
% 31.19/4.50      inference(global_propositional_subsumption,
% 31.19/4.50                [status(thm)],
% 31.19/4.50                [c_119317,c_20,c_23,c_285,c_2813,c_18540,c_27574,c_79663,
% 31.19/4.50                 c_79669,c_105786]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_119508,plain,
% 31.19/4.50      ( r2_hidden(sK0(X0,k1_relat_1(sK2)),sK1) != iProver_top
% 31.19/4.50      | r1_xboole_0(X0,k1_relat_1(sK2)) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_768,c_119502]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_120434,plain,
% 31.19/4.50      ( r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
% 31.19/4.50      inference(superposition,[status(thm)],[c_767,c_119508]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1389,plain,
% 31.19/4.50      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 31.19/4.50      | ~ r1_xboole_0(sK1,k1_relat_1(sK2)) ),
% 31.19/4.50      inference(instantiation,[status(thm)],[c_2]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(c_1390,plain,
% 31.19/4.50      ( r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top
% 31.19/4.50      | r1_xboole_0(sK1,k1_relat_1(sK2)) != iProver_top ),
% 31.19/4.50      inference(predicate_to_equality,[status(thm)],[c_1389]) ).
% 31.19/4.50  
% 31.19/4.50  cnf(contradiction,plain,
% 31.19/4.50      ( $false ),
% 31.19/4.50      inference(minisat,
% 31.19/4.50                [status(thm)],
% 31.19/4.50                [c_120434,c_108547,c_1390,c_23,c_19]) ).
% 31.19/4.50  
% 31.19/4.50  
% 31.19/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.19/4.50  
% 31.19/4.50  ------                               Statistics
% 31.19/4.50  
% 31.19/4.50  ------ Selected
% 31.19/4.50  
% 31.19/4.50  total_time:                             3.623
% 31.19/4.50  
%------------------------------------------------------------------------------
