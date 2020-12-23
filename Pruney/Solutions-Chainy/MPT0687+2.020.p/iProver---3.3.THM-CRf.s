%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:33 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 982 expanded)
%              Number of clauses        :   70 ( 324 expanded)
%              Number of leaves         :   13 ( 193 expanded)
%              Depth                    :   19
%              Number of atoms          :  281 (2978 expanded)
%              Number of equality atoms :  157 (1364 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    9 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f52,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f53,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f54,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
        | ~ r2_hidden(sK1,k2_relat_1(sK2)) )
      & ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1))
        | r2_hidden(sK1,k2_relat_1(sK2)) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
      | ~ r2_hidden(sK1,k2_relat_1(sK2)) )
    & ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1))
      | r2_hidden(sK1,k2_relat_1(sK2)) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f53,f54])).

fof(f87,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f62])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1))
    | r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X1] : k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(equality_resolution,[],[f66])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1038,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1031,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3394,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1031])).

cnf(c_3549,plain,
    ( sK0(X0,k1_tarski(X1)) = X1
    | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1038,c_3394])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1040,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11618,plain,
    ( sK0(X0,k1_tarski(X1)) = X1
    | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3549,c_1040])).

cnf(c_32,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1014,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1023,plain,
    ( k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4552,plain,
    ( k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),X0)) = k2_relat_1(k8_relat_1(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1014,c_1023])).

cnf(c_13920,plain,
    ( sK0(k2_relat_1(sK2),k1_tarski(X0)) = X0
    | k2_relat_1(k8_relat_1(k4_xboole_0(k2_relat_1(sK2),k1_tarski(X0)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11618,c_4552])).

cnf(c_4932,plain,
    ( k2_relat_1(k8_relat_1(k4_xboole_0(k2_relat_1(sK2),X0),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_4552,c_4552])).

cnf(c_5307,plain,
    ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k4_xboole_0(k2_relat_1(sK2),X0),sK2))) = k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,sK2)),sK2)) ),
    inference(superposition,[status(thm)],[c_4932,c_4552])).

cnf(c_14302,plain,
    ( sK0(k2_relat_1(sK2),k1_tarski(X0)) = X0
    | k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k1_tarski(X0),sK2)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_13920,c_5307])).

cnf(c_28,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1022,plain,
    ( k8_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1607,plain,
    ( k8_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1014,c_1022])).

cnf(c_14310,plain,
    ( sK0(k2_relat_1(sK2),k1_tarski(X0)) = X0
    | k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k1_tarski(X0),sK2)),sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14302,c_28,c_1607,c_4552])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1032,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1016,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
    | r2_hidden(sK1,k2_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2064,plain,
    ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
    | k4_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1032,c_1016])).

cnf(c_4929,plain,
    ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
    | k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2064,c_4552])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_10,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_83,plain,
    ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) != k1_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_84,plain,
    ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_tarski(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_356,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1381,plain,
    ( k10_relat_1(sK2,k1_tarski(sK1)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_1382,plain,
    ( k10_relat_1(sK2,k1_tarski(sK1)) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_1317,plain,
    ( r2_hidden(X0,k1_tarski(X0))
    | k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2533,plain,
    ( r2_hidden(sK1,k1_tarski(sK1))
    | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) = k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_26,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1330,plain,
    ( r1_xboole_0(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4190,plain,
    ( r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k1_tarski(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2019,plain,
    ( ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ r1_xboole_0(k2_relat_1(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4201,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_4520,plain,
    ( k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_6488,plain,
    ( k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4929,c_32,c_31,c_83,c_84,c_1382,c_2533,c_4190,c_4201,c_4520])).

cnf(c_6493,plain,
    ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2))) = k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_6488,c_4552])).

cnf(c_6878,plain,
    ( k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2))) ),
    inference(superposition,[status(thm)],[c_6493,c_4552])).

cnf(c_6892,plain,
    ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)),sK2)),sK2))) = k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)),sK2)),sK2)) ),
    inference(superposition,[status(thm)],[c_6878,c_5307])).

cnf(c_14653,plain,
    ( sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1
    | k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)),sK2)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k1_xboole_0,sK2))) ),
    inference(superposition,[status(thm)],[c_14310,c_6892])).

cnf(c_14661,plain,
    ( sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1
    | k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)),sK2)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_14653,c_28,c_1607])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1041,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4737,plain,
    ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
    | k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2064,c_1041])).

cnf(c_33,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_25,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2171,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2172,plain,
    ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(c_7129,plain,
    ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4737,c_32,c_33,c_31,c_83,c_84,c_1382,c_2172,c_2533,c_4190,c_4201,c_4520])).

cnf(c_7133,plain,
    ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7129,c_32,c_33,c_31,c_83,c_84,c_1382,c_2172,c_2533,c_4190,c_4201,c_4520,c_4737])).

cnf(c_7135,plain,
    ( k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7133,c_6488])).

cnf(c_13911,plain,
    ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
    | sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1
    | k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2064,c_11618])).

cnf(c_13966,plain,
    ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
    | sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1
    | k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13911,c_6488])).

cnf(c_15310,plain,
    ( sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14661,c_32,c_31,c_83,c_84,c_1382,c_2533,c_4190,c_4201,c_4520,c_7135,c_13966])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1037,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15314,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2)) = iProver_top
    | r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15310,c_1037])).

cnf(c_3395,plain,
    ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
    | r2_hidden(sK1,k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2064,c_1031])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15314,c_4520,c_4201,c_4190,c_3395,c_2533,c_2172,c_1382,c_84,c_83,c_31,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.89/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/1.00  
% 3.89/1.00  ------  iProver source info
% 3.89/1.00  
% 3.89/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.89/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/1.00  git: non_committed_changes: false
% 3.89/1.00  git: last_make_outside_of_git: false
% 3.89/1.00  
% 3.89/1.00  ------ 
% 3.89/1.00  ------ Parsing...
% 3.89/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/1.00  
% 3.89/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.89/1.00  
% 3.89/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/1.00  
% 3.89/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.00  ------ Proving...
% 3.89/1.00  ------ Problem Properties 
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  clauses                                 33
% 3.89/1.00  conjectures                             3
% 3.89/1.00  EPR                                     2
% 3.89/1.00  Horn                                    28
% 3.89/1.00  unary                                   5
% 3.89/1.00  binary                                  21
% 3.89/1.00  lits                                    70
% 3.89/1.00  lits eq                                 25
% 3.89/1.00  fd_pure                                 0
% 3.89/1.00  fd_pseudo                               0
% 3.89/1.00  fd_cond                                 1
% 3.89/1.00  fd_pseudo_cond                          1
% 3.89/1.00  AC symbols                              0
% 3.89/1.00  
% 3.89/1.00  ------ Input Options Time Limit: Unbounded
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  ------ 
% 3.89/1.00  Current options:
% 3.89/1.00  ------ 
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  ------ Proving...
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  % SZS status Theorem for theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  fof(f2,axiom,(
% 3.89/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f25,plain,(
% 3.89/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.89/1.00    inference(rectify,[],[f2])).
% 3.89/1.00  
% 3.89/1.00  fof(f26,plain,(
% 3.89/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.89/1.00    inference(ennf_transformation,[],[f25])).
% 3.89/1.00  
% 3.89/1.00  fof(f45,plain,(
% 3.89/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.89/1.00    introduced(choice_axiom,[])).
% 3.89/1.00  
% 3.89/1.00  fof(f46,plain,(
% 3.89/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.89/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f45])).
% 3.89/1.00  
% 3.89/1.00  fof(f59,plain,(
% 3.89/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f46])).
% 3.89/1.00  
% 3.89/1.00  fof(f8,axiom,(
% 3.89/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f47,plain,(
% 3.89/1.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.89/1.00    inference(nnf_transformation,[],[f8])).
% 3.89/1.00  
% 3.89/1.00  fof(f67,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.89/1.00    inference(cnf_transformation,[],[f47])).
% 3.89/1.00  
% 3.89/1.00  fof(f9,axiom,(
% 3.89/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f48,plain,(
% 3.89/1.00    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.89/1.00    inference(nnf_transformation,[],[f9])).
% 3.89/1.00  
% 3.89/1.00  fof(f68,plain,(
% 3.89/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.89/1.00    inference(cnf_transformation,[],[f48])).
% 3.89/1.00  
% 3.89/1.00  fof(f1,axiom,(
% 3.89/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f44,plain,(
% 3.89/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.89/1.00    inference(nnf_transformation,[],[f1])).
% 3.89/1.00  
% 3.89/1.00  fof(f56,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f44])).
% 3.89/1.00  
% 3.89/1.00  fof(f4,axiom,(
% 3.89/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f62,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.89/1.00    inference(cnf_transformation,[],[f4])).
% 3.89/1.00  
% 3.89/1.00  fof(f91,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.89/1.00    inference(definition_unfolding,[],[f56,f62])).
% 3.89/1.00  
% 3.89/1.00  fof(f23,conjecture,(
% 3.89/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f24,negated_conjecture,(
% 3.89/1.00    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 3.89/1.00    inference(negated_conjecture,[],[f23])).
% 3.89/1.00  
% 3.89/1.00  fof(f43,plain,(
% 3.89/1.00    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 3.89/1.00    inference(ennf_transformation,[],[f24])).
% 3.89/1.00  
% 3.89/1.00  fof(f52,plain,(
% 3.89/1.00    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 3.89/1.00    inference(nnf_transformation,[],[f43])).
% 3.89/1.00  
% 3.89/1.00  fof(f53,plain,(
% 3.89/1.00    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 3.89/1.00    inference(flattening,[],[f52])).
% 3.89/1.00  
% 3.89/1.00  fof(f54,plain,(
% 3.89/1.00    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))) & (k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) | r2_hidden(sK1,k2_relat_1(sK2))) & v1_relat_1(sK2))),
% 3.89/1.00    introduced(choice_axiom,[])).
% 3.89/1.00  
% 3.89/1.00  fof(f55,plain,(
% 3.89/1.00    (k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))) & (k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) | r2_hidden(sK1,k2_relat_1(sK2))) & v1_relat_1(sK2)),
% 3.89/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f53,f54])).
% 3.89/1.00  
% 3.89/1.00  fof(f87,plain,(
% 3.89/1.00    v1_relat_1(sK2)),
% 3.89/1.00    inference(cnf_transformation,[],[f55])).
% 3.89/1.00  
% 3.89/1.00  fof(f15,axiom,(
% 3.89/1.00    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)))),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f36,plain,(
% 3.89/1.00    ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 3.89/1.00    inference(ennf_transformation,[],[f15])).
% 3.89/1.00  
% 3.89/1.00  fof(f77,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f36])).
% 3.89/1.00  
% 3.89/1.00  fof(f93,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.89/1.00    inference(definition_unfolding,[],[f77,f62])).
% 3.89/1.00  
% 3.89/1.00  fof(f22,axiom,(
% 3.89/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f86,plain,(
% 3.89/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.89/1.00    inference(cnf_transformation,[],[f22])).
% 3.89/1.00  
% 3.89/1.00  fof(f16,axiom,(
% 3.89/1.00    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f37,plain,(
% 3.89/1.00    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 3.89/1.00    inference(ennf_transformation,[],[f16])).
% 3.89/1.00  
% 3.89/1.00  fof(f78,plain,(
% 3.89/1.00    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f37])).
% 3.89/1.00  
% 3.89/1.00  fof(f69,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f48])).
% 3.89/1.00  
% 3.89/1.00  fof(f89,plain,(
% 3.89/1.00    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_relat_1(sK2))),
% 3.89/1.00    inference(cnf_transformation,[],[f55])).
% 3.89/1.00  
% 3.89/1.00  fof(f88,plain,(
% 3.89/1.00    k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) | r2_hidden(sK1,k2_relat_1(sK2))),
% 3.89/1.00    inference(cnf_transformation,[],[f55])).
% 3.89/1.00  
% 3.89/1.00  fof(f66,plain,(
% 3.89/1.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f47])).
% 3.89/1.00  
% 3.89/1.00  fof(f95,plain,(
% 3.89/1.00    ( ! [X1] : (k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1)) )),
% 3.89/1.00    inference(equality_resolution,[],[f66])).
% 3.89/1.00  
% 3.89/1.00  fof(f20,axiom,(
% 3.89/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.89/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.00  
% 3.89/1.00  fof(f40,plain,(
% 3.89/1.00    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.89/1.00    inference(ennf_transformation,[],[f20])).
% 3.89/1.00  
% 3.89/1.00  fof(f51,plain,(
% 3.89/1.00    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.89/1.00    inference(nnf_transformation,[],[f40])).
% 3.89/1.00  
% 3.89/1.00  fof(f82,plain,(
% 3.89/1.00    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f51])).
% 3.89/1.00  
% 3.89/1.00  fof(f60,plain,(
% 3.89/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f46])).
% 3.89/1.00  
% 3.89/1.00  fof(f57,plain,(
% 3.89/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.89/1.00    inference(cnf_transformation,[],[f44])).
% 3.89/1.00  
% 3.89/1.00  fof(f90,plain,(
% 3.89/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.89/1.00    inference(definition_unfolding,[],[f57,f62])).
% 3.89/1.00  
% 3.89/1.00  fof(f83,plain,(
% 3.89/1.00    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f51])).
% 3.89/1.00  
% 3.89/1.00  fof(f58,plain,(
% 3.89/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.89/1.00    inference(cnf_transformation,[],[f46])).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3,plain,
% 3.89/1.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.89/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1038,plain,
% 3.89/1.00      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.89/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_9,plain,
% 3.89/1.00      ( X0 = X1
% 3.89/1.00      | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
% 3.89/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_12,plain,
% 3.89/1.00      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
% 3.89/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1031,plain,
% 3.89/1.00      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
% 3.89/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3394,plain,
% 3.89/1.00      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_9,c_1031]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3549,plain,
% 3.89/1.00      ( sK0(X0,k1_tarski(X1)) = X1
% 3.89/1.00      | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_1038,c_3394]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1,plain,
% 3.89/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.89/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1040,plain,
% 3.89/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.89/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_11618,plain,
% 3.89/1.00      ( sK0(X0,k1_tarski(X1)) = X1
% 3.89/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) = k1_xboole_0 ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_3549,c_1040]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_32,negated_conjecture,
% 3.89/1.00      ( v1_relat_1(sK2) ),
% 3.89/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1014,plain,
% 3.89/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_20,plain,
% 3.89/1.00      ( ~ v1_relat_1(X0)
% 3.89/1.00      | k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 3.89/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1023,plain,
% 3.89/1.00      ( k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
% 3.89/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4552,plain,
% 3.89/1.00      ( k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),X0)) = k2_relat_1(k8_relat_1(X0,sK2)) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_1014,c_1023]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_13920,plain,
% 3.89/1.00      ( sK0(k2_relat_1(sK2),k1_tarski(X0)) = X0
% 3.89/1.00      | k2_relat_1(k8_relat_1(k4_xboole_0(k2_relat_1(sK2),k1_tarski(X0)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k1_xboole_0) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_11618,c_4552]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4932,plain,
% 3.89/1.00      ( k2_relat_1(k8_relat_1(k4_xboole_0(k2_relat_1(sK2),X0),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(X0,sK2))) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_4552,c_4552]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_5307,plain,
% 3.89/1.00      ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k4_xboole_0(k2_relat_1(sK2),X0),sK2))) = k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,sK2)),sK2)) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_4932,c_4552]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_14302,plain,
% 3.89/1.00      ( sK0(k2_relat_1(sK2),k1_tarski(X0)) = X0
% 3.89/1.00      | k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k1_tarski(X0),sK2)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_xboole_0)) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_13920,c_5307]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_28,plain,
% 3.89/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_21,plain,
% 3.89/1.00      ( ~ v1_relat_1(X0) | k8_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1022,plain,
% 3.89/1.00      ( k8_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.89/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1607,plain,
% 3.89/1.00      ( k8_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_1014,c_1022]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_14310,plain,
% 3.89/1.00      ( sK0(k2_relat_1(sK2),k1_tarski(X0)) = X0
% 3.89/1.00      | k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k1_tarski(X0),sK2)),sK2)) = k1_xboole_0 ),
% 3.89/1.00      inference(demodulation,[status(thm)],[c_14302,c_28,c_1607,c_4552]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_11,plain,
% 3.89/1.00      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
% 3.89/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1032,plain,
% 3.89/1.00      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
% 3.89/1.00      | r2_hidden(X1,X0) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_30,negated_conjecture,
% 3.89/1.00      ( ~ r2_hidden(sK1,k2_relat_1(sK2))
% 3.89/1.00      | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) ),
% 3.89/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1016,plain,
% 3.89/1.00      ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
% 3.89/1.00      | r2_hidden(sK1,k2_relat_1(sK2)) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2064,plain,
% 3.89/1.00      ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
% 3.89/1.00      | k4_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) = k2_relat_1(sK2) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_1032,c_1016]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4929,plain,
% 3.89/1.00      ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
% 3.89/1.00      | k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_2064,c_4552]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_31,negated_conjecture,
% 3.89/1.00      ( r2_hidden(sK1,k2_relat_1(sK2))
% 3.89/1.00      | k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK1)) ),
% 3.89/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_10,plain,
% 3.89/1.00      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
% 3.89/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_83,plain,
% 3.89/1.00      ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) != k1_tarski(k1_xboole_0) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_84,plain,
% 3.89/1.00      ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_tarski(k1_xboole_0)
% 3.89/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_356,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1381,plain,
% 3.89/1.00      ( k10_relat_1(sK2,k1_tarski(sK1)) != X0
% 3.89/1.00      | k1_xboole_0 != X0
% 3.89/1.00      | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1)) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_356]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1382,plain,
% 3.89/1.00      ( k10_relat_1(sK2,k1_tarski(sK1)) != k1_xboole_0
% 3.89/1.00      | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK1))
% 3.89/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_1381]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1317,plain,
% 3.89/1.00      ( r2_hidden(X0,k1_tarski(X0))
% 3.89/1.00      | k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_tarski(X0) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2533,plain,
% 3.89/1.00      ( r2_hidden(sK1,k1_tarski(sK1))
% 3.89/1.00      | k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) = k1_tarski(sK1) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_1317]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_26,plain,
% 3.89/1.00      ( r1_xboole_0(k2_relat_1(X0),X1)
% 3.89/1.00      | ~ v1_relat_1(X0)
% 3.89/1.00      | k10_relat_1(X0,X1) != k1_xboole_0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1330,plain,
% 3.89/1.00      ( r1_xboole_0(k2_relat_1(sK2),X0)
% 3.89/1.00      | ~ v1_relat_1(sK2)
% 3.89/1.00      | k10_relat_1(sK2,X0) != k1_xboole_0 ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4190,plain,
% 3.89/1.00      ( r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1))
% 3.89/1.00      | ~ v1_relat_1(sK2)
% 3.89/1.00      | k10_relat_1(sK2,k1_tarski(sK1)) != k1_xboole_0 ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_1330]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2,plain,
% 3.89/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.89/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2019,plain,
% 3.89/1.00      ( ~ r2_hidden(sK1,X0)
% 3.89/1.00      | ~ r2_hidden(sK1,k2_relat_1(sK2))
% 3.89/1.00      | ~ r1_xboole_0(k2_relat_1(sK2),X0) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4201,plain,
% 3.89/1.00      ( ~ r2_hidden(sK1,k2_relat_1(sK2))
% 3.89/1.00      | ~ r2_hidden(sK1,k1_tarski(sK1))
% 3.89/1.00      | ~ r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_2019]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4520,plain,
% 3.89/1.00      ( k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) != k1_tarski(sK1) ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_6488,plain,
% 3.89/1.00      ( k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_4929,c_32,c_31,c_83,c_84,c_1382,c_2533,c_4190,c_4201,
% 3.89/1.00                 c_4520]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_6493,plain,
% 3.89/1.00      ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2))) = k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_6488,c_4552]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_6878,plain,
% 3.89/1.00      ( k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2))) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_6493,c_4552]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_6892,plain,
% 3.89/1.00      ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)),sK2)),sK2))) = k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)),sK2)),sK2)) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_6878,c_5307]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_14653,plain,
% 3.89/1.00      ( sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1
% 3.89/1.00      | k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)),sK2)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(k8_relat_1(k1_xboole_0,sK2))) ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_14310,c_6892]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_14661,plain,
% 3.89/1.00      ( sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1
% 3.89/1.00      | k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(k2_relat_1(sK2),sK2)),sK2)),sK2)) = k4_xboole_0(k2_relat_1(sK2),k1_xboole_0) ),
% 3.89/1.00      inference(light_normalisation,[status(thm)],[c_14653,c_28,c_1607]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_0,plain,
% 3.89/1.00      ( r1_xboole_0(X0,X1)
% 3.89/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1041,plain,
% 3.89/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.89/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4737,plain,
% 3.89/1.00      ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
% 3.89/1.00      | k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) != k1_xboole_0
% 3.89/1.00      | r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) = iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_2064,c_1041]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_33,plain,
% 3.89/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_25,plain,
% 3.89/1.00      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 3.89/1.00      | ~ v1_relat_1(X0)
% 3.89/1.00      | k10_relat_1(X0,X1) = k1_xboole_0 ),
% 3.89/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2171,plain,
% 3.89/1.00      ( ~ r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1))
% 3.89/1.00      | ~ v1_relat_1(sK2)
% 3.89/1.00      | k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0 ),
% 3.89/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_2172,plain,
% 3.89/1.00      ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
% 3.89/1.00      | r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) != iProver_top
% 3.89/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_7129,plain,
% 3.89/1.00      ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) != k1_xboole_0
% 3.89/1.00      | r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) = iProver_top ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_4737,c_32,c_33,c_31,c_83,c_84,c_1382,c_2172,c_2533,
% 3.89/1.00                 c_4190,c_4201,c_4520]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_7133,plain,
% 3.89/1.00      ( k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) != k1_xboole_0 ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_7129,c_32,c_33,c_31,c_83,c_84,c_1382,c_2172,c_2533,
% 3.89/1.00                 c_4190,c_4201,c_4520,c_4737]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_7135,plain,
% 3.89/1.00      ( k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)) != k1_xboole_0 ),
% 3.89/1.00      inference(light_normalisation,[status(thm)],[c_7133,c_6488]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_13911,plain,
% 3.89/1.00      ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
% 3.89/1.00      | sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1
% 3.89/1.00      | k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) = k1_xboole_0 ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_2064,c_11618]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_13966,plain,
% 3.89/1.00      ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
% 3.89/1.00      | sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1
% 3.89/1.00      | k2_relat_1(k8_relat_1(k1_tarski(sK1),sK2)) = k1_xboole_0 ),
% 3.89/1.00      inference(demodulation,[status(thm)],[c_13911,c_6488]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_15310,plain,
% 3.89/1.00      ( sK0(k2_relat_1(sK2),k1_tarski(sK1)) = sK1 ),
% 3.89/1.00      inference(global_propositional_subsumption,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_14661,c_32,c_31,c_83,c_84,c_1382,c_2533,c_4190,c_4201,
% 3.89/1.00                 c_4520,c_7135,c_13966]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_4,plain,
% 3.89/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.89/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_1037,plain,
% 3.89/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.89/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.89/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_15314,plain,
% 3.89/1.00      ( r2_hidden(sK1,k2_relat_1(sK2)) = iProver_top
% 3.89/1.00      | r1_xboole_0(k2_relat_1(sK2),k1_tarski(sK1)) = iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_15310,c_1037]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(c_3395,plain,
% 3.89/1.00      ( k10_relat_1(sK2,k1_tarski(sK1)) = k1_xboole_0
% 3.89/1.00      | r2_hidden(sK1,k2_relat_1(sK2)) != iProver_top ),
% 3.89/1.00      inference(superposition,[status(thm)],[c_2064,c_1031]) ).
% 3.89/1.00  
% 3.89/1.00  cnf(contradiction,plain,
% 3.89/1.00      ( $false ),
% 3.89/1.00      inference(minisat,
% 3.89/1.00                [status(thm)],
% 3.89/1.00                [c_15314,c_4520,c_4201,c_4190,c_3395,c_2533,c_2172,
% 3.89/1.00                 c_1382,c_84,c_83,c_31,c_33,c_32]) ).
% 3.89/1.00  
% 3.89/1.00  
% 3.89/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/1.00  
% 3.89/1.00  ------                               Statistics
% 3.89/1.00  
% 3.89/1.00  ------ Selected
% 3.89/1.00  
% 3.89/1.00  total_time:                             0.443
% 3.89/1.00  
%------------------------------------------------------------------------------
