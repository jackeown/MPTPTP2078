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
% DateTime   : Thu Dec  3 11:51:33 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 341 expanded)
%              Number of clauses        :   39 (  76 expanded)
%              Number of leaves         :   13 (  80 expanded)
%              Depth                    :   17
%              Number of atoms          :  288 (1076 expanded)
%              Number of equality atoms :  108 ( 390 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f48,f55,f55])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0
        | ~ r2_hidden(sK2,k2_relat_1(sK3)) )
      & ( k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0
        | r2_hidden(sK2,k2_relat_1(sK3)) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0
      | ~ r2_hidden(sK2,k2_relat_1(sK3)) )
    & ( k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0
      | r2_hidden(sK2,k2_relat_1(sK3)) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f29])).

fof(f53,plain,
    ( k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0
    | ~ r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f60,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
    | ~ r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(definition_unfolding,[],[f53,f56])).

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
    inference(rectify,[],[f2])).

fof(f13,plain,(
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

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) != k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) != k3_enumset1(X0,X0,X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f55,f55])).

fof(f52,plain,
    ( k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(definition_unfolding,[],[f52,f56])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) = k3_enumset1(X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1202,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK2,k2_relat_1(sK3))
    | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1199,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1929,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
    | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k2_relat_1(sK3)) = k3_enumset1(X0,X0,X0,X0,sK2)
    | r2_hidden(X0,k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1199])).

cnf(c_2334,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
    | k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k2_relat_1(sK3)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1929,c_1199])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1205,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1206,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1209,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1550,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_1209])).

cnf(c_1723,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1550])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_272,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | k10_relat_1(X0,X1) = k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_273,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
    | k10_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_509,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
    | k10_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_273])).

cnf(c_1196,plain,
    ( k10_relat_1(sK3,X0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_1745,plain,
    ( k10_relat_1(sK3,k4_xboole_0(X0,k2_relat_1(sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1723,c_1196])).

cnf(c_2392,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2334,c_1745])).

cnf(c_15,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_260,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | k10_relat_1(X0,X1) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_261,plain,
    ( r1_xboole_0(k2_relat_1(sK3),X0)
    | k10_relat_1(sK3,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_507,plain,
    ( r1_xboole_0(k2_relat_1(sK3),X0)
    | k10_relat_1(sK3,X0) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_261])).

cnf(c_1197,plain,
    ( k10_relat_1(sK3,X0) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_2462,plain,
    ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2392,c_1197])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1203,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2562,plain,
    ( k4_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2462,c_1203])).

cnf(c_1744,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1723,c_1203])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) != k3_enumset1(X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1200,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) != k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1819,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1200])).

cnf(c_2644,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2562,c_1819])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
    | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2644,c_2392,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.99/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.03  
% 1.99/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/1.03  
% 1.99/1.03  ------  iProver source info
% 1.99/1.03  
% 1.99/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.99/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/1.03  git: non_committed_changes: false
% 1.99/1.03  git: last_make_outside_of_git: false
% 1.99/1.03  
% 1.99/1.03  ------ 
% 1.99/1.03  
% 1.99/1.03  ------ Input Options
% 1.99/1.03  
% 1.99/1.03  --out_options                           all
% 1.99/1.03  --tptp_safe_out                         true
% 1.99/1.03  --problem_path                          ""
% 1.99/1.03  --include_path                          ""
% 1.99/1.03  --clausifier                            res/vclausify_rel
% 1.99/1.03  --clausifier_options                    --mode clausify
% 1.99/1.03  --stdin                                 false
% 1.99/1.03  --stats_out                             all
% 1.99/1.03  
% 1.99/1.03  ------ General Options
% 1.99/1.03  
% 1.99/1.03  --fof                                   false
% 1.99/1.03  --time_out_real                         305.
% 1.99/1.03  --time_out_virtual                      -1.
% 1.99/1.03  --symbol_type_check                     false
% 1.99/1.03  --clausify_out                          false
% 1.99/1.03  --sig_cnt_out                           false
% 1.99/1.03  --trig_cnt_out                          false
% 1.99/1.03  --trig_cnt_out_tolerance                1.
% 1.99/1.03  --trig_cnt_out_sk_spl                   false
% 1.99/1.03  --abstr_cl_out                          false
% 1.99/1.03  
% 1.99/1.03  ------ Global Options
% 1.99/1.03  
% 1.99/1.03  --schedule                              default
% 1.99/1.03  --add_important_lit                     false
% 1.99/1.03  --prop_solver_per_cl                    1000
% 1.99/1.03  --min_unsat_core                        false
% 1.99/1.03  --soft_assumptions                      false
% 1.99/1.03  --soft_lemma_size                       3
% 1.99/1.03  --prop_impl_unit_size                   0
% 1.99/1.03  --prop_impl_unit                        []
% 1.99/1.03  --share_sel_clauses                     true
% 1.99/1.03  --reset_solvers                         false
% 1.99/1.03  --bc_imp_inh                            [conj_cone]
% 1.99/1.03  --conj_cone_tolerance                   3.
% 1.99/1.03  --extra_neg_conj                        none
% 1.99/1.03  --large_theory_mode                     true
% 1.99/1.03  --prolific_symb_bound                   200
% 1.99/1.03  --lt_threshold                          2000
% 1.99/1.03  --clause_weak_htbl                      true
% 1.99/1.03  --gc_record_bc_elim                     false
% 1.99/1.03  
% 1.99/1.03  ------ Preprocessing Options
% 1.99/1.03  
% 1.99/1.03  --preprocessing_flag                    true
% 1.99/1.03  --time_out_prep_mult                    0.1
% 1.99/1.03  --splitting_mode                        input
% 1.99/1.03  --splitting_grd                         true
% 1.99/1.03  --splitting_cvd                         false
% 1.99/1.03  --splitting_cvd_svl                     false
% 1.99/1.03  --splitting_nvd                         32
% 1.99/1.03  --sub_typing                            true
% 1.99/1.03  --prep_gs_sim                           true
% 1.99/1.03  --prep_unflatten                        true
% 1.99/1.03  --prep_res_sim                          true
% 1.99/1.03  --prep_upred                            true
% 1.99/1.03  --prep_sem_filter                       exhaustive
% 1.99/1.03  --prep_sem_filter_out                   false
% 1.99/1.03  --pred_elim                             true
% 1.99/1.03  --res_sim_input                         true
% 1.99/1.03  --eq_ax_congr_red                       true
% 1.99/1.03  --pure_diseq_elim                       true
% 1.99/1.03  --brand_transform                       false
% 1.99/1.03  --non_eq_to_eq                          false
% 1.99/1.03  --prep_def_merge                        true
% 1.99/1.03  --prep_def_merge_prop_impl              false
% 1.99/1.03  --prep_def_merge_mbd                    true
% 1.99/1.03  --prep_def_merge_tr_red                 false
% 1.99/1.03  --prep_def_merge_tr_cl                  false
% 1.99/1.03  --smt_preprocessing                     true
% 1.99/1.03  --smt_ac_axioms                         fast
% 1.99/1.03  --preprocessed_out                      false
% 1.99/1.03  --preprocessed_stats                    false
% 1.99/1.03  
% 1.99/1.03  ------ Abstraction refinement Options
% 1.99/1.03  
% 1.99/1.03  --abstr_ref                             []
% 1.99/1.03  --abstr_ref_prep                        false
% 1.99/1.03  --abstr_ref_until_sat                   false
% 1.99/1.03  --abstr_ref_sig_restrict                funpre
% 1.99/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.03  --abstr_ref_under                       []
% 1.99/1.03  
% 1.99/1.03  ------ SAT Options
% 1.99/1.03  
% 1.99/1.03  --sat_mode                              false
% 1.99/1.03  --sat_fm_restart_options                ""
% 1.99/1.03  --sat_gr_def                            false
% 1.99/1.03  --sat_epr_types                         true
% 1.99/1.03  --sat_non_cyclic_types                  false
% 1.99/1.03  --sat_finite_models                     false
% 1.99/1.03  --sat_fm_lemmas                         false
% 1.99/1.03  --sat_fm_prep                           false
% 1.99/1.03  --sat_fm_uc_incr                        true
% 1.99/1.03  --sat_out_model                         small
% 1.99/1.03  --sat_out_clauses                       false
% 1.99/1.03  
% 1.99/1.03  ------ QBF Options
% 1.99/1.03  
% 1.99/1.03  --qbf_mode                              false
% 1.99/1.03  --qbf_elim_univ                         false
% 1.99/1.03  --qbf_dom_inst                          none
% 1.99/1.03  --qbf_dom_pre_inst                      false
% 1.99/1.03  --qbf_sk_in                             false
% 1.99/1.03  --qbf_pred_elim                         true
% 1.99/1.03  --qbf_split                             512
% 1.99/1.03  
% 1.99/1.03  ------ BMC1 Options
% 1.99/1.03  
% 1.99/1.03  --bmc1_incremental                      false
% 1.99/1.03  --bmc1_axioms                           reachable_all
% 1.99/1.03  --bmc1_min_bound                        0
% 1.99/1.03  --bmc1_max_bound                        -1
% 1.99/1.03  --bmc1_max_bound_default                -1
% 1.99/1.03  --bmc1_symbol_reachability              true
% 1.99/1.03  --bmc1_property_lemmas                  false
% 1.99/1.03  --bmc1_k_induction                      false
% 1.99/1.03  --bmc1_non_equiv_states                 false
% 1.99/1.03  --bmc1_deadlock                         false
% 1.99/1.03  --bmc1_ucm                              false
% 1.99/1.03  --bmc1_add_unsat_core                   none
% 1.99/1.03  --bmc1_unsat_core_children              false
% 1.99/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.03  --bmc1_out_stat                         full
% 1.99/1.03  --bmc1_ground_init                      false
% 1.99/1.03  --bmc1_pre_inst_next_state              false
% 1.99/1.03  --bmc1_pre_inst_state                   false
% 1.99/1.03  --bmc1_pre_inst_reach_state             false
% 1.99/1.03  --bmc1_out_unsat_core                   false
% 1.99/1.03  --bmc1_aig_witness_out                  false
% 1.99/1.03  --bmc1_verbose                          false
% 1.99/1.03  --bmc1_dump_clauses_tptp                false
% 1.99/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.03  --bmc1_dump_file                        -
% 1.99/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.03  --bmc1_ucm_extend_mode                  1
% 1.99/1.03  --bmc1_ucm_init_mode                    2
% 1.99/1.03  --bmc1_ucm_cone_mode                    none
% 1.99/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.03  --bmc1_ucm_relax_model                  4
% 1.99/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.03  --bmc1_ucm_layered_model                none
% 1.99/1.03  --bmc1_ucm_max_lemma_size               10
% 1.99/1.03  
% 1.99/1.03  ------ AIG Options
% 1.99/1.03  
% 1.99/1.03  --aig_mode                              false
% 1.99/1.03  
% 1.99/1.03  ------ Instantiation Options
% 1.99/1.03  
% 1.99/1.03  --instantiation_flag                    true
% 1.99/1.03  --inst_sos_flag                         false
% 1.99/1.03  --inst_sos_phase                        true
% 1.99/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.03  --inst_lit_sel_side                     num_symb
% 1.99/1.03  --inst_solver_per_active                1400
% 1.99/1.03  --inst_solver_calls_frac                1.
% 1.99/1.03  --inst_passive_queue_type               priority_queues
% 1.99/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.03  --inst_passive_queues_freq              [25;2]
% 1.99/1.03  --inst_dismatching                      true
% 1.99/1.03  --inst_eager_unprocessed_to_passive     true
% 1.99/1.03  --inst_prop_sim_given                   true
% 1.99/1.03  --inst_prop_sim_new                     false
% 1.99/1.03  --inst_subs_new                         false
% 1.99/1.03  --inst_eq_res_simp                      false
% 1.99/1.03  --inst_subs_given                       false
% 1.99/1.03  --inst_orphan_elimination               true
% 1.99/1.03  --inst_learning_loop_flag               true
% 1.99/1.03  --inst_learning_start                   3000
% 1.99/1.03  --inst_learning_factor                  2
% 1.99/1.03  --inst_start_prop_sim_after_learn       3
% 1.99/1.03  --inst_sel_renew                        solver
% 1.99/1.03  --inst_lit_activity_flag                true
% 1.99/1.03  --inst_restr_to_given                   false
% 1.99/1.03  --inst_activity_threshold               500
% 1.99/1.03  --inst_out_proof                        true
% 1.99/1.03  
% 1.99/1.03  ------ Resolution Options
% 1.99/1.03  
% 1.99/1.03  --resolution_flag                       true
% 1.99/1.03  --res_lit_sel                           adaptive
% 1.99/1.03  --res_lit_sel_side                      none
% 1.99/1.03  --res_ordering                          kbo
% 1.99/1.03  --res_to_prop_solver                    active
% 1.99/1.03  --res_prop_simpl_new                    false
% 1.99/1.03  --res_prop_simpl_given                  true
% 1.99/1.03  --res_passive_queue_type                priority_queues
% 1.99/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.03  --res_passive_queues_freq               [15;5]
% 1.99/1.03  --res_forward_subs                      full
% 1.99/1.03  --res_backward_subs                     full
% 1.99/1.03  --res_forward_subs_resolution           true
% 1.99/1.03  --res_backward_subs_resolution          true
% 1.99/1.03  --res_orphan_elimination                true
% 1.99/1.03  --res_time_limit                        2.
% 1.99/1.03  --res_out_proof                         true
% 1.99/1.03  
% 1.99/1.03  ------ Superposition Options
% 1.99/1.03  
% 1.99/1.03  --superposition_flag                    true
% 1.99/1.03  --sup_passive_queue_type                priority_queues
% 1.99/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.03  --demod_completeness_check              fast
% 1.99/1.03  --demod_use_ground                      true
% 1.99/1.03  --sup_to_prop_solver                    passive
% 1.99/1.03  --sup_prop_simpl_new                    true
% 1.99/1.03  --sup_prop_simpl_given                  true
% 1.99/1.03  --sup_fun_splitting                     false
% 1.99/1.03  --sup_smt_interval                      50000
% 1.99/1.03  
% 1.99/1.03  ------ Superposition Simplification Setup
% 1.99/1.03  
% 1.99/1.03  --sup_indices_passive                   []
% 1.99/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.03  --sup_full_bw                           [BwDemod]
% 1.99/1.03  --sup_immed_triv                        [TrivRules]
% 1.99/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.03  --sup_immed_bw_main                     []
% 1.99/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.03  
% 1.99/1.03  ------ Combination Options
% 1.99/1.03  
% 1.99/1.03  --comb_res_mult                         3
% 1.99/1.03  --comb_sup_mult                         2
% 1.99/1.03  --comb_inst_mult                        10
% 1.99/1.03  
% 1.99/1.03  ------ Debug Options
% 1.99/1.03  
% 1.99/1.03  --dbg_backtrace                         false
% 1.99/1.03  --dbg_dump_prop_clauses                 false
% 1.99/1.03  --dbg_dump_prop_clauses_file            -
% 1.99/1.03  --dbg_out_stat                          false
% 1.99/1.03  ------ Parsing...
% 1.99/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/1.03  
% 1.99/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.99/1.03  
% 1.99/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/1.03  
% 1.99/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/1.03  ------ Proving...
% 1.99/1.03  ------ Problem Properties 
% 1.99/1.03  
% 1.99/1.03  
% 1.99/1.03  clauses                                 18
% 1.99/1.03  conjectures                             2
% 1.99/1.03  EPR                                     1
% 1.99/1.03  Horn                                    11
% 1.99/1.03  unary                                   0
% 1.99/1.03  binary                                  12
% 1.99/1.03  lits                                    43
% 1.99/1.03  lits eq                                 12
% 1.99/1.03  fd_pure                                 0
% 1.99/1.03  fd_pseudo                               0
% 1.99/1.03  fd_cond                                 0
% 1.99/1.03  fd_pseudo_cond                          3
% 1.99/1.03  AC symbols                              0
% 1.99/1.03  
% 1.99/1.03  ------ Schedule dynamic 5 is on 
% 1.99/1.03  
% 1.99/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/1.03  
% 1.99/1.03  
% 1.99/1.03  ------ 
% 1.99/1.03  Current options:
% 1.99/1.03  ------ 
% 1.99/1.03  
% 1.99/1.03  ------ Input Options
% 1.99/1.03  
% 1.99/1.03  --out_options                           all
% 1.99/1.03  --tptp_safe_out                         true
% 1.99/1.03  --problem_path                          ""
% 1.99/1.03  --include_path                          ""
% 1.99/1.03  --clausifier                            res/vclausify_rel
% 1.99/1.03  --clausifier_options                    --mode clausify
% 1.99/1.03  --stdin                                 false
% 1.99/1.03  --stats_out                             all
% 1.99/1.03  
% 1.99/1.03  ------ General Options
% 1.99/1.03  
% 1.99/1.03  --fof                                   false
% 1.99/1.03  --time_out_real                         305.
% 1.99/1.03  --time_out_virtual                      -1.
% 1.99/1.03  --symbol_type_check                     false
% 1.99/1.03  --clausify_out                          false
% 1.99/1.03  --sig_cnt_out                           false
% 1.99/1.03  --trig_cnt_out                          false
% 1.99/1.03  --trig_cnt_out_tolerance                1.
% 1.99/1.03  --trig_cnt_out_sk_spl                   false
% 1.99/1.03  --abstr_cl_out                          false
% 1.99/1.03  
% 1.99/1.03  ------ Global Options
% 1.99/1.03  
% 1.99/1.03  --schedule                              default
% 1.99/1.03  --add_important_lit                     false
% 1.99/1.03  --prop_solver_per_cl                    1000
% 1.99/1.03  --min_unsat_core                        false
% 1.99/1.03  --soft_assumptions                      false
% 1.99/1.03  --soft_lemma_size                       3
% 1.99/1.03  --prop_impl_unit_size                   0
% 1.99/1.03  --prop_impl_unit                        []
% 1.99/1.03  --share_sel_clauses                     true
% 1.99/1.03  --reset_solvers                         false
% 1.99/1.03  --bc_imp_inh                            [conj_cone]
% 1.99/1.03  --conj_cone_tolerance                   3.
% 1.99/1.03  --extra_neg_conj                        none
% 1.99/1.03  --large_theory_mode                     true
% 1.99/1.03  --prolific_symb_bound                   200
% 1.99/1.03  --lt_threshold                          2000
% 1.99/1.03  --clause_weak_htbl                      true
% 1.99/1.03  --gc_record_bc_elim                     false
% 1.99/1.03  
% 1.99/1.03  ------ Preprocessing Options
% 1.99/1.03  
% 1.99/1.03  --preprocessing_flag                    true
% 1.99/1.03  --time_out_prep_mult                    0.1
% 1.99/1.03  --splitting_mode                        input
% 1.99/1.03  --splitting_grd                         true
% 1.99/1.03  --splitting_cvd                         false
% 1.99/1.03  --splitting_cvd_svl                     false
% 1.99/1.03  --splitting_nvd                         32
% 1.99/1.03  --sub_typing                            true
% 1.99/1.03  --prep_gs_sim                           true
% 1.99/1.03  --prep_unflatten                        true
% 1.99/1.03  --prep_res_sim                          true
% 1.99/1.03  --prep_upred                            true
% 1.99/1.03  --prep_sem_filter                       exhaustive
% 1.99/1.03  --prep_sem_filter_out                   false
% 1.99/1.03  --pred_elim                             true
% 1.99/1.03  --res_sim_input                         true
% 1.99/1.03  --eq_ax_congr_red                       true
% 1.99/1.03  --pure_diseq_elim                       true
% 1.99/1.03  --brand_transform                       false
% 1.99/1.03  --non_eq_to_eq                          false
% 1.99/1.03  --prep_def_merge                        true
% 1.99/1.03  --prep_def_merge_prop_impl              false
% 1.99/1.03  --prep_def_merge_mbd                    true
% 1.99/1.03  --prep_def_merge_tr_red                 false
% 1.99/1.03  --prep_def_merge_tr_cl                  false
% 1.99/1.03  --smt_preprocessing                     true
% 1.99/1.03  --smt_ac_axioms                         fast
% 1.99/1.03  --preprocessed_out                      false
% 1.99/1.03  --preprocessed_stats                    false
% 1.99/1.03  
% 1.99/1.03  ------ Abstraction refinement Options
% 1.99/1.03  
% 1.99/1.03  --abstr_ref                             []
% 1.99/1.03  --abstr_ref_prep                        false
% 1.99/1.03  --abstr_ref_until_sat                   false
% 1.99/1.03  --abstr_ref_sig_restrict                funpre
% 1.99/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.03  --abstr_ref_under                       []
% 1.99/1.03  
% 1.99/1.03  ------ SAT Options
% 1.99/1.03  
% 1.99/1.03  --sat_mode                              false
% 1.99/1.03  --sat_fm_restart_options                ""
% 1.99/1.03  --sat_gr_def                            false
% 1.99/1.03  --sat_epr_types                         true
% 1.99/1.03  --sat_non_cyclic_types                  false
% 1.99/1.03  --sat_finite_models                     false
% 1.99/1.03  --sat_fm_lemmas                         false
% 1.99/1.03  --sat_fm_prep                           false
% 1.99/1.03  --sat_fm_uc_incr                        true
% 1.99/1.03  --sat_out_model                         small
% 1.99/1.03  --sat_out_clauses                       false
% 1.99/1.03  
% 1.99/1.03  ------ QBF Options
% 1.99/1.03  
% 1.99/1.03  --qbf_mode                              false
% 1.99/1.03  --qbf_elim_univ                         false
% 1.99/1.03  --qbf_dom_inst                          none
% 1.99/1.03  --qbf_dom_pre_inst                      false
% 1.99/1.03  --qbf_sk_in                             false
% 1.99/1.03  --qbf_pred_elim                         true
% 1.99/1.03  --qbf_split                             512
% 1.99/1.03  
% 1.99/1.03  ------ BMC1 Options
% 1.99/1.03  
% 1.99/1.03  --bmc1_incremental                      false
% 1.99/1.03  --bmc1_axioms                           reachable_all
% 1.99/1.03  --bmc1_min_bound                        0
% 1.99/1.03  --bmc1_max_bound                        -1
% 1.99/1.03  --bmc1_max_bound_default                -1
% 1.99/1.03  --bmc1_symbol_reachability              true
% 1.99/1.03  --bmc1_property_lemmas                  false
% 1.99/1.03  --bmc1_k_induction                      false
% 1.99/1.03  --bmc1_non_equiv_states                 false
% 1.99/1.03  --bmc1_deadlock                         false
% 1.99/1.03  --bmc1_ucm                              false
% 1.99/1.03  --bmc1_add_unsat_core                   none
% 1.99/1.03  --bmc1_unsat_core_children              false
% 1.99/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.03  --bmc1_out_stat                         full
% 1.99/1.03  --bmc1_ground_init                      false
% 1.99/1.03  --bmc1_pre_inst_next_state              false
% 1.99/1.03  --bmc1_pre_inst_state                   false
% 1.99/1.03  --bmc1_pre_inst_reach_state             false
% 1.99/1.03  --bmc1_out_unsat_core                   false
% 1.99/1.03  --bmc1_aig_witness_out                  false
% 1.99/1.03  --bmc1_verbose                          false
% 1.99/1.03  --bmc1_dump_clauses_tptp                false
% 1.99/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.03  --bmc1_dump_file                        -
% 1.99/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.03  --bmc1_ucm_extend_mode                  1
% 1.99/1.03  --bmc1_ucm_init_mode                    2
% 1.99/1.03  --bmc1_ucm_cone_mode                    none
% 1.99/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.03  --bmc1_ucm_relax_model                  4
% 1.99/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.03  --bmc1_ucm_layered_model                none
% 1.99/1.03  --bmc1_ucm_max_lemma_size               10
% 1.99/1.03  
% 1.99/1.03  ------ AIG Options
% 1.99/1.03  
% 1.99/1.03  --aig_mode                              false
% 1.99/1.03  
% 1.99/1.03  ------ Instantiation Options
% 1.99/1.03  
% 1.99/1.03  --instantiation_flag                    true
% 1.99/1.03  --inst_sos_flag                         false
% 1.99/1.03  --inst_sos_phase                        true
% 1.99/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.03  --inst_lit_sel_side                     none
% 1.99/1.03  --inst_solver_per_active                1400
% 1.99/1.03  --inst_solver_calls_frac                1.
% 1.99/1.03  --inst_passive_queue_type               priority_queues
% 1.99/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.03  --inst_passive_queues_freq              [25;2]
% 1.99/1.03  --inst_dismatching                      true
% 1.99/1.03  --inst_eager_unprocessed_to_passive     true
% 1.99/1.03  --inst_prop_sim_given                   true
% 1.99/1.03  --inst_prop_sim_new                     false
% 1.99/1.03  --inst_subs_new                         false
% 1.99/1.03  --inst_eq_res_simp                      false
% 1.99/1.03  --inst_subs_given                       false
% 1.99/1.03  --inst_orphan_elimination               true
% 1.99/1.03  --inst_learning_loop_flag               true
% 1.99/1.03  --inst_learning_start                   3000
% 1.99/1.03  --inst_learning_factor                  2
% 1.99/1.03  --inst_start_prop_sim_after_learn       3
% 1.99/1.03  --inst_sel_renew                        solver
% 1.99/1.03  --inst_lit_activity_flag                true
% 1.99/1.03  --inst_restr_to_given                   false
% 1.99/1.03  --inst_activity_threshold               500
% 1.99/1.03  --inst_out_proof                        true
% 1.99/1.03  
% 1.99/1.03  ------ Resolution Options
% 1.99/1.03  
% 1.99/1.03  --resolution_flag                       false
% 1.99/1.03  --res_lit_sel                           adaptive
% 1.99/1.03  --res_lit_sel_side                      none
% 1.99/1.03  --res_ordering                          kbo
% 1.99/1.03  --res_to_prop_solver                    active
% 1.99/1.03  --res_prop_simpl_new                    false
% 1.99/1.03  --res_prop_simpl_given                  true
% 1.99/1.03  --res_passive_queue_type                priority_queues
% 1.99/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.03  --res_passive_queues_freq               [15;5]
% 1.99/1.03  --res_forward_subs                      full
% 1.99/1.03  --res_backward_subs                     full
% 1.99/1.03  --res_forward_subs_resolution           true
% 1.99/1.03  --res_backward_subs_resolution          true
% 1.99/1.03  --res_orphan_elimination                true
% 1.99/1.03  --res_time_limit                        2.
% 1.99/1.03  --res_out_proof                         true
% 1.99/1.03  
% 1.99/1.03  ------ Superposition Options
% 1.99/1.03  
% 1.99/1.03  --superposition_flag                    true
% 1.99/1.03  --sup_passive_queue_type                priority_queues
% 1.99/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.03  --demod_completeness_check              fast
% 1.99/1.03  --demod_use_ground                      true
% 1.99/1.03  --sup_to_prop_solver                    passive
% 1.99/1.03  --sup_prop_simpl_new                    true
% 1.99/1.03  --sup_prop_simpl_given                  true
% 1.99/1.03  --sup_fun_splitting                     false
% 1.99/1.03  --sup_smt_interval                      50000
% 1.99/1.03  
% 1.99/1.03  ------ Superposition Simplification Setup
% 1.99/1.03  
% 1.99/1.03  --sup_indices_passive                   []
% 1.99/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.03  --sup_full_bw                           [BwDemod]
% 1.99/1.03  --sup_immed_triv                        [TrivRules]
% 1.99/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.03  --sup_immed_bw_main                     []
% 1.99/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.03  
% 1.99/1.03  ------ Combination Options
% 1.99/1.03  
% 1.99/1.03  --comb_res_mult                         3
% 1.99/1.03  --comb_sup_mult                         2
% 1.99/1.03  --comb_inst_mult                        10
% 1.99/1.03  
% 1.99/1.03  ------ Debug Options
% 1.99/1.03  
% 1.99/1.03  --dbg_backtrace                         false
% 1.99/1.03  --dbg_dump_prop_clauses                 false
% 1.99/1.03  --dbg_dump_prop_clauses_file            -
% 1.99/1.03  --dbg_out_stat                          false
% 1.99/1.03  
% 1.99/1.03  
% 1.99/1.03  
% 1.99/1.03  
% 1.99/1.03  ------ Proving...
% 1.99/1.03  
% 1.99/1.03  
% 1.99/1.03  % SZS status Theorem for theBenchmark.p
% 1.99/1.03  
% 1.99/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/1.03  
% 1.99/1.03  fof(f8,axiom,(
% 1.99/1.03    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.03  
% 1.99/1.03  fof(f24,plain,(
% 1.99/1.03    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 1.99/1.03    inference(nnf_transformation,[],[f8])).
% 1.99/1.03  
% 1.99/1.03  fof(f25,plain,(
% 1.99/1.03    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 1.99/1.03    inference(flattening,[],[f24])).
% 1.99/1.03  
% 1.99/1.03  fof(f48,plain,(
% 1.99/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.99/1.03    inference(cnf_transformation,[],[f25])).
% 1.99/1.03  
% 1.99/1.03  fof(f5,axiom,(
% 1.99/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.03  
% 1.99/1.03  fof(f43,plain,(
% 1.99/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.99/1.03    inference(cnf_transformation,[],[f5])).
% 1.99/1.03  
% 1.99/1.03  fof(f6,axiom,(
% 1.99/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.03  
% 1.99/1.03  fof(f44,plain,(
% 1.99/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.99/1.03    inference(cnf_transformation,[],[f6])).
% 1.99/1.03  
% 1.99/1.03  fof(f7,axiom,(
% 1.99/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.03  
% 1.99/1.03  fof(f45,plain,(
% 1.99/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.99/1.03    inference(cnf_transformation,[],[f7])).
% 1.99/1.03  
% 1.99/1.03  fof(f54,plain,(
% 1.99/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.99/1.03    inference(definition_unfolding,[],[f44,f45])).
% 1.99/1.03  
% 1.99/1.03  fof(f55,plain,(
% 1.99/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.99/1.03    inference(definition_unfolding,[],[f43,f54])).
% 1.99/1.03  
% 1.99/1.03  fof(f57,plain,(
% 1.99/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.99/1.03    inference(definition_unfolding,[],[f48,f55,f55])).
% 1.99/1.03  
% 1.99/1.03  fof(f10,conjecture,(
% 1.99/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 1.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.03  
% 1.99/1.03  fof(f11,negated_conjecture,(
% 1.99/1.03    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 1.99/1.03    inference(negated_conjecture,[],[f10])).
% 1.99/1.03  
% 1.99/1.03  fof(f15,plain,(
% 1.99/1.03    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) & v1_relat_1(X1))),
% 1.99/1.03    inference(ennf_transformation,[],[f11])).
% 1.99/1.03  
% 1.99/1.03  fof(f27,plain,(
% 1.99/1.03    ? [X0,X1] : (((k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1))) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 1.99/1.03    inference(nnf_transformation,[],[f15])).
% 1.99/1.03  
% 1.99/1.03  fof(f28,plain,(
% 1.99/1.03    ? [X0,X1] : ((k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1))) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 1.99/1.04    inference(flattening,[],[f27])).
% 1.99/1.04  
% 1.99/1.04  fof(f29,plain,(
% 1.99/1.04    ? [X0,X1] : ((k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1))) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0 | ~r2_hidden(sK2,k2_relat_1(sK3))) & (k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0 | r2_hidden(sK2,k2_relat_1(sK3))) & v1_relat_1(sK3))),
% 1.99/1.04    introduced(choice_axiom,[])).
% 1.99/1.04  
% 1.99/1.04  fof(f30,plain,(
% 1.99/1.04    (k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0 | ~r2_hidden(sK2,k2_relat_1(sK3))) & (k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0 | r2_hidden(sK2,k2_relat_1(sK3))) & v1_relat_1(sK3)),
% 1.99/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f29])).
% 1.99/1.04  
% 1.99/1.04  fof(f53,plain,(
% 1.99/1.04    k10_relat_1(sK3,k1_tarski(sK2)) = k1_xboole_0 | ~r2_hidden(sK2,k2_relat_1(sK3))),
% 1.99/1.04    inference(cnf_transformation,[],[f30])).
% 1.99/1.04  
% 1.99/1.04  fof(f4,axiom,(
% 1.99/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.04  
% 1.99/1.04  fof(f42,plain,(
% 1.99/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.99/1.04    inference(cnf_transformation,[],[f4])).
% 1.99/1.04  
% 1.99/1.04  fof(f56,plain,(
% 1.99/1.04    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.99/1.04    inference(definition_unfolding,[],[f42,f55])).
% 1.99/1.04  
% 1.99/1.04  fof(f60,plain,(
% 1.99/1.04    k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 | ~r2_hidden(sK2,k2_relat_1(sK3))),
% 1.99/1.04    inference(definition_unfolding,[],[f53,f56])).
% 1.99/1.04  
% 1.99/1.04  fof(f2,axiom,(
% 1.99/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.04  
% 1.99/1.04  fof(f12,plain,(
% 1.99/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.99/1.04    inference(rectify,[],[f2])).
% 1.99/1.04  
% 1.99/1.04  fof(f13,plain,(
% 1.99/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.99/1.04    inference(ennf_transformation,[],[f12])).
% 1.99/1.04  
% 1.99/1.04  fof(f21,plain,(
% 1.99/1.04    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.99/1.04    introduced(choice_axiom,[])).
% 1.99/1.04  
% 1.99/1.04  fof(f22,plain,(
% 1.99/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.99/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).
% 1.99/1.04  
% 1.99/1.04  fof(f37,plain,(
% 1.99/1.04    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.99/1.04    inference(cnf_transformation,[],[f22])).
% 1.99/1.04  
% 1.99/1.04  fof(f38,plain,(
% 1.99/1.04    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.99/1.04    inference(cnf_transformation,[],[f22])).
% 1.99/1.04  
% 1.99/1.04  fof(f1,axiom,(
% 1.99/1.04    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.04  
% 1.99/1.04  fof(f16,plain,(
% 1.99/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.99/1.04    inference(nnf_transformation,[],[f1])).
% 1.99/1.04  
% 1.99/1.04  fof(f17,plain,(
% 1.99/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.99/1.04    inference(flattening,[],[f16])).
% 1.99/1.04  
% 1.99/1.04  fof(f18,plain,(
% 1.99/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.99/1.04    inference(rectify,[],[f17])).
% 1.99/1.04  
% 1.99/1.04  fof(f19,plain,(
% 1.99/1.04    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.99/1.04    introduced(choice_axiom,[])).
% 1.99/1.04  
% 1.99/1.04  fof(f20,plain,(
% 1.99/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.99/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 1.99/1.04  
% 1.99/1.04  fof(f32,plain,(
% 1.99/1.04    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.99/1.04    inference(cnf_transformation,[],[f20])).
% 1.99/1.04  
% 1.99/1.04  fof(f63,plain,(
% 1.99/1.04    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.99/1.04    inference(equality_resolution,[],[f32])).
% 1.99/1.04  
% 1.99/1.04  fof(f9,axiom,(
% 1.99/1.04    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.04  
% 1.99/1.04  fof(f14,plain,(
% 1.99/1.04    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.99/1.04    inference(ennf_transformation,[],[f9])).
% 1.99/1.04  
% 1.99/1.04  fof(f26,plain,(
% 1.99/1.04    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 1.99/1.04    inference(nnf_transformation,[],[f14])).
% 1.99/1.04  
% 1.99/1.04  fof(f50,plain,(
% 1.99/1.04    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.99/1.04    inference(cnf_transformation,[],[f26])).
% 1.99/1.04  
% 1.99/1.04  fof(f51,plain,(
% 1.99/1.04    v1_relat_1(sK3)),
% 1.99/1.04    inference(cnf_transformation,[],[f30])).
% 1.99/1.04  
% 1.99/1.04  fof(f49,plain,(
% 1.99/1.04    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0 | ~v1_relat_1(X1)) )),
% 1.99/1.04    inference(cnf_transformation,[],[f26])).
% 1.99/1.04  
% 1.99/1.04  fof(f3,axiom,(
% 1.99/1.04    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.99/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.99/1.04  
% 1.99/1.04  fof(f23,plain,(
% 1.99/1.04    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.99/1.04    inference(nnf_transformation,[],[f3])).
% 1.99/1.04  
% 1.99/1.04  fof(f40,plain,(
% 1.99/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.99/1.04    inference(cnf_transformation,[],[f23])).
% 1.99/1.04  
% 1.99/1.04  fof(f46,plain,(
% 1.99/1.04    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 1.99/1.04    inference(cnf_transformation,[],[f25])).
% 1.99/1.04  
% 1.99/1.04  fof(f59,plain,(
% 1.99/1.04    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) != k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.99/1.04    inference(definition_unfolding,[],[f46,f55,f55])).
% 1.99/1.04  
% 1.99/1.04  fof(f52,plain,(
% 1.99/1.04    k10_relat_1(sK3,k1_tarski(sK2)) != k1_xboole_0 | r2_hidden(sK2,k2_relat_1(sK3))),
% 1.99/1.04    inference(cnf_transformation,[],[f30])).
% 1.99/1.04  
% 1.99/1.04  fof(f61,plain,(
% 1.99/1.04    k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0 | r2_hidden(sK2,k2_relat_1(sK3))),
% 1.99/1.04    inference(definition_unfolding,[],[f52,f56])).
% 1.99/1.04  
% 1.99/1.04  cnf(c_11,plain,
% 1.99/1.04      ( r2_hidden(X0,X1)
% 1.99/1.04      | r2_hidden(X2,X1)
% 1.99/1.04      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) = k3_enumset1(X0,X0,X0,X0,X2) ),
% 1.99/1.04      inference(cnf_transformation,[],[f57]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1202,plain,
% 1.99/1.04      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 1.99/1.04      | r2_hidden(X0,X2) = iProver_top
% 1.99/1.04      | r2_hidden(X1,X2) = iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_16,negated_conjecture,
% 1.99/1.04      ( ~ r2_hidden(sK2,k2_relat_1(sK3))
% 1.99/1.04      | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 1.99/1.04      inference(cnf_transformation,[],[f60]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1199,plain,
% 1.99/1.04      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
% 1.99/1.04      | r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1929,plain,
% 1.99/1.04      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
% 1.99/1.04      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,sK2),k2_relat_1(sK3)) = k3_enumset1(X0,X0,X0,X0,sK2)
% 1.99/1.04      | r2_hidden(X0,k2_relat_1(sK3)) = iProver_top ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_1202,c_1199]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_2334,plain,
% 1.99/1.04      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0
% 1.99/1.04      | k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k2_relat_1(sK3)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_1929,c_1199]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_8,plain,
% 1.99/1.04      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.99/1.04      inference(cnf_transformation,[],[f37]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1205,plain,
% 1.99/1.04      ( r1_xboole_0(X0,X1) = iProver_top
% 1.99/1.04      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_7,plain,
% 1.99/1.04      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 1.99/1.04      inference(cnf_transformation,[],[f38]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1206,plain,
% 1.99/1.04      ( r1_xboole_0(X0,X1) = iProver_top
% 1.99/1.04      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_4,plain,
% 1.99/1.04      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 1.99/1.04      inference(cnf_transformation,[],[f63]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1209,plain,
% 1.99/1.04      ( r2_hidden(X0,X1) != iProver_top
% 1.99/1.04      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1550,plain,
% 1.99/1.04      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 1.99/1.04      | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_1206,c_1209]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1723,plain,
% 1.99/1.04      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_1205,c_1550]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_14,plain,
% 1.99/1.04      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 1.99/1.04      | ~ v1_relat_1(X0)
% 1.99/1.04      | k10_relat_1(X0,X1) = k1_xboole_0 ),
% 1.99/1.04      inference(cnf_transformation,[],[f50]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_18,negated_conjecture,
% 1.99/1.04      ( v1_relat_1(sK3) ),
% 1.99/1.04      inference(cnf_transformation,[],[f51]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_272,plain,
% 1.99/1.04      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 1.99/1.04      | k10_relat_1(X0,X1) = k1_xboole_0
% 1.99/1.04      | sK3 != X0 ),
% 1.99/1.04      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_273,plain,
% 1.99/1.04      ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
% 1.99/1.04      | k10_relat_1(sK3,X0) = k1_xboole_0 ),
% 1.99/1.04      inference(unflattening,[status(thm)],[c_272]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_509,plain,
% 1.99/1.04      ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
% 1.99/1.04      | k10_relat_1(sK3,X0) = k1_xboole_0 ),
% 1.99/1.04      inference(prop_impl,[status(thm)],[c_273]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1196,plain,
% 1.99/1.04      ( k10_relat_1(sK3,X0) = k1_xboole_0
% 1.99/1.04      | r1_xboole_0(k2_relat_1(sK3),X0) != iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1745,plain,
% 1.99/1.04      ( k10_relat_1(sK3,k4_xboole_0(X0,k2_relat_1(sK3))) = k1_xboole_0 ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_1723,c_1196]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_2392,plain,
% 1.99/1.04      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_2334,c_1745]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_15,plain,
% 1.99/1.04      ( r1_xboole_0(k2_relat_1(X0),X1)
% 1.99/1.04      | ~ v1_relat_1(X0)
% 1.99/1.04      | k10_relat_1(X0,X1) != k1_xboole_0 ),
% 1.99/1.04      inference(cnf_transformation,[],[f49]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_260,plain,
% 1.99/1.04      ( r1_xboole_0(k2_relat_1(X0),X1)
% 1.99/1.04      | k10_relat_1(X0,X1) != k1_xboole_0
% 1.99/1.04      | sK3 != X0 ),
% 1.99/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_261,plain,
% 1.99/1.04      ( r1_xboole_0(k2_relat_1(sK3),X0)
% 1.99/1.04      | k10_relat_1(sK3,X0) != k1_xboole_0 ),
% 1.99/1.04      inference(unflattening,[status(thm)],[c_260]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_507,plain,
% 1.99/1.04      ( r1_xboole_0(k2_relat_1(sK3),X0)
% 1.99/1.04      | k10_relat_1(sK3,X0) != k1_xboole_0 ),
% 1.99/1.04      inference(prop_impl,[status(thm)],[c_261]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1197,plain,
% 1.99/1.04      ( k10_relat_1(sK3,X0) != k1_xboole_0
% 1.99/1.04      | r1_xboole_0(k2_relat_1(sK3),X0) = iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_2462,plain,
% 1.99/1.04      ( r1_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_2392,c_1197]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_10,plain,
% 1.99/1.04      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 1.99/1.04      inference(cnf_transformation,[],[f40]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1203,plain,
% 1.99/1.04      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_2562,plain,
% 1.99/1.04      ( k4_xboole_0(k2_relat_1(sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k2_relat_1(sK3) ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_2462,c_1203]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1744,plain,
% 1.99/1.04      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_1723,c_1203]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_13,plain,
% 1.99/1.04      ( ~ r2_hidden(X0,X1)
% 1.99/1.04      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) != k3_enumset1(X0,X0,X0,X0,X2) ),
% 1.99/1.04      inference(cnf_transformation,[],[f59]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1200,plain,
% 1.99/1.04      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) != k3_enumset1(X0,X0,X0,X0,X1)
% 1.99/1.04      | r2_hidden(X0,X2) != iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_1819,plain,
% 1.99/1.04      ( r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X2))) != iProver_top ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_1744,c_1200]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_2644,plain,
% 1.99/1.04      ( r2_hidden(sK2,k2_relat_1(sK3)) != iProver_top ),
% 1.99/1.04      inference(superposition,[status(thm)],[c_2562,c_1819]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_17,negated_conjecture,
% 1.99/1.04      ( r2_hidden(sK2,k2_relat_1(sK3))
% 1.99/1.04      | k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0 ),
% 1.99/1.04      inference(cnf_transformation,[],[f61]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(c_20,plain,
% 1.99/1.04      ( k10_relat_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k1_xboole_0
% 1.99/1.04      | r2_hidden(sK2,k2_relat_1(sK3)) = iProver_top ),
% 1.99/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.99/1.04  
% 1.99/1.04  cnf(contradiction,plain,
% 1.99/1.04      ( $false ),
% 1.99/1.04      inference(minisat,[status(thm)],[c_2644,c_2392,c_20]) ).
% 1.99/1.04  
% 1.99/1.04  
% 1.99/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/1.04  
% 1.99/1.04  ------                               Statistics
% 1.99/1.04  
% 1.99/1.04  ------ General
% 1.99/1.04  
% 1.99/1.04  abstr_ref_over_cycles:                  0
% 1.99/1.04  abstr_ref_under_cycles:                 0
% 1.99/1.04  gc_basic_clause_elim:                   0
% 1.99/1.04  forced_gc_time:                         0
% 1.99/1.04  parsing_time:                           0.009
% 1.99/1.04  unif_index_cands_time:                  0.
% 1.99/1.04  unif_index_add_time:                    0.
% 1.99/1.04  orderings_time:                         0.
% 1.99/1.04  out_proof_time:                         0.022
% 1.99/1.04  total_time:                             0.141
% 1.99/1.04  num_of_symbols:                         43
% 1.99/1.04  num_of_terms:                           1795
% 1.99/1.04  
% 1.99/1.04  ------ Preprocessing
% 1.99/1.04  
% 1.99/1.04  num_of_splits:                          0
% 1.99/1.04  num_of_split_atoms:                     0
% 1.99/1.04  num_of_reused_defs:                     0
% 1.99/1.04  num_eq_ax_congr_red:                    21
% 1.99/1.04  num_of_sem_filtered_clauses:            1
% 1.99/1.04  num_of_subtypes:                        0
% 1.99/1.04  monotx_restored_types:                  0
% 1.99/1.04  sat_num_of_epr_types:                   0
% 1.99/1.04  sat_num_of_non_cyclic_types:            0
% 1.99/1.04  sat_guarded_non_collapsed_types:        0
% 1.99/1.04  num_pure_diseq_elim:                    0
% 1.99/1.04  simp_replaced_by:                       0
% 1.99/1.04  res_preprocessed:                       90
% 1.99/1.04  prep_upred:                             0
% 1.99/1.04  prep_unflattend:                        22
% 1.99/1.04  smt_new_axioms:                         0
% 1.99/1.04  pred_elim_cands:                        2
% 1.99/1.04  pred_elim:                              1
% 1.99/1.04  pred_elim_cl:                           1
% 1.99/1.04  pred_elim_cycles:                       3
% 1.99/1.04  merged_defs:                            22
% 1.99/1.04  merged_defs_ncl:                        0
% 1.99/1.04  bin_hyper_res:                          22
% 1.99/1.04  prep_cycles:                            4
% 1.99/1.04  pred_elim_time:                         0.004
% 1.99/1.04  splitting_time:                         0.
% 1.99/1.04  sem_filter_time:                        0.
% 1.99/1.04  monotx_time:                            0.
% 1.99/1.04  subtype_inf_time:                       0.
% 1.99/1.04  
% 1.99/1.04  ------ Problem properties
% 1.99/1.04  
% 1.99/1.04  clauses:                                18
% 1.99/1.04  conjectures:                            2
% 1.99/1.04  epr:                                    1
% 1.99/1.04  horn:                                   11
% 1.99/1.04  ground:                                 2
% 1.99/1.04  unary:                                  0
% 1.99/1.04  binary:                                 12
% 1.99/1.04  lits:                                   43
% 1.99/1.04  lits_eq:                                12
% 1.99/1.04  fd_pure:                                0
% 1.99/1.04  fd_pseudo:                              0
% 1.99/1.04  fd_cond:                                0
% 1.99/1.04  fd_pseudo_cond:                         3
% 1.99/1.04  ac_symbols:                             0
% 1.99/1.04  
% 1.99/1.04  ------ Propositional Solver
% 1.99/1.04  
% 1.99/1.04  prop_solver_calls:                      28
% 1.99/1.04  prop_fast_solver_calls:                 564
% 1.99/1.04  smt_solver_calls:                       0
% 1.99/1.04  smt_fast_solver_calls:                  0
% 1.99/1.04  prop_num_of_clauses:                    635
% 1.99/1.04  prop_preprocess_simplified:             3396
% 1.99/1.04  prop_fo_subsumed:                       0
% 1.99/1.04  prop_solver_time:                       0.
% 1.99/1.04  smt_solver_time:                        0.
% 1.99/1.04  smt_fast_solver_time:                   0.
% 1.99/1.04  prop_fast_solver_time:                  0.
% 1.99/1.04  prop_unsat_core_time:                   0.
% 1.99/1.04  
% 1.99/1.04  ------ QBF
% 1.99/1.04  
% 1.99/1.04  qbf_q_res:                              0
% 1.99/1.04  qbf_num_tautologies:                    0
% 1.99/1.04  qbf_prep_cycles:                        0
% 1.99/1.04  
% 1.99/1.04  ------ BMC1
% 1.99/1.04  
% 1.99/1.04  bmc1_current_bound:                     -1
% 1.99/1.04  bmc1_last_solved_bound:                 -1
% 1.99/1.04  bmc1_unsat_core_size:                   -1
% 1.99/1.04  bmc1_unsat_core_parents_size:           -1
% 1.99/1.04  bmc1_merge_next_fun:                    0
% 1.99/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.99/1.04  
% 1.99/1.04  ------ Instantiation
% 1.99/1.04  
% 1.99/1.04  inst_num_of_clauses:                    161
% 1.99/1.04  inst_num_in_passive:                    23
% 1.99/1.04  inst_num_in_active:                     99
% 1.99/1.04  inst_num_in_unprocessed:                39
% 1.99/1.04  inst_num_of_loops:                      170
% 1.99/1.04  inst_num_of_learning_restarts:          0
% 1.99/1.04  inst_num_moves_active_passive:          67
% 1.99/1.04  inst_lit_activity:                      0
% 1.99/1.04  inst_lit_activity_moves:                0
% 1.99/1.04  inst_num_tautologies:                   0
% 1.99/1.04  inst_num_prop_implied:                  0
% 1.99/1.04  inst_num_existing_simplified:           0
% 1.99/1.04  inst_num_eq_res_simplified:             0
% 1.99/1.04  inst_num_child_elim:                    0
% 1.99/1.04  inst_num_of_dismatching_blockings:      48
% 1.99/1.04  inst_num_of_non_proper_insts:           163
% 1.99/1.04  inst_num_of_duplicates:                 0
% 1.99/1.04  inst_inst_num_from_inst_to_res:         0
% 1.99/1.04  inst_dismatching_checking_time:         0.
% 1.99/1.04  
% 1.99/1.04  ------ Resolution
% 1.99/1.04  
% 1.99/1.04  res_num_of_clauses:                     0
% 1.99/1.04  res_num_in_passive:                     0
% 1.99/1.04  res_num_in_active:                      0
% 1.99/1.04  res_num_of_loops:                       94
% 1.99/1.04  res_forward_subset_subsumed:            8
% 1.99/1.04  res_backward_subset_subsumed:           0
% 1.99/1.04  res_forward_subsumed:                   0
% 1.99/1.04  res_backward_subsumed:                  0
% 1.99/1.04  res_forward_subsumption_resolution:     0
% 1.99/1.04  res_backward_subsumption_resolution:    0
% 1.99/1.04  res_clause_to_clause_subsumption:       400
% 1.99/1.04  res_orphan_elimination:                 0
% 1.99/1.04  res_tautology_del:                      73
% 1.99/1.04  res_num_eq_res_simplified:              0
% 1.99/1.04  res_num_sel_changes:                    0
% 1.99/1.04  res_moves_from_active_to_pass:          0
% 1.99/1.04  
% 1.99/1.04  ------ Superposition
% 1.99/1.04  
% 1.99/1.04  sup_time_total:                         0.
% 1.99/1.04  sup_time_generating:                    0.
% 1.99/1.04  sup_time_sim_full:                      0.
% 1.99/1.04  sup_time_sim_immed:                     0.
% 1.99/1.04  
% 1.99/1.04  sup_num_of_clauses:                     65
% 1.99/1.04  sup_num_in_active:                      29
% 1.99/1.04  sup_num_in_passive:                     36
% 1.99/1.04  sup_num_of_loops:                       32
% 1.99/1.04  sup_fw_superposition:                   24
% 1.99/1.04  sup_bw_superposition:                   80
% 1.99/1.04  sup_immediate_simplified:               16
% 1.99/1.04  sup_given_eliminated:                   0
% 1.99/1.04  comparisons_done:                       0
% 1.99/1.04  comparisons_avoided:                    6
% 1.99/1.04  
% 1.99/1.04  ------ Simplifications
% 1.99/1.04  
% 1.99/1.04  
% 1.99/1.04  sim_fw_subset_subsumed:                 4
% 1.99/1.04  sim_bw_subset_subsumed:                 11
% 1.99/1.04  sim_fw_subsumed:                        5
% 1.99/1.04  sim_bw_subsumed:                        0
% 1.99/1.04  sim_fw_subsumption_res:                 0
% 1.99/1.04  sim_bw_subsumption_res:                 0
% 1.99/1.04  sim_tautology_del:                      12
% 1.99/1.04  sim_eq_tautology_del:                   0
% 1.99/1.04  sim_eq_res_simp:                        3
% 1.99/1.04  sim_fw_demodulated:                     2
% 1.99/1.04  sim_bw_demodulated:                     1
% 1.99/1.04  sim_light_normalised:                   7
% 1.99/1.04  sim_joinable_taut:                      0
% 1.99/1.04  sim_joinable_simp:                      0
% 1.99/1.04  sim_ac_normalised:                      0
% 1.99/1.04  sim_smt_subsumption:                    0
% 1.99/1.04  
%------------------------------------------------------------------------------
