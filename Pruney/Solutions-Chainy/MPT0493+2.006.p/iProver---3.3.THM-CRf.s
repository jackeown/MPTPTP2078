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
% DateTime   : Thu Dec  3 11:44:42 EST 2020

% Result     : Theorem 43.22s
% Output     : CNFRefutation 43.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 105 expanded)
%              Number of clauses        :   29 (  30 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  218 ( 302 expanded)
%              Number of equality atoms :   65 (  93 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
      & r1_tarski(sK2,k1_relat_1(sK3))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    & r1_tarski(sK2,k1_relat_1(sK3))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f27])).

fof(f47,plain,(
    r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f38,f43])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f42,f43,f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f46,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1726,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1727,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1730,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2275,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_1730])).

cnf(c_2640,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_2275])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_217,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | k1_relat_1(sK3) != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_218,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),X0)
    | r1_xboole_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_1722,plain,
    ( r1_xboole_0(k1_relat_1(sK3),X0) != iProver_top
    | r1_xboole_0(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_2932,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(X0,k1_relat_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2640,c_1722])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1724,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3451,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k1_relat_1(sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_2932,c_1724])).

cnf(c_13,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_190400,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,k1_relat_1(sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_3451,c_13])).

cnf(c_12,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_210,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_211,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_1961,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_211])).

cnf(c_2020,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK3))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_1961])).

cnf(c_191478,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_190400,c_2020])).

cnf(c_15,negated_conjecture,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_191478,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 15:09:42 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 43.22/6.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.22/6.00  
% 43.22/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.22/6.00  
% 43.22/6.00  ------  iProver source info
% 43.22/6.00  
% 43.22/6.00  git: date: 2020-06-30 10:37:57 +0100
% 43.22/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.22/6.00  git: non_committed_changes: false
% 43.22/6.00  git: last_make_outside_of_git: false
% 43.22/6.00  
% 43.22/6.00  ------ 
% 43.22/6.00  ------ Parsing...
% 43.22/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.22/6.00  ------ Proving...
% 43.22/6.00  ------ Problem Properties 
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  clauses                                 16
% 43.22/6.00  conjectures                             3
% 43.22/6.00  EPR                                     1
% 43.22/6.00  Horn                                    10
% 43.22/6.00  unary                                   4
% 43.22/6.00  binary                                  7
% 43.22/6.00  lits                                    34
% 43.22/6.00  lits eq                                 9
% 43.22/6.00  fd_pure                                 0
% 43.22/6.00  fd_pseudo                               0
% 43.22/6.00  fd_cond                                 0
% 43.22/6.00  fd_pseudo_cond                          3
% 43.22/6.00  AC symbols                              0
% 43.22/6.00  
% 43.22/6.00  ------ Input Options Time Limit: Unbounded
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 43.22/6.00  Current options:
% 43.22/6.00  ------ 
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ Proving...
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.22/6.00  
% 43.22/6.00  ------ Proving...
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.22/6.00  
% 43.22/6.00  ------ Proving...
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.22/6.00  
% 43.22/6.00  ------ Proving...
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.22/6.00  
% 43.22/6.00  ------ Proving...
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.22/6.00  
% 43.22/6.00  ------ Proving...
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.22/6.00  
% 43.22/6.00  ------ Proving...
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  % SZS status Theorem for theBenchmark.p
% 43.22/6.00  
% 43.22/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.22/6.00  
% 43.22/6.00  fof(f2,axiom,(
% 43.22/6.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f12,plain,(
% 43.22/6.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 43.22/6.00    inference(rectify,[],[f2])).
% 43.22/6.00  
% 43.22/6.00  fof(f13,plain,(
% 43.22/6.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 43.22/6.00    inference(ennf_transformation,[],[f12])).
% 43.22/6.00  
% 43.22/6.00  fof(f24,plain,(
% 43.22/6.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 43.22/6.00    introduced(choice_axiom,[])).
% 43.22/6.00  
% 43.22/6.00  fof(f25,plain,(
% 43.22/6.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 43.22/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f24])).
% 43.22/6.00  
% 43.22/6.00  fof(f35,plain,(
% 43.22/6.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f25])).
% 43.22/6.00  
% 43.22/6.00  fof(f36,plain,(
% 43.22/6.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f25])).
% 43.22/6.00  
% 43.22/6.00  fof(f1,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f19,plain,(
% 43.22/6.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 43.22/6.00    inference(nnf_transformation,[],[f1])).
% 43.22/6.00  
% 43.22/6.00  fof(f20,plain,(
% 43.22/6.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 43.22/6.00    inference(flattening,[],[f19])).
% 43.22/6.00  
% 43.22/6.00  fof(f21,plain,(
% 43.22/6.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 43.22/6.00    inference(rectify,[],[f20])).
% 43.22/6.00  
% 43.22/6.00  fof(f22,plain,(
% 43.22/6.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 43.22/6.00    introduced(choice_axiom,[])).
% 43.22/6.00  
% 43.22/6.00  fof(f23,plain,(
% 43.22/6.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 43.22/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 43.22/6.00  
% 43.22/6.00  fof(f30,plain,(
% 43.22/6.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 43.22/6.00    inference(cnf_transformation,[],[f23])).
% 43.22/6.00  
% 43.22/6.00  fof(f53,plain,(
% 43.22/6.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 43.22/6.00    inference(equality_resolution,[],[f30])).
% 43.22/6.00  
% 43.22/6.00  fof(f4,axiom,(
% 43.22/6.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f14,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 43.22/6.00    inference(ennf_transformation,[],[f4])).
% 43.22/6.00  
% 43.22/6.00  fof(f15,plain,(
% 43.22/6.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 43.22/6.00    inference(flattening,[],[f14])).
% 43.22/6.00  
% 43.22/6.00  fof(f39,plain,(
% 43.22/6.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f15])).
% 43.22/6.00  
% 43.22/6.00  fof(f10,conjecture,(
% 43.22/6.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f11,negated_conjecture,(
% 43.22/6.00    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 43.22/6.00    inference(negated_conjecture,[],[f10])).
% 43.22/6.00  
% 43.22/6.00  fof(f17,plain,(
% 43.22/6.00    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 43.22/6.00    inference(ennf_transformation,[],[f11])).
% 43.22/6.00  
% 43.22/6.00  fof(f18,plain,(
% 43.22/6.00    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 43.22/6.00    inference(flattening,[],[f17])).
% 43.22/6.00  
% 43.22/6.00  fof(f27,plain,(
% 43.22/6.00    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 & r1_tarski(sK2,k1_relat_1(sK3)) & v1_relat_1(sK3))),
% 43.22/6.00    introduced(choice_axiom,[])).
% 43.22/6.00  
% 43.22/6.00  fof(f28,plain,(
% 43.22/6.00    k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 & r1_tarski(sK2,k1_relat_1(sK3)) & v1_relat_1(sK3)),
% 43.22/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f27])).
% 43.22/6.00  
% 43.22/6.00  fof(f47,plain,(
% 43.22/6.00    r1_tarski(sK2,k1_relat_1(sK3))),
% 43.22/6.00    inference(cnf_transformation,[],[f28])).
% 43.22/6.00  
% 43.22/6.00  fof(f5,axiom,(
% 43.22/6.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f26,plain,(
% 43.22/6.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 43.22/6.00    inference(nnf_transformation,[],[f5])).
% 43.22/6.00  
% 43.22/6.00  fof(f40,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f26])).
% 43.22/6.00  
% 43.22/6.00  fof(f8,axiom,(
% 43.22/6.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f44,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 43.22/6.00    inference(cnf_transformation,[],[f8])).
% 43.22/6.00  
% 43.22/6.00  fof(f3,axiom,(
% 43.22/6.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f38,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f3])).
% 43.22/6.00  
% 43.22/6.00  fof(f7,axiom,(
% 43.22/6.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f43,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f7])).
% 43.22/6.00  
% 43.22/6.00  fof(f50,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 43.22/6.00    inference(definition_unfolding,[],[f44,f38,f43])).
% 43.22/6.00  
% 43.22/6.00  fof(f6,axiom,(
% 43.22/6.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f42,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f6])).
% 43.22/6.00  
% 43.22/6.00  fof(f49,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 43.22/6.00    inference(definition_unfolding,[],[f42,f43,f43])).
% 43.22/6.00  
% 43.22/6.00  fof(f9,axiom,(
% 43.22/6.00    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 43.22/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.22/6.00  
% 43.22/6.00  fof(f16,plain,(
% 43.22/6.00    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 43.22/6.00    inference(ennf_transformation,[],[f9])).
% 43.22/6.00  
% 43.22/6.00  fof(f45,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 43.22/6.00    inference(cnf_transformation,[],[f16])).
% 43.22/6.00  
% 43.22/6.00  fof(f51,plain,(
% 43.22/6.00    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 43.22/6.00    inference(definition_unfolding,[],[f45,f38])).
% 43.22/6.00  
% 43.22/6.00  fof(f46,plain,(
% 43.22/6.00    v1_relat_1(sK3)),
% 43.22/6.00    inference(cnf_transformation,[],[f28])).
% 43.22/6.00  
% 43.22/6.00  fof(f48,plain,(
% 43.22/6.00    k1_relat_1(k7_relat_1(sK3,sK2)) != sK2),
% 43.22/6.00    inference(cnf_transformation,[],[f28])).
% 43.22/6.00  
% 43.22/6.00  cnf(c_8,plain,
% 43.22/6.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 43.22/6.00      inference(cnf_transformation,[],[f35]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1726,plain,
% 43.22/6.00      ( r1_xboole_0(X0,X1) = iProver_top
% 43.22/6.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_7,plain,
% 43.22/6.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 43.22/6.00      inference(cnf_transformation,[],[f36]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1727,plain,
% 43.22/6.00      ( r1_xboole_0(X0,X1) = iProver_top
% 43.22/6.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_4,negated_conjecture,
% 43.22/6.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 43.22/6.00      inference(cnf_transformation,[],[f53]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1730,plain,
% 43.22/6.00      ( r2_hidden(X0,X1) != iProver_top
% 43.22/6.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2275,plain,
% 43.22/6.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 43.22/6.00      | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_1727,c_1730]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2640,plain,
% 43.22/6.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_1726,c_2275]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_9,plain,
% 43.22/6.00      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 43.22/6.00      inference(cnf_transformation,[],[f39]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_16,negated_conjecture,
% 43.22/6.00      ( r1_tarski(sK2,k1_relat_1(sK3)) ),
% 43.22/6.00      inference(cnf_transformation,[],[f47]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_217,plain,
% 43.22/6.00      ( ~ r1_xboole_0(X0,X1)
% 43.22/6.00      | r1_xboole_0(X2,X1)
% 43.22/6.00      | k1_relat_1(sK3) != X0
% 43.22/6.00      | sK2 != X2 ),
% 43.22/6.00      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_218,plain,
% 43.22/6.00      ( ~ r1_xboole_0(k1_relat_1(sK3),X0) | r1_xboole_0(sK2,X0) ),
% 43.22/6.00      inference(unflattening,[status(thm)],[c_217]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1722,plain,
% 43.22/6.00      ( r1_xboole_0(k1_relat_1(sK3),X0) != iProver_top
% 43.22/6.00      | r1_xboole_0(sK2,X0) = iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2932,plain,
% 43.22/6.00      ( r1_xboole_0(sK2,k4_xboole_0(X0,k1_relat_1(sK3))) = iProver_top ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_2640,c_1722]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_11,plain,
% 43.22/6.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 43.22/6.00      inference(cnf_transformation,[],[f40]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1724,plain,
% 43.22/6.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 43.22/6.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_3451,plain,
% 43.22/6.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,k1_relat_1(sK3))) = sK2 ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_2932,c_1724]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_13,plain,
% 43.22/6.00      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 43.22/6.00      inference(cnf_transformation,[],[f50]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_190400,plain,
% 43.22/6.00      ( k1_setfam_1(k1_enumset1(sK2,sK2,k1_relat_1(sK3))) = sK2 ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_3451,c_13]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_12,plain,
% 43.22/6.00      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 43.22/6.00      inference(cnf_transformation,[],[f49]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_14,plain,
% 43.22/6.00      ( ~ v1_relat_1(X0)
% 43.22/6.00      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 43.22/6.00      inference(cnf_transformation,[],[f51]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_17,negated_conjecture,
% 43.22/6.00      ( v1_relat_1(sK3) ),
% 43.22/6.00      inference(cnf_transformation,[],[f46]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_210,plain,
% 43.22/6.00      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 43.22/6.00      | sK3 != X0 ),
% 43.22/6.00      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_211,plain,
% 43.22/6.00      ( k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 43.22/6.00      inference(unflattening,[status(thm)],[c_210]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_1961,plain,
% 43.22/6.00      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_13,c_211]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_2020,plain,
% 43.22/6.00      ( k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK3))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_12,c_1961]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_191478,plain,
% 43.22/6.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
% 43.22/6.00      inference(superposition,[status(thm)],[c_190400,c_2020]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(c_15,negated_conjecture,
% 43.22/6.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 ),
% 43.22/6.00      inference(cnf_transformation,[],[f48]) ).
% 43.22/6.00  
% 43.22/6.00  cnf(contradiction,plain,
% 43.22/6.00      ( $false ),
% 43.22/6.00      inference(minisat,[status(thm)],[c_191478,c_15]) ).
% 43.22/6.00  
% 43.22/6.00  
% 43.22/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.22/6.00  
% 43.22/6.00  ------                               Statistics
% 43.22/6.00  
% 43.22/6.00  ------ Selected
% 43.22/6.00  
% 43.22/6.00  total_time:                             5.13
% 43.22/6.00  
%------------------------------------------------------------------------------
