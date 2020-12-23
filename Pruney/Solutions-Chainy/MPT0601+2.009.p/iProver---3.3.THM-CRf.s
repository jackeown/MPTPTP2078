%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:20 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 294 expanded)
%              Number of clauses        :   34 (  89 expanded)
%              Number of leaves         :   11 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :  203 ( 887 expanded)
%              Number of equality atoms :   80 ( 282 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f27,f30,f29,f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0] : r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK8,sK7)
        | ~ r2_hidden(sK7,k1_relat_1(sK8)) )
      & ( k1_xboole_0 != k11_relat_1(sK8,sK7)
        | r2_hidden(sK7,k1_relat_1(sK8)) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK8,sK7)
      | ~ r2_hidden(sK7,k1_relat_1(sK8)) )
    & ( k1_xboole_0 != k11_relat_1(sK8,sK7)
      | r2_hidden(sK7,k1_relat_1(sK8)) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f38,f39])).

fof(f63,plain,
    ( k1_xboole_0 = k11_relat_1(sK8,sK7)
    | ~ r2_hidden(sK7,k1_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,
    ( o_0_0_xboole_0 = k11_relat_1(sK8,sK7)
    | ~ r2_hidden(sK7,k1_relat_1(sK8)) ),
    inference(definition_unfolding,[],[f63,f41])).

fof(f61,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,
    ( k1_xboole_0 != k11_relat_1(sK8,sK7)
    | r2_hidden(sK7,k1_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,
    ( o_0_0_xboole_0 != k11_relat_1(sK8,sK7)
    | r2_hidden(sK7,k1_relat_1(sK8)) ),
    inference(definition_unfolding,[],[f62,f41])).

cnf(c_7,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3321,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_enumset1(X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_273,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_enumset1(X0,X0,X2) != X3
    | o_0_0_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_274,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_3306,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_3906,plain,
    ( k1_relat_1(o_0_0_xboole_0) = X0
    | r2_hidden(sK3(o_0_0_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_3306])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3313,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4056,plain,
    ( k11_relat_1(X0,X1) = k1_relat_1(o_0_0_xboole_0)
    | r2_hidden(k4_tarski(X1,sK3(o_0_0_xboole_0,k11_relat_1(X0,X1))),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3906,c_3313])).

cnf(c_4057,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_3906,c_3306])).

cnf(c_4118,plain,
    ( k11_relat_1(X0,X1) = o_0_0_xboole_0
    | r2_hidden(k4_tarski(X1,sK3(o_0_0_xboole_0,k11_relat_1(X0,X1))),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4056,c_4057])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3320,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5303,plain,
    ( k11_relat_1(X0,X1) = o_0_0_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4118,c_3320])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK7,k1_relat_1(sK8))
    | o_0_0_xboole_0 = k11_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3311,plain,
    ( o_0_0_xboole_0 = k11_relat_1(sK8,sK7)
    | r2_hidden(sK7,k1_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11102,plain,
    ( k11_relat_1(sK8,sK7) = o_0_0_xboole_0
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5303,c_3311])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11256,plain,
    ( k11_relat_1(sK8,sK7) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11102,c_20])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3319,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3312,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3549,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1,X0),k11_relat_1(X1,X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3319,c_3312])).

cnf(c_11267,plain,
    ( r2_hidden(sK5(sK8,sK7),o_0_0_xboole_0) = iProver_top
    | r2_hidden(sK7,k1_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_11256,c_3549])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK7,k1_relat_1(sK8))
    | o_0_0_xboole_0 != k11_relat_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3310,plain,
    ( o_0_0_xboole_0 != k11_relat_1(sK8,sK7)
    | r2_hidden(sK7,k1_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11260,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | r2_hidden(sK7,k1_relat_1(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11256,c_3310])).

cnf(c_11261,plain,
    ( r2_hidden(sK7,k1_relat_1(sK8)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11260])).

cnf(c_11628,plain,
    ( r2_hidden(sK5(sK8,sK7),o_0_0_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11267,c_20,c_11261])).

cnf(c_11633,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11628,c_3306])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:42:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.91/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/0.99  
% 3.91/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.91/0.99  
% 3.91/0.99  ------  iProver source info
% 3.91/0.99  
% 3.91/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.91/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.91/0.99  git: non_committed_changes: false
% 3.91/0.99  git: last_make_outside_of_git: false
% 3.91/0.99  
% 3.91/0.99  ------ 
% 3.91/0.99  ------ Parsing...
% 3.91/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.91/0.99  ------ Proving...
% 3.91/0.99  ------ Problem Properties 
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  clauses                                 19
% 3.91/0.99  conjectures                             3
% 3.91/0.99  EPR                                     2
% 3.91/0.99  Horn                                    17
% 3.91/0.99  unary                                   2
% 3.91/0.99  binary                                  8
% 3.91/0.99  lits                                    47
% 3.91/0.99  lits eq                                 8
% 3.91/0.99  fd_pure                                 0
% 3.91/0.99  fd_pseudo                               0
% 3.91/0.99  fd_cond                                 0
% 3.91/0.99  fd_pseudo_cond                          2
% 3.91/0.99  AC symbols                              0
% 3.91/0.99  
% 3.91/0.99  ------ Input Options Time Limit: Unbounded
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.91/0.99  Current options:
% 3.91/0.99  ------ 
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  ------ Proving...
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.91/0.99  
% 3.91/0.99  ------ Proving...
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.91/0.99  
% 3.91/0.99  ------ Proving...
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.91/0.99  
% 3.91/0.99  ------ Proving...
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.91/0.99  
% 3.91/0.99  ------ Proving...
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.91/0.99  
% 3.91/0.99  ------ Proving...
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  % SZS status Theorem for theBenchmark.p
% 3.91/0.99  
% 3.91/0.99   Resolution empty clause
% 3.91/0.99  
% 3.91/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.91/0.99  
% 3.91/0.99  fof(f8,axiom,(
% 3.91/0.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f26,plain,(
% 3.91/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.91/0.99    inference(nnf_transformation,[],[f8])).
% 3.91/0.99  
% 3.91/0.99  fof(f27,plain,(
% 3.91/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.91/0.99    inference(rectify,[],[f26])).
% 3.91/0.99  
% 3.91/0.99  fof(f30,plain,(
% 3.91/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 3.91/0.99    introduced(choice_axiom,[])).
% 3.91/0.99  
% 3.91/0.99  fof(f29,plain,(
% 3.91/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0))) )),
% 3.91/0.99    introduced(choice_axiom,[])).
% 3.91/0.99  
% 3.91/0.99  fof(f28,plain,(
% 3.91/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.91/0.99    introduced(choice_axiom,[])).
% 3.91/0.99  
% 3.91/0.99  fof(f31,plain,(
% 3.91/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.91/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f27,f30,f29,f28])).
% 3.91/0.99  
% 3.91/0.99  fof(f52,plain,(
% 3.91/0.99    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f2,axiom,(
% 3.91/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f42,plain,(
% 3.91/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f2])).
% 3.91/0.99  
% 3.91/0.99  fof(f1,axiom,(
% 3.91/0.99    k1_xboole_0 = o_0_0_xboole_0),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f41,plain,(
% 3.91/0.99    k1_xboole_0 = o_0_0_xboole_0),
% 3.91/0.99    inference(cnf_transformation,[],[f1])).
% 3.91/0.99  
% 3.91/0.99  fof(f65,plain,(
% 3.91/0.99    ( ! [X0] : (r1_xboole_0(X0,o_0_0_xboole_0)) )),
% 3.91/0.99    inference(definition_unfolding,[],[f42,f41])).
% 3.91/0.99  
% 3.91/0.99  fof(f5,axiom,(
% 3.91/0.99    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f14,plain,(
% 3.91/0.99    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.91/0.99    inference(ennf_transformation,[],[f5])).
% 3.91/0.99  
% 3.91/0.99  fof(f45,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f14])).
% 3.91/0.99  
% 3.91/0.99  fof(f4,axiom,(
% 3.91/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f44,plain,(
% 3.91/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f4])).
% 3.91/0.99  
% 3.91/0.99  fof(f66,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k1_enumset1(X0,X0,X1),X2)) )),
% 3.91/0.99    inference(definition_unfolding,[],[f45,f44])).
% 3.91/0.99  
% 3.91/0.99  fof(f11,axiom,(
% 3.91/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f19,plain,(
% 3.91/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 3.91/0.99    inference(ennf_transformation,[],[f11])).
% 3.91/0.99  
% 3.91/0.99  fof(f36,plain,(
% 3.91/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 3.91/0.99    inference(nnf_transformation,[],[f19])).
% 3.91/0.99  
% 3.91/0.99  fof(f60,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f36])).
% 3.91/0.99  
% 3.91/0.99  fof(f51,plain,(
% 3.91/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 3.91/0.99    inference(cnf_transformation,[],[f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f70,plain,(
% 3.91/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 3.91/0.99    inference(equality_resolution,[],[f51])).
% 3.91/0.99  
% 3.91/0.99  fof(f12,conjecture,(
% 3.91/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f13,negated_conjecture,(
% 3.91/0.99    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 3.91/0.99    inference(negated_conjecture,[],[f12])).
% 3.91/0.99  
% 3.91/0.99  fof(f20,plain,(
% 3.91/0.99    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.91/0.99    inference(ennf_transformation,[],[f13])).
% 3.91/0.99  
% 3.91/0.99  fof(f37,plain,(
% 3.91/0.99    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 3.91/0.99    inference(nnf_transformation,[],[f20])).
% 3.91/0.99  
% 3.91/0.99  fof(f38,plain,(
% 3.91/0.99    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 3.91/0.99    inference(flattening,[],[f37])).
% 3.91/0.99  
% 3.91/0.99  fof(f39,plain,(
% 3.91/0.99    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK8,sK7) | ~r2_hidden(sK7,k1_relat_1(sK8))) & (k1_xboole_0 != k11_relat_1(sK8,sK7) | r2_hidden(sK7,k1_relat_1(sK8))) & v1_relat_1(sK8))),
% 3.91/0.99    introduced(choice_axiom,[])).
% 3.91/0.99  
% 3.91/0.99  fof(f40,plain,(
% 3.91/0.99    (k1_xboole_0 = k11_relat_1(sK8,sK7) | ~r2_hidden(sK7,k1_relat_1(sK8))) & (k1_xboole_0 != k11_relat_1(sK8,sK7) | r2_hidden(sK7,k1_relat_1(sK8))) & v1_relat_1(sK8)),
% 3.91/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f38,f39])).
% 3.91/0.99  
% 3.91/0.99  fof(f63,plain,(
% 3.91/0.99    k1_xboole_0 = k11_relat_1(sK8,sK7) | ~r2_hidden(sK7,k1_relat_1(sK8))),
% 3.91/0.99    inference(cnf_transformation,[],[f40])).
% 3.91/0.99  
% 3.91/0.99  fof(f68,plain,(
% 3.91/0.99    o_0_0_xboole_0 = k11_relat_1(sK8,sK7) | ~r2_hidden(sK7,k1_relat_1(sK8))),
% 3.91/0.99    inference(definition_unfolding,[],[f63,f41])).
% 3.91/0.99  
% 3.91/0.99  fof(f61,plain,(
% 3.91/0.99    v1_relat_1(sK8)),
% 3.91/0.99    inference(cnf_transformation,[],[f40])).
% 3.91/0.99  
% 3.91/0.99  fof(f50,plain,(
% 3.91/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.91/0.99    inference(cnf_transformation,[],[f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f71,plain,(
% 3.91/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.91/0.99    inference(equality_resolution,[],[f50])).
% 3.91/0.99  
% 3.91/0.99  fof(f59,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f36])).
% 3.91/0.99  
% 3.91/0.99  fof(f62,plain,(
% 3.91/0.99    k1_xboole_0 != k11_relat_1(sK8,sK7) | r2_hidden(sK7,k1_relat_1(sK8))),
% 3.91/0.99    inference(cnf_transformation,[],[f40])).
% 3.91/0.99  
% 3.91/0.99  fof(f69,plain,(
% 3.91/0.99    o_0_0_xboole_0 != k11_relat_1(sK8,sK7) | r2_hidden(sK7,k1_relat_1(sK8))),
% 3.91/0.99    inference(definition_unfolding,[],[f62,f41])).
% 3.91/0.99  
% 3.91/0.99  cnf(c_7,plain,
% 3.91/0.99      ( r2_hidden(sK3(X0,X1),X1)
% 3.91/0.99      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
% 3.91/0.99      | k1_relat_1(X0) = X1 ),
% 3.91/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3321,plain,
% 3.91/0.99      ( k1_relat_1(X0) = X1
% 3.91/0.99      | r2_hidden(sK3(X0,X1),X1) = iProver_top
% 3.91/0.99      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_0,plain,
% 3.91/0.99      ( r1_xboole_0(X0,o_0_0_xboole_0) ),
% 3.91/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1,negated_conjecture,
% 3.91/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k1_enumset1(X0,X0,X2),X1) ),
% 3.91/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_273,plain,
% 3.91/0.99      ( ~ r2_hidden(X0,X1)
% 3.91/0.99      | k1_enumset1(X0,X0,X2) != X3
% 3.91/0.99      | o_0_0_xboole_0 != X1 ),
% 3.91/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_274,plain,
% 3.91/0.99      ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
% 3.91/0.99      inference(unflattening,[status(thm)],[c_273]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3306,plain,
% 3.91/0.99      ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3906,plain,
% 3.91/0.99      ( k1_relat_1(o_0_0_xboole_0) = X0
% 3.91/0.99      | r2_hidden(sK3(o_0_0_xboole_0,X0),X0) = iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_3321,c_3306]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_15,plain,
% 3.91/0.99      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 3.91/0.99      | r2_hidden(k4_tarski(X2,X0),X1)
% 3.91/0.99      | ~ v1_relat_1(X1) ),
% 3.91/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3313,plain,
% 3.91/0.99      ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
% 3.91/0.99      | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
% 3.91/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_4056,plain,
% 3.91/0.99      ( k11_relat_1(X0,X1) = k1_relat_1(o_0_0_xboole_0)
% 3.91/0.99      | r2_hidden(k4_tarski(X1,sK3(o_0_0_xboole_0,k11_relat_1(X0,X1))),X0) = iProver_top
% 3.91/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_3906,c_3313]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_4057,plain,
% 3.91/0.99      ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_3906,c_3306]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_4118,plain,
% 3.91/0.99      ( k11_relat_1(X0,X1) = o_0_0_xboole_0
% 3.91/0.99      | r2_hidden(k4_tarski(X1,sK3(o_0_0_xboole_0,k11_relat_1(X0,X1))),X0) = iProver_top
% 3.91/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.91/0.99      inference(light_normalisation,[status(thm)],[c_4056,c_4057]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_8,plain,
% 3.91/0.99      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 3.91/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3320,plain,
% 3.91/0.99      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.91/0.99      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_5303,plain,
% 3.91/0.99      ( k11_relat_1(X0,X1) = o_0_0_xboole_0
% 3.91/0.99      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 3.91/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_4118,c_3320]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_17,negated_conjecture,
% 3.91/0.99      ( ~ r2_hidden(sK7,k1_relat_1(sK8))
% 3.91/0.99      | o_0_0_xboole_0 = k11_relat_1(sK8,sK7) ),
% 3.91/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3311,plain,
% 3.91/0.99      ( o_0_0_xboole_0 = k11_relat_1(sK8,sK7)
% 3.91/0.99      | r2_hidden(sK7,k1_relat_1(sK8)) != iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11102,plain,
% 3.91/0.99      ( k11_relat_1(sK8,sK7) = o_0_0_xboole_0
% 3.91/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_5303,c_3311]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_19,negated_conjecture,
% 3.91/0.99      ( v1_relat_1(sK8) ),
% 3.91/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_20,plain,
% 3.91/0.99      ( v1_relat_1(sK8) = iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11256,plain,
% 3.91/0.99      ( k11_relat_1(sK8,sK7) = o_0_0_xboole_0 ),
% 3.91/0.99      inference(global_propositional_subsumption,[status(thm)],[c_11102,c_20]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_9,plain,
% 3.91/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.91/0.99      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
% 3.91/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3319,plain,
% 3.91/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.91/0.99      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_16,plain,
% 3.91/0.99      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 3.91/0.99      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.91/0.99      | ~ v1_relat_1(X1) ),
% 3.91/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3312,plain,
% 3.91/0.99      ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
% 3.91/0.99      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 3.91/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3549,plain,
% 3.91/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.91/0.99      | r2_hidden(sK5(X1,X0),k11_relat_1(X1,X0)) = iProver_top
% 3.91/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_3319,c_3312]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11267,plain,
% 3.91/0.99      ( r2_hidden(sK5(sK8,sK7),o_0_0_xboole_0) = iProver_top
% 3.91/0.99      | r2_hidden(sK7,k1_relat_1(sK8)) != iProver_top
% 3.91/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_11256,c_3549]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_18,negated_conjecture,
% 3.91/0.99      ( r2_hidden(sK7,k1_relat_1(sK8))
% 3.91/0.99      | o_0_0_xboole_0 != k11_relat_1(sK8,sK7) ),
% 3.91/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3310,plain,
% 3.91/0.99      ( o_0_0_xboole_0 != k11_relat_1(sK8,sK7)
% 3.91/0.99      | r2_hidden(sK7,k1_relat_1(sK8)) = iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11260,plain,
% 3.91/0.99      ( o_0_0_xboole_0 != o_0_0_xboole_0
% 3.91/0.99      | r2_hidden(sK7,k1_relat_1(sK8)) = iProver_top ),
% 3.91/0.99      inference(demodulation,[status(thm)],[c_11256,c_3310]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11261,plain,
% 3.91/0.99      ( r2_hidden(sK7,k1_relat_1(sK8)) = iProver_top ),
% 3.91/0.99      inference(equality_resolution_simp,[status(thm)],[c_11260]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11628,plain,
% 3.91/0.99      ( r2_hidden(sK5(sK8,sK7),o_0_0_xboole_0) = iProver_top ),
% 3.91/0.99      inference(global_propositional_subsumption,
% 3.91/0.99                [status(thm)],
% 3.91/0.99                [c_11267,c_20,c_11261]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11633,plain,
% 3.91/0.99      ( $false ),
% 3.91/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_11628,c_3306]) ).
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.91/0.99  
% 3.91/0.99  ------                               Statistics
% 3.91/0.99  
% 3.91/0.99  ------ Selected
% 3.91/0.99  
% 3.91/0.99  total_time:                             0.323
% 3.91/0.99  
%------------------------------------------------------------------------------
