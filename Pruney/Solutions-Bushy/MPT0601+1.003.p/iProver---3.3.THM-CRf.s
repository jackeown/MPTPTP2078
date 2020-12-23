%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0601+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:42 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 577 expanded)
%              Number of clauses        :   40 ( 196 expanded)
%              Number of leaves         :   11 ( 123 expanded)
%              Depth                    :   21
%              Number of atoms          :  212 (1958 expanded)
%              Number of equality atoms :   68 ( 539 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k11_relat_1(X1,X0) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k11_relat_1(X1,X0) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k11_relat_1(X1,X0) != k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k11_relat_1(X1,X0) = k1_xboole_0
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k11_relat_1(X1,X0) != k1_xboole_0
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k11_relat_1(X1,X0) = k1_xboole_0
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k11_relat_1(X1,X0) != k1_xboole_0
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( k11_relat_1(X1,X0) = k1_xboole_0
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k11_relat_1(X1,X0) != k1_xboole_0
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k11_relat_1(sK5,sK4) = k1_xboole_0
        | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
      & ( k11_relat_1(sK5,sK4) != k1_xboole_0
        | r2_hidden(sK4,k1_relat_1(sK5)) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( k11_relat_1(sK5,sK4) = k1_xboole_0
      | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
    & ( k11_relat_1(sK5,sK4) != k1_xboole_0
      | r2_hidden(sK4,k1_relat_1(sK5)) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f25])).

fof(f36,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f20,f19,f18])).

fof(f30,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f38,plain,
    ( k11_relat_1(sK5,sK4) = k1_xboole_0
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,
    ( k11_relat_1(sK5,sK4) != k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_172,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_1,c_8])).

cnf(c_597,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_172])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_198,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_199,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_258,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK5)
    | ~ r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_199])).

cnf(c_259,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_595,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_1017,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | r2_hidden(k4_tarski(X0,sK0(k11_relat_1(sK5,X0))),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_597,c_595])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_601,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1726,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1017,c_601])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(sK4,k1_relat_1(sK5))
    | k11_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_599,plain,
    ( k11_relat_1(sK5,sK4) = k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1851,plain,
    ( k11_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1726,c_599])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_600,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_186,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_187,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_260,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK5)
    | r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_187])).

cnf(c_261,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_596,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_845,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X0),k11_relat_1(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_600,c_596])).

cnf(c_1890,plain,
    ( r2_hidden(sK3(sK5,sK4),k1_xboole_0) = iProver_top
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1851,c_845])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK4,k1_relat_1(sK5))
    | k11_relat_1(sK5,sK4) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,plain,
    ( k11_relat_1(sK5,sK4) != k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2166,plain,
    ( r2_hidden(sK3(sK5,sK4),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1890,c_13,c_1851])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_604,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1848,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | r2_hidden(k1_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_604])).

cnf(c_2371,plain,
    ( k11_relat_1(sK5,k1_relat_1(sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1726,c_1848])).

cnf(c_2598,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(k1_relat_1(sK5),X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_595])).

cnf(c_2759,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2598,c_601])).

cnf(c_2801,plain,
    ( r2_hidden(k1_relat_1(sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_2759])).

cnf(c_2809,plain,
    ( r2_hidden(k1_relat_1(sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_604])).

cnf(c_2812,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2809,c_2801])).


%------------------------------------------------------------------------------
