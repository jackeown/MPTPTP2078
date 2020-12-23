%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:31 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  119 (1228 expanded)
%              Number of clauses        :   64 ( 444 expanded)
%              Number of leaves         :   21 ( 290 expanded)
%              Depth                    :   21
%              Number of atoms          :  352 (4426 expanded)
%              Number of equality atoms :  169 (2016 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f13,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
        & k1_relat_1(sK5(X0,X1)) = X0
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
          & k1_relat_1(sK5(X0,X1)) = X0
          & v1_funct_1(sK5(X0,X1))
          & v1_relat_1(sK5(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k2_relat_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f48])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK5(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK6)
          | k1_relat_1(X2) != sK7
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK7
        | k1_xboole_0 != sK6 ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK6)
        | k1_relat_1(X2) != sK7
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 != sK6 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f38])).

fof(f66,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK6)
      | k1_relat_1(X2) != sK7
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

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
    inference(rectify,[],[f2])).

fof(f17,plain,(
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

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r2_hidden(sK2(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1547,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1552,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_20,plain,
    ( k2_relat_1(sK5(X0,X1)) = k2_tarski(X1,X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_21,plain,
    ( k1_relat_1(sK5(X0,X1)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK6)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK7 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,plain,
    ( v1_relat_1(sK5(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_723,plain,
    ( ~ r1_tarski(k2_relat_1(X0),sK6)
    | ~ v1_funct_1(X0)
    | sK5(X1,X2) != X0
    | k1_relat_1(X0) != sK7
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_23])).

cnf(c_724,plain,
    ( ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK6)
    | ~ v1_funct_1(sK5(X0,X1))
    | k1_relat_1(sK5(X0,X1)) != sK7
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_319,plain,
    ( ~ r1_tarski(k2_relat_1(X0),sK6)
    | ~ v1_funct_1(X0)
    | sK5(X1,X2) != X0
    | k1_relat_1(X0) != sK7
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_23])).

cnf(c_320,plain,
    ( ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK6)
    | ~ v1_funct_1(sK5(X0,X1))
    | k1_relat_1(sK5(X0,X1)) != sK7
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_22,plain,
    ( v1_funct_1(sK5(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_324,plain,
    ( ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK6)
    | k1_relat_1(sK5(X0,X1)) != sK7
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_22])).

cnf(c_726,plain,
    ( ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK6)
    | k1_relat_1(sK5(X0,X1)) != sK7
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_22,c_320])).

cnf(c_1544,plain,
    ( k1_relat_1(sK5(X0,X1)) != sK7
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_1839,plain,
    ( sK7 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1544])).

cnf(c_1997,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1839])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_308,plain,
    ( v1_relat_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_309,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_740,plain,
    ( ~ r1_tarski(k2_relat_1(X0),sK6)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) != sK7
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_309])).

cnf(c_741,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK6)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK7 ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_19,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_49,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_409,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) != sK7
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_410,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) != sK7 ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_412,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != sK7 ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_743,plain,
    ( k1_relat_1(k1_xboole_0) != sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_38,c_17,c_49,c_0,c_412])).

cnf(c_18,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1563,plain,
    ( sK7 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_743,c_18])).

cnf(c_2037,plain,
    ( r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1997,c_1563])).

cnf(c_2044,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k2_tarski(X0,X0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2037])).

cnf(c_2049,plain,
    ( r1_tarski(k2_tarski(X0,X0),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2044,c_1563])).

cnf(c_2351,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_2049])).

cnf(c_3112,plain,
    ( k1_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_2351])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1558,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3433,plain,
    ( k1_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),X1) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3112,c_1558])).

cnf(c_3436,plain,
    ( k1_relat_1(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_3112,c_2351])).

cnf(c_3500,plain,
    ( sK6 = X0
    | r2_hidden(sK2(sK6,X0),X1) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3433,c_3436])).

cnf(c_3511,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3500])).

cnf(c_3443,plain,
    ( sK6 = X0
    | r2_hidden(sK2(sK6,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3436,c_3112])).

cnf(c_3452,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3443])).

cnf(c_1150,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1744,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_2022,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_2023,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_1149,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1927,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_1692,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_1693,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_1164,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_5,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_69,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_66,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_68,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3511,c_3452,c_2023,c_1927,c_1693,c_1563,c_1164,c_69,c_68,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:49:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.06/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.06/0.99  
% 2.06/0.99  ------  iProver source info
% 2.06/0.99  
% 2.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.06/0.99  git: non_committed_changes: false
% 2.06/0.99  git: last_make_outside_of_git: false
% 2.06/0.99  
% 2.06/0.99  ------ 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options
% 2.06/0.99  
% 2.06/0.99  --out_options                           all
% 2.06/0.99  --tptp_safe_out                         true
% 2.06/0.99  --problem_path                          ""
% 2.06/0.99  --include_path                          ""
% 2.06/0.99  --clausifier                            res/vclausify_rel
% 2.06/0.99  --clausifier_options                    --mode clausify
% 2.06/0.99  --stdin                                 false
% 2.06/0.99  --stats_out                             all
% 2.06/0.99  
% 2.06/0.99  ------ General Options
% 2.06/0.99  
% 2.06/0.99  --fof                                   false
% 2.06/0.99  --time_out_real                         305.
% 2.06/0.99  --time_out_virtual                      -1.
% 2.06/0.99  --symbol_type_check                     false
% 2.06/0.99  --clausify_out                          false
% 2.06/0.99  --sig_cnt_out                           false
% 2.06/0.99  --trig_cnt_out                          false
% 2.06/0.99  --trig_cnt_out_tolerance                1.
% 2.06/0.99  --trig_cnt_out_sk_spl                   false
% 2.06/0.99  --abstr_cl_out                          false
% 2.06/0.99  
% 2.06/0.99  ------ Global Options
% 2.06/0.99  
% 2.06/0.99  --schedule                              default
% 2.06/0.99  --add_important_lit                     false
% 2.06/0.99  --prop_solver_per_cl                    1000
% 2.06/0.99  --min_unsat_core                        false
% 2.06/0.99  --soft_assumptions                      false
% 2.06/0.99  --soft_lemma_size                       3
% 2.06/0.99  --prop_impl_unit_size                   0
% 2.06/0.99  --prop_impl_unit                        []
% 2.06/0.99  --share_sel_clauses                     true
% 2.06/0.99  --reset_solvers                         false
% 2.06/0.99  --bc_imp_inh                            [conj_cone]
% 2.06/0.99  --conj_cone_tolerance                   3.
% 2.06/0.99  --extra_neg_conj                        none
% 2.06/0.99  --large_theory_mode                     true
% 2.06/0.99  --prolific_symb_bound                   200
% 2.06/0.99  --lt_threshold                          2000
% 2.06/0.99  --clause_weak_htbl                      true
% 2.06/0.99  --gc_record_bc_elim                     false
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing Options
% 2.06/0.99  
% 2.06/0.99  --preprocessing_flag                    true
% 2.06/0.99  --time_out_prep_mult                    0.1
% 2.06/0.99  --splitting_mode                        input
% 2.06/0.99  --splitting_grd                         true
% 2.06/0.99  --splitting_cvd                         false
% 2.06/0.99  --splitting_cvd_svl                     false
% 2.06/0.99  --splitting_nvd                         32
% 2.06/0.99  --sub_typing                            true
% 2.06/0.99  --prep_gs_sim                           true
% 2.06/0.99  --prep_unflatten                        true
% 2.06/0.99  --prep_res_sim                          true
% 2.06/0.99  --prep_upred                            true
% 2.06/0.99  --prep_sem_filter                       exhaustive
% 2.06/0.99  --prep_sem_filter_out                   false
% 2.06/0.99  --pred_elim                             true
% 2.06/0.99  --res_sim_input                         true
% 2.06/0.99  --eq_ax_congr_red                       true
% 2.06/0.99  --pure_diseq_elim                       true
% 2.06/0.99  --brand_transform                       false
% 2.06/0.99  --non_eq_to_eq                          false
% 2.06/0.99  --prep_def_merge                        true
% 2.06/0.99  --prep_def_merge_prop_impl              false
% 2.06/0.99  --prep_def_merge_mbd                    true
% 2.06/0.99  --prep_def_merge_tr_red                 false
% 2.06/0.99  --prep_def_merge_tr_cl                  false
% 2.06/0.99  --smt_preprocessing                     true
% 2.06/0.99  --smt_ac_axioms                         fast
% 2.06/0.99  --preprocessed_out                      false
% 2.06/0.99  --preprocessed_stats                    false
% 2.06/0.99  
% 2.06/0.99  ------ Abstraction refinement Options
% 2.06/0.99  
% 2.06/0.99  --abstr_ref                             []
% 2.06/0.99  --abstr_ref_prep                        false
% 2.06/0.99  --abstr_ref_until_sat                   false
% 2.06/0.99  --abstr_ref_sig_restrict                funpre
% 2.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.99  --abstr_ref_under                       []
% 2.06/0.99  
% 2.06/0.99  ------ SAT Options
% 2.06/0.99  
% 2.06/0.99  --sat_mode                              false
% 2.06/0.99  --sat_fm_restart_options                ""
% 2.06/0.99  --sat_gr_def                            false
% 2.06/0.99  --sat_epr_types                         true
% 2.06/0.99  --sat_non_cyclic_types                  false
% 2.06/0.99  --sat_finite_models                     false
% 2.06/0.99  --sat_fm_lemmas                         false
% 2.06/0.99  --sat_fm_prep                           false
% 2.06/0.99  --sat_fm_uc_incr                        true
% 2.06/0.99  --sat_out_model                         small
% 2.06/0.99  --sat_out_clauses                       false
% 2.06/0.99  
% 2.06/0.99  ------ QBF Options
% 2.06/0.99  
% 2.06/0.99  --qbf_mode                              false
% 2.06/0.99  --qbf_elim_univ                         false
% 2.06/0.99  --qbf_dom_inst                          none
% 2.06/0.99  --qbf_dom_pre_inst                      false
% 2.06/0.99  --qbf_sk_in                             false
% 2.06/0.99  --qbf_pred_elim                         true
% 2.06/0.99  --qbf_split                             512
% 2.06/0.99  
% 2.06/0.99  ------ BMC1 Options
% 2.06/0.99  
% 2.06/0.99  --bmc1_incremental                      false
% 2.06/0.99  --bmc1_axioms                           reachable_all
% 2.06/0.99  --bmc1_min_bound                        0
% 2.06/0.99  --bmc1_max_bound                        -1
% 2.06/0.99  --bmc1_max_bound_default                -1
% 2.06/0.99  --bmc1_symbol_reachability              true
% 2.06/0.99  --bmc1_property_lemmas                  false
% 2.06/0.99  --bmc1_k_induction                      false
% 2.06/0.99  --bmc1_non_equiv_states                 false
% 2.06/0.99  --bmc1_deadlock                         false
% 2.06/0.99  --bmc1_ucm                              false
% 2.06/0.99  --bmc1_add_unsat_core                   none
% 2.06/0.99  --bmc1_unsat_core_children              false
% 2.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.99  --bmc1_out_stat                         full
% 2.06/0.99  --bmc1_ground_init                      false
% 2.06/0.99  --bmc1_pre_inst_next_state              false
% 2.06/0.99  --bmc1_pre_inst_state                   false
% 2.06/0.99  --bmc1_pre_inst_reach_state             false
% 2.06/0.99  --bmc1_out_unsat_core                   false
% 2.06/0.99  --bmc1_aig_witness_out                  false
% 2.06/0.99  --bmc1_verbose                          false
% 2.06/0.99  --bmc1_dump_clauses_tptp                false
% 2.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.99  --bmc1_dump_file                        -
% 2.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.99  --bmc1_ucm_extend_mode                  1
% 2.06/0.99  --bmc1_ucm_init_mode                    2
% 2.06/0.99  --bmc1_ucm_cone_mode                    none
% 2.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.99  --bmc1_ucm_relax_model                  4
% 2.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.99  --bmc1_ucm_layered_model                none
% 2.06/0.99  --bmc1_ucm_max_lemma_size               10
% 2.06/0.99  
% 2.06/0.99  ------ AIG Options
% 2.06/0.99  
% 2.06/0.99  --aig_mode                              false
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation Options
% 2.06/0.99  
% 2.06/0.99  --instantiation_flag                    true
% 2.06/0.99  --inst_sos_flag                         false
% 2.06/0.99  --inst_sos_phase                        true
% 2.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel_side                     num_symb
% 2.06/0.99  --inst_solver_per_active                1400
% 2.06/0.99  --inst_solver_calls_frac                1.
% 2.06/0.99  --inst_passive_queue_type               priority_queues
% 2.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.99  --inst_passive_queues_freq              [25;2]
% 2.06/0.99  --inst_dismatching                      true
% 2.06/0.99  --inst_eager_unprocessed_to_passive     true
% 2.06/0.99  --inst_prop_sim_given                   true
% 2.06/0.99  --inst_prop_sim_new                     false
% 2.06/0.99  --inst_subs_new                         false
% 2.06/0.99  --inst_eq_res_simp                      false
% 2.06/0.99  --inst_subs_given                       false
% 2.06/0.99  --inst_orphan_elimination               true
% 2.06/0.99  --inst_learning_loop_flag               true
% 2.06/0.99  --inst_learning_start                   3000
% 2.06/0.99  --inst_learning_factor                  2
% 2.06/0.99  --inst_start_prop_sim_after_learn       3
% 2.06/0.99  --inst_sel_renew                        solver
% 2.06/0.99  --inst_lit_activity_flag                true
% 2.06/0.99  --inst_restr_to_given                   false
% 2.06/0.99  --inst_activity_threshold               500
% 2.06/0.99  --inst_out_proof                        true
% 2.06/0.99  
% 2.06/0.99  ------ Resolution Options
% 2.06/0.99  
% 2.06/0.99  --resolution_flag                       true
% 2.06/0.99  --res_lit_sel                           adaptive
% 2.06/0.99  --res_lit_sel_side                      none
% 2.06/0.99  --res_ordering                          kbo
% 2.06/0.99  --res_to_prop_solver                    active
% 2.06/0.99  --res_prop_simpl_new                    false
% 2.06/0.99  --res_prop_simpl_given                  true
% 2.06/0.99  --res_passive_queue_type                priority_queues
% 2.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/0.99  --res_passive_queues_freq               [15;5]
% 2.06/0.99  --res_forward_subs                      full
% 2.06/0.99  --res_backward_subs                     full
% 2.06/0.99  --res_forward_subs_resolution           true
% 2.06/0.99  --res_backward_subs_resolution          true
% 2.06/0.99  --res_orphan_elimination                true
% 2.06/0.99  --res_time_limit                        2.
% 2.06/0.99  --res_out_proof                         true
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Options
% 2.06/0.99  
% 2.06/0.99  --superposition_flag                    true
% 2.06/0.99  --sup_passive_queue_type                priority_queues
% 2.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.06/0.99  --demod_completeness_check              fast
% 2.06/0.99  --demod_use_ground                      true
% 2.06/0.99  --sup_to_prop_solver                    passive
% 2.06/0.99  --sup_prop_simpl_new                    true
% 2.06/0.99  --sup_prop_simpl_given                  true
% 2.06/0.99  --sup_fun_splitting                     false
% 2.06/0.99  --sup_smt_interval                      50000
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Simplification Setup
% 2.06/0.99  
% 2.06/0.99  --sup_indices_passive                   []
% 2.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_full_bw                           [BwDemod]
% 2.06/0.99  --sup_immed_triv                        [TrivRules]
% 2.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_immed_bw_main                     []
% 2.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.00  
% 2.06/1.00  ------ Combination Options
% 2.06/1.00  
% 2.06/1.00  --comb_res_mult                         3
% 2.06/1.00  --comb_sup_mult                         2
% 2.06/1.00  --comb_inst_mult                        10
% 2.06/1.00  
% 2.06/1.00  ------ Debug Options
% 2.06/1.00  
% 2.06/1.00  --dbg_backtrace                         false
% 2.06/1.00  --dbg_dump_prop_clauses                 false
% 2.06/1.00  --dbg_dump_prop_clauses_file            -
% 2.06/1.00  --dbg_out_stat                          false
% 2.06/1.00  ------ Parsing...
% 2.06/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.06/1.00  ------ Proving...
% 2.06/1.00  ------ Problem Properties 
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  clauses                                 22
% 2.06/1.00  conjectures                             1
% 2.06/1.00  EPR                                     3
% 2.06/1.00  Horn                                    17
% 2.06/1.00  unary                                   5
% 2.06/1.00  binary                                  12
% 2.06/1.00  lits                                    44
% 2.06/1.00  lits eq                                 16
% 2.06/1.00  fd_pure                                 0
% 2.06/1.00  fd_pseudo                               0
% 2.06/1.00  fd_cond                                 2
% 2.06/1.00  fd_pseudo_cond                          2
% 2.06/1.00  AC symbols                              0
% 2.06/1.00  
% 2.06/1.00  ------ Schedule dynamic 5 is on 
% 2.06/1.00  
% 2.06/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  ------ 
% 2.06/1.00  Current options:
% 2.06/1.00  ------ 
% 2.06/1.00  
% 2.06/1.00  ------ Input Options
% 2.06/1.00  
% 2.06/1.00  --out_options                           all
% 2.06/1.00  --tptp_safe_out                         true
% 2.06/1.00  --problem_path                          ""
% 2.06/1.00  --include_path                          ""
% 2.06/1.00  --clausifier                            res/vclausify_rel
% 2.06/1.00  --clausifier_options                    --mode clausify
% 2.06/1.00  --stdin                                 false
% 2.06/1.00  --stats_out                             all
% 2.06/1.00  
% 2.06/1.00  ------ General Options
% 2.06/1.00  
% 2.06/1.00  --fof                                   false
% 2.06/1.00  --time_out_real                         305.
% 2.06/1.00  --time_out_virtual                      -1.
% 2.06/1.00  --symbol_type_check                     false
% 2.06/1.00  --clausify_out                          false
% 2.06/1.00  --sig_cnt_out                           false
% 2.06/1.00  --trig_cnt_out                          false
% 2.06/1.00  --trig_cnt_out_tolerance                1.
% 2.06/1.00  --trig_cnt_out_sk_spl                   false
% 2.06/1.00  --abstr_cl_out                          false
% 2.06/1.00  
% 2.06/1.00  ------ Global Options
% 2.06/1.00  
% 2.06/1.00  --schedule                              default
% 2.06/1.00  --add_important_lit                     false
% 2.06/1.00  --prop_solver_per_cl                    1000
% 2.06/1.00  --min_unsat_core                        false
% 2.06/1.00  --soft_assumptions                      false
% 2.06/1.00  --soft_lemma_size                       3
% 2.06/1.00  --prop_impl_unit_size                   0
% 2.06/1.00  --prop_impl_unit                        []
% 2.06/1.00  --share_sel_clauses                     true
% 2.06/1.00  --reset_solvers                         false
% 2.06/1.00  --bc_imp_inh                            [conj_cone]
% 2.06/1.00  --conj_cone_tolerance                   3.
% 2.06/1.00  --extra_neg_conj                        none
% 2.06/1.00  --large_theory_mode                     true
% 2.06/1.00  --prolific_symb_bound                   200
% 2.06/1.00  --lt_threshold                          2000
% 2.06/1.00  --clause_weak_htbl                      true
% 2.06/1.00  --gc_record_bc_elim                     false
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing Options
% 2.06/1.00  
% 2.06/1.00  --preprocessing_flag                    true
% 2.06/1.00  --time_out_prep_mult                    0.1
% 2.06/1.00  --splitting_mode                        input
% 2.06/1.00  --splitting_grd                         true
% 2.06/1.00  --splitting_cvd                         false
% 2.06/1.00  --splitting_cvd_svl                     false
% 2.06/1.00  --splitting_nvd                         32
% 2.06/1.00  --sub_typing                            true
% 2.06/1.00  --prep_gs_sim                           true
% 2.06/1.00  --prep_unflatten                        true
% 2.06/1.00  --prep_res_sim                          true
% 2.06/1.00  --prep_upred                            true
% 2.06/1.00  --prep_sem_filter                       exhaustive
% 2.06/1.00  --prep_sem_filter_out                   false
% 2.06/1.00  --pred_elim                             true
% 2.06/1.00  --res_sim_input                         true
% 2.06/1.00  --eq_ax_congr_red                       true
% 2.06/1.00  --pure_diseq_elim                       true
% 2.06/1.00  --brand_transform                       false
% 2.06/1.00  --non_eq_to_eq                          false
% 2.06/1.00  --prep_def_merge                        true
% 2.06/1.00  --prep_def_merge_prop_impl              false
% 2.06/1.00  --prep_def_merge_mbd                    true
% 2.06/1.00  --prep_def_merge_tr_red                 false
% 2.06/1.00  --prep_def_merge_tr_cl                  false
% 2.06/1.00  --smt_preprocessing                     true
% 2.06/1.00  --smt_ac_axioms                         fast
% 2.06/1.00  --preprocessed_out                      false
% 2.06/1.00  --preprocessed_stats                    false
% 2.06/1.00  
% 2.06/1.00  ------ Abstraction refinement Options
% 2.06/1.00  
% 2.06/1.00  --abstr_ref                             []
% 2.06/1.00  --abstr_ref_prep                        false
% 2.06/1.00  --abstr_ref_until_sat                   false
% 2.06/1.00  --abstr_ref_sig_restrict                funpre
% 2.06/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/1.00  --abstr_ref_under                       []
% 2.06/1.00  
% 2.06/1.00  ------ SAT Options
% 2.06/1.00  
% 2.06/1.00  --sat_mode                              false
% 2.06/1.00  --sat_fm_restart_options                ""
% 2.06/1.00  --sat_gr_def                            false
% 2.06/1.00  --sat_epr_types                         true
% 2.06/1.00  --sat_non_cyclic_types                  false
% 2.06/1.00  --sat_finite_models                     false
% 2.06/1.00  --sat_fm_lemmas                         false
% 2.06/1.00  --sat_fm_prep                           false
% 2.06/1.00  --sat_fm_uc_incr                        true
% 2.06/1.00  --sat_out_model                         small
% 2.06/1.00  --sat_out_clauses                       false
% 2.06/1.00  
% 2.06/1.00  ------ QBF Options
% 2.06/1.00  
% 2.06/1.00  --qbf_mode                              false
% 2.06/1.00  --qbf_elim_univ                         false
% 2.06/1.00  --qbf_dom_inst                          none
% 2.06/1.00  --qbf_dom_pre_inst                      false
% 2.06/1.00  --qbf_sk_in                             false
% 2.06/1.00  --qbf_pred_elim                         true
% 2.06/1.00  --qbf_split                             512
% 2.06/1.00  
% 2.06/1.00  ------ BMC1 Options
% 2.06/1.00  
% 2.06/1.00  --bmc1_incremental                      false
% 2.06/1.00  --bmc1_axioms                           reachable_all
% 2.06/1.00  --bmc1_min_bound                        0
% 2.06/1.00  --bmc1_max_bound                        -1
% 2.06/1.00  --bmc1_max_bound_default                -1
% 2.06/1.00  --bmc1_symbol_reachability              true
% 2.06/1.00  --bmc1_property_lemmas                  false
% 2.06/1.00  --bmc1_k_induction                      false
% 2.06/1.00  --bmc1_non_equiv_states                 false
% 2.06/1.00  --bmc1_deadlock                         false
% 2.06/1.00  --bmc1_ucm                              false
% 2.06/1.00  --bmc1_add_unsat_core                   none
% 2.06/1.00  --bmc1_unsat_core_children              false
% 2.06/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/1.00  --bmc1_out_stat                         full
% 2.06/1.00  --bmc1_ground_init                      false
% 2.06/1.00  --bmc1_pre_inst_next_state              false
% 2.06/1.00  --bmc1_pre_inst_state                   false
% 2.06/1.00  --bmc1_pre_inst_reach_state             false
% 2.06/1.00  --bmc1_out_unsat_core                   false
% 2.06/1.00  --bmc1_aig_witness_out                  false
% 2.06/1.00  --bmc1_verbose                          false
% 2.06/1.00  --bmc1_dump_clauses_tptp                false
% 2.06/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.06/1.00  --bmc1_dump_file                        -
% 2.06/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.06/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.06/1.00  --bmc1_ucm_extend_mode                  1
% 2.06/1.00  --bmc1_ucm_init_mode                    2
% 2.06/1.00  --bmc1_ucm_cone_mode                    none
% 2.06/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.06/1.00  --bmc1_ucm_relax_model                  4
% 2.06/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.06/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/1.00  --bmc1_ucm_layered_model                none
% 2.06/1.00  --bmc1_ucm_max_lemma_size               10
% 2.06/1.00  
% 2.06/1.00  ------ AIG Options
% 2.06/1.00  
% 2.06/1.00  --aig_mode                              false
% 2.06/1.00  
% 2.06/1.00  ------ Instantiation Options
% 2.06/1.00  
% 2.06/1.00  --instantiation_flag                    true
% 2.06/1.00  --inst_sos_flag                         false
% 2.06/1.00  --inst_sos_phase                        true
% 2.06/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/1.00  --inst_lit_sel_side                     none
% 2.06/1.00  --inst_solver_per_active                1400
% 2.06/1.00  --inst_solver_calls_frac                1.
% 2.06/1.00  --inst_passive_queue_type               priority_queues
% 2.06/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/1.00  --inst_passive_queues_freq              [25;2]
% 2.06/1.00  --inst_dismatching                      true
% 2.06/1.00  --inst_eager_unprocessed_to_passive     true
% 2.06/1.00  --inst_prop_sim_given                   true
% 2.06/1.00  --inst_prop_sim_new                     false
% 2.06/1.00  --inst_subs_new                         false
% 2.06/1.00  --inst_eq_res_simp                      false
% 2.06/1.00  --inst_subs_given                       false
% 2.06/1.00  --inst_orphan_elimination               true
% 2.06/1.00  --inst_learning_loop_flag               true
% 2.06/1.00  --inst_learning_start                   3000
% 2.06/1.00  --inst_learning_factor                  2
% 2.06/1.00  --inst_start_prop_sim_after_learn       3
% 2.06/1.00  --inst_sel_renew                        solver
% 2.06/1.00  --inst_lit_activity_flag                true
% 2.06/1.00  --inst_restr_to_given                   false
% 2.06/1.00  --inst_activity_threshold               500
% 2.06/1.00  --inst_out_proof                        true
% 2.06/1.00  
% 2.06/1.00  ------ Resolution Options
% 2.06/1.00  
% 2.06/1.00  --resolution_flag                       false
% 2.06/1.00  --res_lit_sel                           adaptive
% 2.06/1.00  --res_lit_sel_side                      none
% 2.06/1.00  --res_ordering                          kbo
% 2.06/1.00  --res_to_prop_solver                    active
% 2.06/1.00  --res_prop_simpl_new                    false
% 2.06/1.00  --res_prop_simpl_given                  true
% 2.06/1.00  --res_passive_queue_type                priority_queues
% 2.06/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/1.00  --res_passive_queues_freq               [15;5]
% 2.06/1.00  --res_forward_subs                      full
% 2.06/1.00  --res_backward_subs                     full
% 2.06/1.00  --res_forward_subs_resolution           true
% 2.06/1.00  --res_backward_subs_resolution          true
% 2.06/1.00  --res_orphan_elimination                true
% 2.06/1.00  --res_time_limit                        2.
% 2.06/1.00  --res_out_proof                         true
% 2.06/1.00  
% 2.06/1.00  ------ Superposition Options
% 2.06/1.00  
% 2.06/1.00  --superposition_flag                    true
% 2.06/1.00  --sup_passive_queue_type                priority_queues
% 2.06/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.06/1.00  --demod_completeness_check              fast
% 2.06/1.00  --demod_use_ground                      true
% 2.06/1.00  --sup_to_prop_solver                    passive
% 2.06/1.00  --sup_prop_simpl_new                    true
% 2.06/1.00  --sup_prop_simpl_given                  true
% 2.06/1.00  --sup_fun_splitting                     false
% 2.06/1.00  --sup_smt_interval                      50000
% 2.06/1.00  
% 2.06/1.00  ------ Superposition Simplification Setup
% 2.06/1.00  
% 2.06/1.00  --sup_indices_passive                   []
% 2.06/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_full_bw                           [BwDemod]
% 2.06/1.00  --sup_immed_triv                        [TrivRules]
% 2.06/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_immed_bw_main                     []
% 2.06/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.00  
% 2.06/1.00  ------ Combination Options
% 2.06/1.00  
% 2.06/1.00  --comb_res_mult                         3
% 2.06/1.00  --comb_sup_mult                         2
% 2.06/1.00  --comb_inst_mult                        10
% 2.06/1.00  
% 2.06/1.00  ------ Debug Options
% 2.06/1.00  
% 2.06/1.00  --dbg_backtrace                         false
% 2.06/1.00  --dbg_dump_prop_clauses                 false
% 2.06/1.00  --dbg_dump_prop_clauses_file            -
% 2.06/1.00  --dbg_out_stat                          false
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  ------ Proving...
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  % SZS status Theorem for theBenchmark.p
% 2.06/1.00  
% 2.06/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.06/1.00  
% 2.06/1.00  fof(f10,axiom,(
% 2.06/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f30,plain,(
% 2.06/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.06/1.00    inference(nnf_transformation,[],[f10])).
% 2.06/1.00  
% 2.06/1.00  fof(f31,plain,(
% 2.06/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.06/1.00    inference(rectify,[],[f30])).
% 2.06/1.00  
% 2.06/1.00  fof(f34,plain,(
% 2.06/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f33,plain,(
% 2.06/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f32,plain,(
% 2.06/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f35,plain,(
% 2.06/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).
% 2.06/1.00  
% 2.06/1.00  fof(f56,plain,(
% 2.06/1.00    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f35])).
% 2.06/1.00  
% 2.06/1.00  fof(f7,axiom,(
% 2.06/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f27,plain,(
% 2.06/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.06/1.00    inference(nnf_transformation,[],[f7])).
% 2.06/1.00  
% 2.06/1.00  fof(f50,plain,(
% 2.06/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f27])).
% 2.06/1.00  
% 2.06/1.00  fof(f6,axiom,(
% 2.06/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f48,plain,(
% 2.06/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f6])).
% 2.06/1.00  
% 2.06/1.00  fof(f67,plain,(
% 2.06/1.00    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.06/1.00    inference(definition_unfolding,[],[f50,f48])).
% 2.06/1.00  
% 2.06/1.00  fof(f13,axiom,(
% 2.06/1.00    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f21,plain,(
% 2.06/1.00    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 2.06/1.00    inference(ennf_transformation,[],[f13])).
% 2.06/1.00  
% 2.06/1.00  fof(f36,plain,(
% 2.06/1.00    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f37,plain,(
% 2.06/1.00    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))) | k1_xboole_0 = X0)),
% 2.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f36])).
% 2.06/1.00  
% 2.06/1.00  fof(f64,plain,(
% 2.06/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 2.06/1.00    inference(cnf_transformation,[],[f37])).
% 2.06/1.00  
% 2.06/1.00  fof(f69,plain,(
% 2.06/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k2_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 2.06/1.00    inference(definition_unfolding,[],[f64,f48])).
% 2.06/1.00  
% 2.06/1.00  fof(f63,plain,(
% 2.06/1.00    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 2.06/1.00    inference(cnf_transformation,[],[f37])).
% 2.06/1.00  
% 2.06/1.00  fof(f14,conjecture,(
% 2.06/1.00    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f15,negated_conjecture,(
% 2.06/1.00    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.06/1.00    inference(negated_conjecture,[],[f14])).
% 2.06/1.00  
% 2.06/1.00  fof(f22,plain,(
% 2.06/1.00    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.06/1.00    inference(ennf_transformation,[],[f15])).
% 2.06/1.00  
% 2.06/1.00  fof(f23,plain,(
% 2.06/1.00    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.06/1.00    inference(flattening,[],[f22])).
% 2.06/1.00  
% 2.06/1.00  fof(f38,plain,(
% 2.06/1.00    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6))),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f39,plain,(
% 2.06/1.00    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6)),
% 2.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f38])).
% 2.06/1.00  
% 2.06/1.00  fof(f66,plain,(
% 2.06/1.00    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f39])).
% 2.06/1.00  
% 2.06/1.00  fof(f61,plain,(
% 2.06/1.00    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 2.06/1.00    inference(cnf_transformation,[],[f37])).
% 2.06/1.00  
% 2.06/1.00  fof(f62,plain,(
% 2.06/1.00    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 2.06/1.00    inference(cnf_transformation,[],[f37])).
% 2.06/1.00  
% 2.06/1.00  fof(f1,axiom,(
% 2.06/1.00    v1_xboole_0(k1_xboole_0)),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f40,plain,(
% 2.06/1.00    v1_xboole_0(k1_xboole_0)),
% 2.06/1.00    inference(cnf_transformation,[],[f1])).
% 2.06/1.00  
% 2.06/1.00  fof(f9,axiom,(
% 2.06/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f19,plain,(
% 2.06/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.06/1.00    inference(ennf_transformation,[],[f9])).
% 2.06/1.00  
% 2.06/1.00  fof(f53,plain,(
% 2.06/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f19])).
% 2.06/1.00  
% 2.06/1.00  fof(f12,axiom,(
% 2.06/1.00    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f20,plain,(
% 2.06/1.00    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.06/1.00    inference(ennf_transformation,[],[f12])).
% 2.06/1.00  
% 2.06/1.00  fof(f60,plain,(
% 2.06/1.00    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f20])).
% 2.06/1.00  
% 2.06/1.00  fof(f11,axiom,(
% 2.06/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f59,plain,(
% 2.06/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.06/1.00    inference(cnf_transformation,[],[f11])).
% 2.06/1.00  
% 2.06/1.00  fof(f3,axiom,(
% 2.06/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f44,plain,(
% 2.06/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f3])).
% 2.06/1.00  
% 2.06/1.00  fof(f58,plain,(
% 2.06/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.06/1.00    inference(cnf_transformation,[],[f11])).
% 2.06/1.00  
% 2.06/1.00  fof(f2,axiom,(
% 2.06/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f16,plain,(
% 2.06/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.06/1.00    inference(rectify,[],[f2])).
% 2.06/1.00  
% 2.06/1.00  fof(f17,plain,(
% 2.06/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.06/1.00    inference(ennf_transformation,[],[f16])).
% 2.06/1.00  
% 2.06/1.00  fof(f24,plain,(
% 2.06/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.06/1.00    introduced(choice_axiom,[])).
% 2.06/1.00  
% 2.06/1.00  fof(f25,plain,(
% 2.06/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).
% 2.06/1.00  
% 2.06/1.00  fof(f43,plain,(
% 2.06/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f25])).
% 2.06/1.00  
% 2.06/1.00  fof(f4,axiom,(
% 2.06/1.00    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f45,plain,(
% 2.06/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.06/1.00    inference(cnf_transformation,[],[f4])).
% 2.06/1.00  
% 2.06/1.00  fof(f5,axiom,(
% 2.06/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.00  
% 2.06/1.00  fof(f26,plain,(
% 2.06/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.06/1.00    inference(nnf_transformation,[],[f5])).
% 2.06/1.00  
% 2.06/1.00  fof(f47,plain,(
% 2.06/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.06/1.00    inference(cnf_transformation,[],[f26])).
% 2.06/1.00  
% 2.06/1.00  fof(f65,plain,(
% 2.06/1.00    k1_xboole_0 = sK7 | k1_xboole_0 != sK6),
% 2.06/1.00    inference(cnf_transformation,[],[f39])).
% 2.06/1.00  
% 2.06/1.00  cnf(c_14,plain,
% 2.06/1.00      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 2.06/1.00      | r2_hidden(sK2(X0,X1),X1)
% 2.06/1.00      | k1_relat_1(X0) = X1 ),
% 2.06/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1547,plain,
% 2.06/1.00      ( k1_relat_1(X0) = X1
% 2.06/1.00      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top
% 2.06/1.00      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 2.06/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_8,plain,
% 2.06/1.00      ( r1_tarski(k2_tarski(X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.06/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1552,plain,
% 2.06/1.00      ( r1_tarski(k2_tarski(X0,X0),X1) = iProver_top
% 2.06/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 2.06/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_20,plain,
% 2.06/1.00      ( k2_relat_1(sK5(X0,X1)) = k2_tarski(X1,X1) | k1_xboole_0 = X0 ),
% 2.06/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_21,plain,
% 2.06/1.00      ( k1_relat_1(sK5(X0,X1)) = X0 | k1_xboole_0 = X0 ),
% 2.06/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_24,negated_conjecture,
% 2.06/1.00      ( ~ r1_tarski(k2_relat_1(X0),sK6)
% 2.06/1.00      | ~ v1_funct_1(X0)
% 2.06/1.00      | ~ v1_relat_1(X0)
% 2.06/1.00      | k1_relat_1(X0) != sK7 ),
% 2.06/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_23,plain,
% 2.06/1.00      ( v1_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0 ),
% 2.06/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_723,plain,
% 2.06/1.00      ( ~ r1_tarski(k2_relat_1(X0),sK6)
% 2.06/1.00      | ~ v1_funct_1(X0)
% 2.06/1.00      | sK5(X1,X2) != X0
% 2.06/1.00      | k1_relat_1(X0) != sK7
% 2.06/1.00      | k1_xboole_0 = X1 ),
% 2.06/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_23]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_724,plain,
% 2.06/1.00      ( ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK6)
% 2.06/1.00      | ~ v1_funct_1(sK5(X0,X1))
% 2.06/1.00      | k1_relat_1(sK5(X0,X1)) != sK7
% 2.06/1.00      | k1_xboole_0 = X0 ),
% 2.06/1.00      inference(unflattening,[status(thm)],[c_723]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_319,plain,
% 2.06/1.00      ( ~ r1_tarski(k2_relat_1(X0),sK6)
% 2.06/1.00      | ~ v1_funct_1(X0)
% 2.06/1.00      | sK5(X1,X2) != X0
% 2.06/1.00      | k1_relat_1(X0) != sK7
% 2.06/1.00      | k1_xboole_0 = X1 ),
% 2.06/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_23]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_320,plain,
% 2.06/1.00      ( ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK6)
% 2.06/1.00      | ~ v1_funct_1(sK5(X0,X1))
% 2.06/1.00      | k1_relat_1(sK5(X0,X1)) != sK7
% 2.06/1.00      | k1_xboole_0 = X0 ),
% 2.06/1.00      inference(unflattening,[status(thm)],[c_319]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_22,plain,
% 2.06/1.00      ( v1_funct_1(sK5(X0,X1)) | k1_xboole_0 = X0 ),
% 2.06/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_324,plain,
% 2.06/1.00      ( ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK6)
% 2.06/1.00      | k1_relat_1(sK5(X0,X1)) != sK7
% 2.06/1.00      | k1_xboole_0 = X0 ),
% 2.06/1.00      inference(global_propositional_subsumption,
% 2.06/1.00                [status(thm)],
% 2.06/1.00                [c_320,c_22]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_726,plain,
% 2.06/1.00      ( ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK6)
% 2.06/1.00      | k1_relat_1(sK5(X0,X1)) != sK7
% 2.06/1.00      | k1_xboole_0 = X0 ),
% 2.06/1.00      inference(global_propositional_subsumption,
% 2.06/1.00                [status(thm)],
% 2.06/1.00                [c_724,c_22,c_320]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1544,plain,
% 2.06/1.00      ( k1_relat_1(sK5(X0,X1)) != sK7
% 2.06/1.00      | k1_xboole_0 = X0
% 2.06/1.00      | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
% 2.06/1.00      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1839,plain,
% 2.06/1.00      ( sK7 != X0
% 2.06/1.00      | k1_xboole_0 = X0
% 2.06/1.00      | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
% 2.06/1.00      inference(superposition,[status(thm)],[c_21,c_1544]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1997,plain,
% 2.06/1.00      ( sK7 = k1_xboole_0
% 2.06/1.00      | r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
% 2.06/1.00      inference(equality_resolution,[status(thm)],[c_1839]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_0,plain,
% 2.06/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.06/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_12,plain,
% 2.06/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 2.06/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_308,plain,
% 2.06/1.00      ( v1_relat_1(X0) | k1_xboole_0 != X0 ),
% 2.06/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_309,plain,
% 2.06/1.00      ( v1_relat_1(k1_xboole_0) ),
% 2.06/1.00      inference(unflattening,[status(thm)],[c_308]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_740,plain,
% 2.06/1.00      ( ~ r1_tarski(k2_relat_1(X0),sK6)
% 2.06/1.00      | ~ v1_funct_1(X0)
% 2.06/1.00      | k1_relat_1(X0) != sK7
% 2.06/1.00      | k1_xboole_0 != X0 ),
% 2.06/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_309]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_741,plain,
% 2.06/1.00      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK6)
% 2.06/1.00      | ~ v1_funct_1(k1_xboole_0)
% 2.06/1.00      | k1_relat_1(k1_xboole_0) != sK7 ),
% 2.06/1.00      inference(unflattening,[status(thm)],[c_740]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_19,plain,
% 2.06/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.06/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_38,plain,
% 2.06/1.00      ( v1_funct_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_17,plain,
% 2.06/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.06/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_49,plain,
% 2.06/1.00      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_4,plain,
% 2.06/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.06/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_409,plain,
% 2.06/1.00      ( ~ v1_funct_1(X0)
% 2.06/1.00      | ~ v1_relat_1(X0)
% 2.06/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.06/1.00      | k1_relat_1(X0) != sK7
% 2.06/1.00      | sK6 != X1 ),
% 2.06/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_410,plain,
% 2.06/1.00      ( ~ v1_funct_1(X0)
% 2.06/1.00      | ~ v1_relat_1(X0)
% 2.06/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.06/1.00      | k1_relat_1(X0) != sK7 ),
% 2.06/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_412,plain,
% 2.06/1.00      ( ~ v1_funct_1(k1_xboole_0)
% 2.06/1.00      | ~ v1_relat_1(k1_xboole_0)
% 2.06/1.00      | k2_relat_1(k1_xboole_0) != k1_xboole_0
% 2.06/1.00      | k1_relat_1(k1_xboole_0) != sK7 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_410]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_743,plain,
% 2.06/1.00      ( k1_relat_1(k1_xboole_0) != sK7 ),
% 2.06/1.00      inference(global_propositional_subsumption,
% 2.06/1.00                [status(thm)],
% 2.06/1.00                [c_741,c_38,c_17,c_49,c_0,c_412]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_18,plain,
% 2.06/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.06/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1563,plain,
% 2.06/1.00      ( sK7 != k1_xboole_0 ),
% 2.06/1.00      inference(light_normalisation,[status(thm)],[c_743,c_18]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2037,plain,
% 2.06/1.00      ( r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
% 2.06/1.00      inference(global_propositional_subsumption,
% 2.06/1.00                [status(thm)],
% 2.06/1.00                [c_1997,c_1563]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2044,plain,
% 2.06/1.00      ( sK7 = k1_xboole_0
% 2.06/1.00      | r1_tarski(k2_tarski(X0,X0),sK6) != iProver_top ),
% 2.06/1.00      inference(superposition,[status(thm)],[c_20,c_2037]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2049,plain,
% 2.06/1.00      ( r1_tarski(k2_tarski(X0,X0),sK6) != iProver_top ),
% 2.06/1.00      inference(global_propositional_subsumption,
% 2.06/1.00                [status(thm)],
% 2.06/1.00                [c_2044,c_1563]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2351,plain,
% 2.06/1.00      ( r2_hidden(X0,sK6) != iProver_top ),
% 2.06/1.00      inference(superposition,[status(thm)],[c_1552,c_2049]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3112,plain,
% 2.06/1.00      ( k1_relat_1(sK6) = X0 | r2_hidden(sK2(sK6,X0),X0) = iProver_top ),
% 2.06/1.00      inference(superposition,[status(thm)],[c_1547,c_2351]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1,plain,
% 2.06/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 2.06/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1558,plain,
% 2.06/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.06/1.00      | r2_hidden(X0,X2) != iProver_top
% 2.06/1.00      | r1_xboole_0(X2,X1) != iProver_top ),
% 2.06/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3433,plain,
% 2.06/1.00      ( k1_relat_1(sK6) = X0
% 2.06/1.00      | r2_hidden(sK2(sK6,X0),X1) != iProver_top
% 2.06/1.00      | r1_xboole_0(X1,X0) != iProver_top ),
% 2.06/1.00      inference(superposition,[status(thm)],[c_3112,c_1558]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3436,plain,
% 2.06/1.00      ( k1_relat_1(sK6) = sK6 ),
% 2.06/1.00      inference(superposition,[status(thm)],[c_3112,c_2351]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3500,plain,
% 2.06/1.00      ( sK6 = X0
% 2.06/1.00      | r2_hidden(sK2(sK6,X0),X1) != iProver_top
% 2.06/1.00      | r1_xboole_0(X1,X0) != iProver_top ),
% 2.06/1.00      inference(demodulation,[status(thm)],[c_3433,c_3436]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3511,plain,
% 2.06/1.00      ( sK6 = k1_xboole_0
% 2.06/1.00      | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
% 2.06/1.00      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_3500]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3443,plain,
% 2.06/1.00      ( sK6 = X0 | r2_hidden(sK2(sK6,X0),X0) = iProver_top ),
% 2.06/1.00      inference(demodulation,[status(thm)],[c_3436,c_3112]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_3452,plain,
% 2.06/1.00      ( sK6 = k1_xboole_0
% 2.06/1.00      | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_3443]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1150,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1744,plain,
% 2.06/1.00      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_1150]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2022,plain,
% 2.06/1.00      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_1744]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_2023,plain,
% 2.06/1.00      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_2022]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1149,plain,( X0 = X0 ),theory(equality) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1927,plain,
% 2.06/1.00      ( sK7 = sK7 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_1149]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1692,plain,
% 2.06/1.00      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_1150]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1693,plain,
% 2.06/1.00      ( sK6 != k1_xboole_0
% 2.06/1.00      | k1_xboole_0 = sK6
% 2.06/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_1692]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_1164,plain,
% 2.06/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_1149]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_5,plain,
% 2.06/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.06/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_69,plain,
% 2.06/1.00      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_6,plain,
% 2.06/1.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.06/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_66,plain,
% 2.06/1.00      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.06/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_68,plain,
% 2.06/1.00      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.06/1.00      | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.06/1.00      inference(instantiation,[status(thm)],[c_66]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(c_25,negated_conjecture,
% 2.06/1.00      ( k1_xboole_0 = sK7 | k1_xboole_0 != sK6 ),
% 2.06/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.06/1.00  
% 2.06/1.00  cnf(contradiction,plain,
% 2.06/1.00      ( $false ),
% 2.06/1.00      inference(minisat,
% 2.06/1.00                [status(thm)],
% 2.06/1.00                [c_3511,c_3452,c_2023,c_1927,c_1693,c_1563,c_1164,c_69,
% 2.06/1.00                 c_68,c_25]) ).
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.06/1.00  
% 2.06/1.00  ------                               Statistics
% 2.06/1.00  
% 2.06/1.00  ------ General
% 2.06/1.00  
% 2.06/1.00  abstr_ref_over_cycles:                  0
% 2.06/1.00  abstr_ref_under_cycles:                 0
% 2.06/1.00  gc_basic_clause_elim:                   0
% 2.06/1.00  forced_gc_time:                         0
% 2.06/1.00  parsing_time:                           0.009
% 2.06/1.00  unif_index_cands_time:                  0.
% 2.06/1.00  unif_index_add_time:                    0.
% 2.06/1.00  orderings_time:                         0.
% 2.06/1.00  out_proof_time:                         0.01
% 2.06/1.00  total_time:                             0.119
% 2.06/1.00  num_of_symbols:                         51
% 2.06/1.00  num_of_terms:                           2966
% 2.06/1.00  
% 2.06/1.00  ------ Preprocessing
% 2.06/1.00  
% 2.06/1.00  num_of_splits:                          0
% 2.06/1.00  num_of_split_atoms:                     0
% 2.06/1.00  num_of_reused_defs:                     0
% 2.06/1.00  num_eq_ax_congr_red:                    64
% 2.06/1.00  num_of_sem_filtered_clauses:            1
% 2.06/1.00  num_of_subtypes:                        0
% 2.06/1.00  monotx_restored_types:                  0
% 2.06/1.00  sat_num_of_epr_types:                   0
% 2.06/1.00  sat_num_of_non_cyclic_types:            0
% 2.06/1.00  sat_guarded_non_collapsed_types:        0
% 2.06/1.00  num_pure_diseq_elim:                    0
% 2.06/1.00  simp_replaced_by:                       0
% 2.06/1.00  res_preprocessed:                       134
% 2.06/1.00  prep_upred:                             0
% 2.06/1.00  prep_unflattend:                        35
% 2.06/1.00  smt_new_axioms:                         0
% 2.06/1.00  pred_elim_cands:                        3
% 2.06/1.00  pred_elim:                              3
% 2.06/1.00  pred_elim_cl:                           4
% 2.06/1.00  pred_elim_cycles:                       11
% 2.06/1.00  merged_defs:                            20
% 2.06/1.00  merged_defs_ncl:                        0
% 2.06/1.00  bin_hyper_res:                          20
% 2.06/1.00  prep_cycles:                            5
% 2.06/1.00  pred_elim_time:                         0.007
% 2.06/1.00  splitting_time:                         0.
% 2.06/1.00  sem_filter_time:                        0.
% 2.06/1.00  monotx_time:                            0.
% 2.06/1.00  subtype_inf_time:                       0.
% 2.06/1.00  
% 2.06/1.00  ------ Problem properties
% 2.06/1.00  
% 2.06/1.00  clauses:                                22
% 2.06/1.00  conjectures:                            1
% 2.06/1.00  epr:                                    3
% 2.06/1.00  horn:                                   17
% 2.06/1.00  ground:                                 4
% 2.06/1.00  unary:                                  5
% 2.06/1.00  binary:                                 12
% 2.06/1.00  lits:                                   44
% 2.06/1.00  lits_eq:                                16
% 2.06/1.00  fd_pure:                                0
% 2.06/1.00  fd_pseudo:                              0
% 2.06/1.00  fd_cond:                                2
% 2.06/1.00  fd_pseudo_cond:                         2
% 2.06/1.00  ac_symbols:                             0
% 2.06/1.00  
% 2.06/1.00  ------ Propositional Solver
% 2.06/1.00  
% 2.06/1.00  prop_solver_calls:                      33
% 2.06/1.00  prop_fast_solver_calls:                 738
% 2.06/1.00  smt_solver_calls:                       0
% 2.06/1.00  smt_fast_solver_calls:                  0
% 2.06/1.00  prop_num_of_clauses:                    1112
% 2.06/1.00  prop_preprocess_simplified:             4809
% 2.06/1.00  prop_fo_subsumed:                       9
% 2.06/1.00  prop_solver_time:                       0.
% 2.06/1.00  smt_solver_time:                        0.
% 2.06/1.00  smt_fast_solver_time:                   0.
% 2.06/1.00  prop_fast_solver_time:                  0.
% 2.06/1.00  prop_unsat_core_time:                   0.
% 2.06/1.00  
% 2.06/1.00  ------ QBF
% 2.06/1.00  
% 2.06/1.00  qbf_q_res:                              0
% 2.06/1.00  qbf_num_tautologies:                    0
% 2.06/1.00  qbf_prep_cycles:                        0
% 2.06/1.00  
% 2.06/1.00  ------ BMC1
% 2.06/1.00  
% 2.06/1.00  bmc1_current_bound:                     -1
% 2.06/1.00  bmc1_last_solved_bound:                 -1
% 2.06/1.00  bmc1_unsat_core_size:                   -1
% 2.06/1.00  bmc1_unsat_core_parents_size:           -1
% 2.06/1.00  bmc1_merge_next_fun:                    0
% 2.06/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.06/1.00  
% 2.06/1.00  ------ Instantiation
% 2.06/1.00  
% 2.06/1.00  inst_num_of_clauses:                    323
% 2.06/1.00  inst_num_in_passive:                    107
% 2.06/1.00  inst_num_in_active:                     170
% 2.06/1.00  inst_num_in_unprocessed:                46
% 2.06/1.00  inst_num_of_loops:                      210
% 2.06/1.00  inst_num_of_learning_restarts:          0
% 2.06/1.00  inst_num_moves_active_passive:          36
% 2.06/1.00  inst_lit_activity:                      0
% 2.06/1.00  inst_lit_activity_moves:                0
% 2.06/1.00  inst_num_tautologies:                   0
% 2.06/1.00  inst_num_prop_implied:                  0
% 2.06/1.00  inst_num_existing_simplified:           0
% 2.06/1.00  inst_num_eq_res_simplified:             0
% 2.06/1.00  inst_num_child_elim:                    0
% 2.06/1.00  inst_num_of_dismatching_blockings:      57
% 2.06/1.00  inst_num_of_non_proper_insts:           204
% 2.06/1.00  inst_num_of_duplicates:                 0
% 2.06/1.00  inst_inst_num_from_inst_to_res:         0
% 2.06/1.00  inst_dismatching_checking_time:         0.
% 2.06/1.00  
% 2.06/1.00  ------ Resolution
% 2.06/1.00  
% 2.06/1.00  res_num_of_clauses:                     0
% 2.06/1.00  res_num_in_passive:                     0
% 2.06/1.00  res_num_in_active:                      0
% 2.06/1.00  res_num_of_loops:                       139
% 2.06/1.00  res_forward_subset_subsumed:            16
% 2.06/1.00  res_backward_subset_subsumed:           0
% 2.06/1.00  res_forward_subsumed:                   0
% 2.06/1.00  res_backward_subsumed:                  0
% 2.06/1.00  res_forward_subsumption_resolution:     0
% 2.06/1.00  res_backward_subsumption_resolution:    0
% 2.06/1.00  res_clause_to_clause_subsumption:       121
% 2.06/1.00  res_orphan_elimination:                 0
% 2.06/1.00  res_tautology_del:                      68
% 2.06/1.00  res_num_eq_res_simplified:              0
% 2.06/1.00  res_num_sel_changes:                    0
% 2.06/1.00  res_moves_from_active_to_pass:          0
% 2.06/1.00  
% 2.06/1.00  ------ Superposition
% 2.06/1.00  
% 2.06/1.00  sup_time_total:                         0.
% 2.06/1.00  sup_time_generating:                    0.
% 2.06/1.00  sup_time_sim_full:                      0.
% 2.06/1.00  sup_time_sim_immed:                     0.
% 2.06/1.00  
% 2.06/1.00  sup_num_of_clauses:                     62
% 2.06/1.00  sup_num_in_active:                      35
% 2.06/1.00  sup_num_in_passive:                     27
% 2.06/1.00  sup_num_of_loops:                       40
% 2.06/1.00  sup_fw_superposition:                   38
% 2.06/1.00  sup_bw_superposition:                   39
% 2.06/1.00  sup_immediate_simplified:               15
% 2.06/1.00  sup_given_eliminated:                   1
% 2.06/1.00  comparisons_done:                       0
% 2.06/1.00  comparisons_avoided:                    4
% 2.06/1.00  
% 2.06/1.00  ------ Simplifications
% 2.06/1.00  
% 2.06/1.00  
% 2.06/1.00  sim_fw_subset_subsumed:                 4
% 2.06/1.00  sim_bw_subset_subsumed:                 0
% 2.06/1.00  sim_fw_subsumed:                        7
% 2.06/1.00  sim_bw_subsumed:                        0
% 2.06/1.00  sim_fw_subsumption_res:                 0
% 2.06/1.00  sim_bw_subsumption_res:                 0
% 2.06/1.00  sim_tautology_del:                      3
% 2.06/1.00  sim_eq_tautology_del:                   3
% 2.06/1.00  sim_eq_res_simp:                        0
% 2.06/1.00  sim_fw_demodulated:                     2
% 2.06/1.00  sim_bw_demodulated:                     6
% 2.06/1.00  sim_light_normalised:                   3
% 2.06/1.00  sim_joinable_taut:                      0
% 2.06/1.00  sim_joinable_simp:                      0
% 2.06/1.00  sim_ac_normalised:                      0
% 2.06/1.00  sim_smt_subsumption:                    0
% 2.06/1.00  
%------------------------------------------------------------------------------
