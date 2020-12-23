%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:31 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 303 expanded)
%              Number of clauses        :   62 ( 110 expanded)
%              Number of leaves         :   18 (  71 expanded)
%              Depth                    :   20
%              Number of atoms          :  364 (1124 expanded)
%              Number of equality atoms :  107 ( 308 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
        & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
            & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
        | k1_xboole_0 != k10_relat_1(sK7,sK6) )
      & ( r1_xboole_0(k2_relat_1(sK7),sK6)
        | k1_xboole_0 = k10_relat_1(sK7,sK6) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 != k10_relat_1(sK7,sK6) )
    & ( r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 = k10_relat_1(sK7,sK6) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f31,f32])).

fof(f50,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f9,plain,(
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

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17200,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | r2_hidden(sK4(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(resolution,[status(thm)],[c_11,c_10])).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17186,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | ~ r2_hidden(X0,k10_relat_1(sK7,sK6))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_217,c_16])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16599,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_17209,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | ~ r2_hidden(X0,k10_relat_1(sK7,sK6))
    | X1 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17186,c_16599])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17407,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
    | r1_xboole_0(k2_relat_1(sK7),sK6)
    | X1 != sK1(X0,k10_relat_1(sK7,sK6)) ),
    inference(resolution,[status(thm)],[c_17209,c_3])).

cnf(c_216,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_215,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1947,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_216,c_215])).

cnf(c_2186,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1947,c_16])).

cnf(c_218,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2206,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
    | ~ r1_xboole_0(X1,k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK7),sK6)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_2186,c_218])).

cnf(c_2475,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
    | r1_xboole_0(k2_relat_1(sK7),sK6)
    | X0 != X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2206,c_5])).

cnf(c_2625,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
    | r1_xboole_0(k2_relat_1(sK7),sK6) ),
    inference(resolution,[status(thm)],[c_2475,c_215])).

cnf(c_17422,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | r1_xboole_0(X0,k10_relat_1(sK7,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17407,c_2625])).

cnf(c_17423,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
    | r1_xboole_0(k2_relat_1(sK7),sK6) ),
    inference(renaming,[status(thm)],[c_17422])).

cnf(c_17438,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | ~ r2_hidden(X0,k10_relat_1(sK7,sK6)) ),
    inference(resolution,[status(thm)],[c_17423,c_6])).

cnf(c_19688,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ r2_hidden(X0,sK6)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[status(thm)],[c_17200,c_17438])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1764,plain,
    ( k10_relat_1(sK7,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_1856,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK7,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_1857,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(equality_resolution_simp,[status(thm)],[c_1856])).

cnf(c_1551,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,sK6)
    | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1554,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2006,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_1554])).

cnf(c_2020,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ r2_hidden(X0,sK6)
    | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2006])).

cnf(c_20188,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19688,c_17,c_15,c_1857,c_2020])).

cnf(c_20189,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ r2_hidden(X0,sK6) ),
    inference(renaming,[status(thm)],[c_20188])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20218,plain,
    ( r1_xboole_0(k2_relat_1(sK7),X0)
    | ~ r2_hidden(sK1(k2_relat_1(sK7),X0),sK6) ),
    inference(resolution,[status(thm)],[c_20189,c_4])).

cnf(c_20502,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6) ),
    inference(resolution,[status(thm)],[c_20218,c_3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16375,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16367,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16366,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16364,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,sK6)
    | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_16374,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17313,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_16364,c_16374])).

cnf(c_17328,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_16366,c_17313])).

cnf(c_18,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_17526,plain,
    ( r2_hidden(sK5(X0,X1,sK7),sK6) != iProver_top
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17328,c_18])).

cnf(c_17527,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_17526])).

cnf(c_18135,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_16367,c_17527])).

cnf(c_20,plain,
    ( k1_xboole_0 != k10_relat_1(sK7,sK6)
    | r1_xboole_0(k2_relat_1(sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17439,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17438])).

cnf(c_18711,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18135,c_18,c_20,c_1857,c_17439])).

cnf(c_18723,plain,
    ( k10_relat_1(sK7,sK6) = X0
    | r2_hidden(sK0(k10_relat_1(sK7,sK6),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16375,c_18711])).

cnf(c_16371,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16370,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16700,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16371,c_16370])).

cnf(c_20327,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18723,c_16700])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20502,c_20327,c_1857,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.69/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/1.49  
% 7.69/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.69/1.49  
% 7.69/1.49  ------  iProver source info
% 7.69/1.49  
% 7.69/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.69/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.69/1.49  git: non_committed_changes: false
% 7.69/1.49  git: last_make_outside_of_git: false
% 7.69/1.49  
% 7.69/1.49  ------ 
% 7.69/1.49  ------ Parsing...
% 7.69/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.69/1.49  ------ Proving...
% 7.69/1.49  ------ Problem Properties 
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  clauses                                 18
% 7.69/1.49  conjectures                             3
% 7.69/1.49  EPR                                     3
% 7.69/1.49  Horn                                    13
% 7.69/1.49  unary                                   2
% 7.69/1.49  binary                                  7
% 7.69/1.49  lits                                    45
% 7.69/1.49  lits eq                                 6
% 7.69/1.49  fd_pure                                 0
% 7.69/1.49  fd_pseudo                               0
% 7.69/1.49  fd_cond                                 0
% 7.69/1.49  fd_pseudo_cond                          4
% 7.69/1.49  AC symbols                              0
% 7.69/1.49  
% 7.69/1.49  ------ Input Options Time Limit: Unbounded
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.69/1.49  Current options:
% 7.69/1.49  ------ 
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  ------ Proving...
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.69/1.49  
% 7.69/1.49  ------ Proving...
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.69/1.49  
% 7.69/1.49  ------ Proving...
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.69/1.49  
% 7.69/1.49  ------ Proving...
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.69/1.49  
% 7.69/1.49  ------ Proving...
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.69/1.49  
% 7.69/1.49  ------ Proving...
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  % SZS status Theorem for theBenchmark.p
% 7.69/1.49  
% 7.69/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.69/1.49  
% 7.69/1.49  fof(f6,axiom,(
% 7.69/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 7.69/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f13,plain,(
% 7.69/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.69/1.49    inference(ennf_transformation,[],[f6])).
% 7.69/1.49  
% 7.69/1.49  fof(f26,plain,(
% 7.69/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.69/1.49    inference(nnf_transformation,[],[f13])).
% 7.69/1.49  
% 7.69/1.49  fof(f27,plain,(
% 7.69/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.69/1.49    inference(rectify,[],[f26])).
% 7.69/1.49  
% 7.69/1.49  fof(f28,plain,(
% 7.69/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f29,plain,(
% 7.69/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.69/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 7.69/1.49  
% 7.69/1.49  fof(f48,plain,(
% 7.69/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f29])).
% 7.69/1.49  
% 7.69/1.49  fof(f5,axiom,(
% 7.69/1.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.69/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f20,plain,(
% 7.69/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.69/1.49    inference(nnf_transformation,[],[f5])).
% 7.69/1.49  
% 7.69/1.49  fof(f21,plain,(
% 7.69/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.69/1.49    inference(rectify,[],[f20])).
% 7.69/1.49  
% 7.69/1.49  fof(f24,plain,(
% 7.69/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f23,plain,(
% 7.69/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0))) )),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f22,plain,(
% 7.69/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f25,plain,(
% 7.69/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.69/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).
% 7.69/1.49  
% 7.69/1.49  fof(f41,plain,(
% 7.69/1.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 7.69/1.49    inference(cnf_transformation,[],[f25])).
% 7.69/1.49  
% 7.69/1.49  fof(f53,plain,(
% 7.69/1.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 7.69/1.49    inference(equality_resolution,[],[f41])).
% 7.69/1.49  
% 7.69/1.49  fof(f7,conjecture,(
% 7.69/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.69/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f8,negated_conjecture,(
% 7.69/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.69/1.49    inference(negated_conjecture,[],[f7])).
% 7.69/1.49  
% 7.69/1.49  fof(f14,plain,(
% 7.69/1.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 7.69/1.49    inference(ennf_transformation,[],[f8])).
% 7.69/1.49  
% 7.69/1.49  fof(f30,plain,(
% 7.69/1.49    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.69/1.49    inference(nnf_transformation,[],[f14])).
% 7.69/1.49  
% 7.69/1.49  fof(f31,plain,(
% 7.69/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.69/1.49    inference(flattening,[],[f30])).
% 7.69/1.49  
% 7.69/1.49  fof(f32,plain,(
% 7.69/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f33,plain,(
% 7.69/1.49    (~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7)),
% 7.69/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f31,f32])).
% 7.69/1.49  
% 7.69/1.49  fof(f50,plain,(
% 7.69/1.49    r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)),
% 7.69/1.49    inference(cnf_transformation,[],[f33])).
% 7.69/1.49  
% 7.69/1.49  fof(f4,axiom,(
% 7.69/1.49    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 7.69/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f12,plain,(
% 7.69/1.49    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 7.69/1.49    inference(ennf_transformation,[],[f4])).
% 7.69/1.49  
% 7.69/1.49  fof(f40,plain,(
% 7.69/1.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f12])).
% 7.69/1.49  
% 7.69/1.49  fof(f3,axiom,(
% 7.69/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.69/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f39,plain,(
% 7.69/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f3])).
% 7.69/1.49  
% 7.69/1.49  fof(f2,axiom,(
% 7.69/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.69/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f9,plain,(
% 7.69/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.69/1.49    inference(rectify,[],[f2])).
% 7.69/1.49  
% 7.69/1.49  fof(f11,plain,(
% 7.69/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.69/1.49    inference(ennf_transformation,[],[f9])).
% 7.69/1.49  
% 7.69/1.49  fof(f18,plain,(
% 7.69/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f19,plain,(
% 7.69/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.69/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f18])).
% 7.69/1.49  
% 7.69/1.49  fof(f37,plain,(
% 7.69/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f19])).
% 7.69/1.49  
% 7.69/1.49  fof(f49,plain,(
% 7.69/1.49    v1_relat_1(sK7)),
% 7.69/1.49    inference(cnf_transformation,[],[f33])).
% 7.69/1.49  
% 7.69/1.49  fof(f51,plain,(
% 7.69/1.49    ~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)),
% 7.69/1.49    inference(cnf_transformation,[],[f33])).
% 7.69/1.49  
% 7.69/1.49  fof(f38,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f19])).
% 7.69/1.49  
% 7.69/1.49  fof(f36,plain,(
% 7.69/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f19])).
% 7.69/1.49  
% 7.69/1.49  fof(f1,axiom,(
% 7.69/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 7.69/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f10,plain,(
% 7.69/1.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 7.69/1.49    inference(ennf_transformation,[],[f1])).
% 7.69/1.49  
% 7.69/1.49  fof(f15,plain,(
% 7.69/1.49    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 7.69/1.49    inference(nnf_transformation,[],[f10])).
% 7.69/1.49  
% 7.69/1.49  fof(f16,plain,(
% 7.69/1.49    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f17,plain,(
% 7.69/1.49    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 7.69/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 7.69/1.49  
% 7.69/1.49  fof(f34,plain,(
% 7.69/1.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f17])).
% 7.69/1.49  
% 7.69/1.49  fof(f47,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f29])).
% 7.69/1.49  
% 7.69/1.49  fof(f45,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f29])).
% 7.69/1.49  
% 7.69/1.49  cnf(c_11,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,X1)
% 7.69/1.49      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.69/1.49      | ~ r2_hidden(X0,k2_relat_1(X3))
% 7.69/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.69/1.49      | ~ v1_relat_1(X3) ),
% 7.69/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_10,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.69/1.49      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
% 7.69/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17200,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,X1)
% 7.69/1.49      | ~ r2_hidden(X0,k2_relat_1(X2))
% 7.69/1.49      | r2_hidden(sK4(X2,X0),k10_relat_1(X2,X1))
% 7.69/1.49      | ~ v1_relat_1(X2) ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_11,c_10]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_217,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.69/1.49      theory(equality) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16,negated_conjecture,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
% 7.69/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17186,plain,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | ~ r2_hidden(X0,k10_relat_1(sK7,sK6))
% 7.69/1.49      | r2_hidden(X1,k1_xboole_0)
% 7.69/1.49      | X1 != X0 ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_217,c_16]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6,plain,
% 7.69/1.49      ( ~ r1_xboole_0(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 7.69/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5,plain,
% 7.69/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16599,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17209,plain,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | ~ r2_hidden(X0,k10_relat_1(sK7,sK6))
% 7.69/1.49      | X1 != X0 ),
% 7.69/1.49      inference(forward_subsumption_resolution,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_17186,c_16599]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_3,plain,
% 7.69/1.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 7.69/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17407,plain,
% 7.69/1.49      ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
% 7.69/1.49      | r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | X1 != sK1(X0,k10_relat_1(sK7,sK6)) ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_17209,c_3]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_216,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_215,plain,( X0 = X0 ),theory(equality) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_1947,plain,
% 7.69/1.49      ( X0 != X1 | X1 = X0 ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_216,c_215]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_2186,plain,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_1947,c_16]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_218,plain,
% 7.69/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.69/1.49      theory(equality) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_2206,plain,
% 7.69/1.49      ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
% 7.69/1.49      | ~ r1_xboole_0(X1,k1_xboole_0)
% 7.69/1.49      | r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | X0 != X1 ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_2186,c_218]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_2475,plain,
% 7.69/1.49      ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
% 7.69/1.49      | r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | X0 != X1 ),
% 7.69/1.49      inference(forward_subsumption_resolution,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_2206,c_5]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_2625,plain,
% 7.69/1.49      ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
% 7.69/1.49      | r1_xboole_0(k2_relat_1(sK7),sK6) ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_2475,c_215]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17422,plain,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | r1_xboole_0(X0,k10_relat_1(sK7,sK6)) ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_17407,c_2625]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17423,plain,
% 7.69/1.49      ( r1_xboole_0(X0,k10_relat_1(sK7,sK6))
% 7.69/1.49      | r1_xboole_0(k2_relat_1(sK7),sK6) ),
% 7.69/1.49      inference(renaming,[status(thm)],[c_17422]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17438,plain,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | ~ r2_hidden(X0,k10_relat_1(sK7,sK6)) ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_17423,c_6]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_19688,plain,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.69/1.49      | ~ r2_hidden(X0,sK6)
% 7.69/1.49      | ~ v1_relat_1(sK7) ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_17200,c_17438]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17,negated_conjecture,
% 7.69/1.49      ( v1_relat_1(sK7) ),
% 7.69/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_15,negated_conjecture,
% 7.69/1.49      ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.69/1.49      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.69/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_1764,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) != X0
% 7.69/1.49      | k1_xboole_0 != X0
% 7.69/1.49      | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_216]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_1856,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.69/1.49      | k1_xboole_0 = k10_relat_1(sK7,sK6)
% 7.69/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_1764]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_1857,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.69/1.49      | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
% 7.69/1.49      inference(equality_resolution_simp,[status(thm)],[c_1856]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_1551,plain,
% 7.69/1.49      ( k1_xboole_0 = k10_relat_1(sK7,sK6)
% 7.69/1.49      | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_2,plain,
% 7.69/1.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_1554,plain,
% 7.69/1.49      ( r1_xboole_0(X0,X1) != iProver_top
% 7.69/1.49      | r2_hidden(X2,X1) != iProver_top
% 7.69/1.49      | r2_hidden(X2,X0) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_2006,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 7.69/1.49      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 7.69/1.49      | r2_hidden(X0,sK6) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_1551,c_1554]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_2020,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.69/1.49      | ~ r2_hidden(X0,sK6)
% 7.69/1.49      | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 7.69/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2006]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_20188,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,sK6) | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_19688,c_17,c_15,c_1857,c_2020]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_20189,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,k2_relat_1(sK7)) | ~ r2_hidden(X0,sK6) ),
% 7.69/1.49      inference(renaming,[status(thm)],[c_20188]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_4,plain,
% 7.69/1.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_20218,plain,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),X0)
% 7.69/1.49      | ~ r2_hidden(sK1(k2_relat_1(sK7),X0),sK6) ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_20189,c_4]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_20502,plain,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6) ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_20218,c_3]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_1,plain,
% 7.69/1.49      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 7.69/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16375,plain,
% 7.69/1.49      ( X0 = X1
% 7.69/1.49      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 7.69/1.49      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_12,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.69/1.49      | r2_hidden(sK5(X0,X2,X1),X2)
% 7.69/1.49      | ~ v1_relat_1(X1) ),
% 7.69/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16367,plain,
% 7.69/1.49      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 7.69/1.49      | r2_hidden(sK5(X0,X2,X1),X2) = iProver_top
% 7.69/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_14,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.69/1.49      | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
% 7.69/1.49      | ~ v1_relat_1(X1) ),
% 7.69/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16366,plain,
% 7.69/1.49      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 7.69/1.49      | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1)) = iProver_top
% 7.69/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16364,plain,
% 7.69/1.49      ( k1_xboole_0 = k10_relat_1(sK7,sK6)
% 7.69/1.49      | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16374,plain,
% 7.69/1.49      ( r1_xboole_0(X0,X1) != iProver_top
% 7.69/1.49      | r2_hidden(X2,X1) != iProver_top
% 7.69/1.49      | r2_hidden(X2,X0) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17313,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 7.69/1.49      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 7.69/1.49      | r2_hidden(X0,sK6) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_16364,c_16374]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17328,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 7.69/1.49      | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.69/1.49      | r2_hidden(sK5(X0,X1,sK7),sK6) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_16366,c_17313]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_18,plain,
% 7.69/1.49      ( v1_relat_1(sK7) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17526,plain,
% 7.69/1.49      ( r2_hidden(sK5(X0,X1,sK7),sK6) != iProver_top
% 7.69/1.49      | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.69/1.49      | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_17328,c_18]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17527,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 7.69/1.49      | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.69/1.49      | r2_hidden(sK5(X0,X1,sK7),sK6) != iProver_top ),
% 7.69/1.49      inference(renaming,[status(thm)],[c_17526]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_18135,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 7.69/1.49      | r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_16367,c_17527]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_20,plain,
% 7.69/1.49      ( k1_xboole_0 != k10_relat_1(sK7,sK6)
% 7.69/1.49      | r1_xboole_0(k2_relat_1(sK7),sK6) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17439,plain,
% 7.69/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top
% 7.69/1.49      | r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_17438]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_18711,plain,
% 7.69/1.49      ( r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_18135,c_18,c_20,c_1857,c_17439]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_18723,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) = X0
% 7.69/1.49      | r2_hidden(sK0(k10_relat_1(sK7,sK6),X0),X0) = iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_16375,c_18711]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16371,plain,
% 7.69/1.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16370,plain,
% 7.69/1.49      ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
% 7.69/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_16700,plain,
% 7.69/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_16371,c_16370]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_20327,plain,
% 7.69/1.49      ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_18723,c_16700]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(contradiction,plain,
% 7.69/1.49      ( $false ),
% 7.69/1.49      inference(minisat,[status(thm)],[c_20502,c_20327,c_1857,c_15]) ).
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.69/1.49  
% 7.69/1.49  ------                               Statistics
% 7.69/1.49  
% 7.69/1.49  ------ Selected
% 7.69/1.49  
% 7.69/1.49  total_time:                             0.548
% 7.69/1.49  
%------------------------------------------------------------------------------
