%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:30 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 218 expanded)
%              Number of clauses        :   44 (  79 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  269 ( 726 expanded)
%              Number of equality atoms :   59 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK7,sK6)
        | ~ r2_hidden(sK6,k1_relat_1(sK7)) )
      & ( k1_xboole_0 != k11_relat_1(sK7,sK6)
        | r2_hidden(sK6,k1_relat_1(sK7)) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK7,sK6)
      | ~ r2_hidden(sK6,k1_relat_1(sK7)) )
    & ( k1_xboole_0 != k11_relat_1(sK7,sK6)
      | r2_hidden(sK6,k1_relat_1(sK7)) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f31,f32])).

fof(f49,plain,
    ( k1_xboole_0 != k11_relat_1(sK7,sK6)
    | r2_hidden(sK6,k1_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f43,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f50,plain,
    ( k1_xboole_0 = k11_relat_1(sK7,sK6)
    | ~ r2_hidden(sK6,k1_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1225,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r2_hidden(sK2(X1),X1)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_7,c_1])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_238,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_239,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_3645,plain,
    ( r2_hidden(sK2(X0),X0)
    | X0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1225,c_239])).

cnf(c_426,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_425,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2315,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_426,c_425])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2665,plain,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2315,c_4])).

cnf(c_2675,plain,
    ( X0 != k3_xboole_0(X1,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_2665,c_426])).

cnf(c_3908,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_3645,c_2675])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK6,k1_relat_1(sK7))
    | k1_xboole_0 != k11_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4096,plain,
    ( r2_hidden(sK2(k11_relat_1(sK7,sK6)),k11_relat_1(sK7,sK6))
    | r2_hidden(sK6,k1_relat_1(sK7)) ),
    inference(resolution,[status(thm)],[c_3908,c_15])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_265,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK7,X1))
    | r2_hidden(k4_tarski(X1,X0),sK7) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_336,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK7)
    | ~ r2_hidden(X0,k11_relat_1(sK7,X1)) ),
    inference(prop_impl,[status(thm)],[c_265])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK7,X1))
    | r2_hidden(k4_tarski(X1,X0),sK7) ),
    inference(renaming,[status(thm)],[c_336])).

cnf(c_1636,plain,
    ( r2_hidden(k4_tarski(sK6,sK2(k11_relat_1(sK7,sK6))),sK7)
    | ~ r2_hidden(sK2(k11_relat_1(sK7,sK6)),k11_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3309,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK2(k11_relat_1(sK7,sK6))),sK7)
    | r2_hidden(sK6,k1_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4155,plain,
    ( r2_hidden(sK6,k1_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4096,c_1636,c_3309])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK6,k1_relat_1(sK7))
    | k1_xboole_0 = k11_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4166,plain,
    ( k1_xboole_0 = k11_relat_1(sK7,sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4155,c_14])).

cnf(c_427,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4392,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK7,sK6))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_4166,c_427])).

cnf(c_13,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_252,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_253,plain,
    ( r2_hidden(X0,k11_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK7) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_338,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK7)
    | r2_hidden(X0,k11_relat_1(sK7,X1)) ),
    inference(prop_impl,[status(thm)],[c_253])).

cnf(c_339,plain,
    ( r2_hidden(X0,k11_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK7) ),
    inference(renaming,[status(thm)],[c_338])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1958,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k11_relat_1(sK7,X0)) ),
    inference(resolution,[status(thm)],[c_339,c_11])).

cnf(c_4832,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK6,k1_relat_1(sK7))
    | X0 != sK5(sK7,sK6) ),
    inference(resolution,[status(thm)],[c_4392,c_1958])).

cnf(c_790,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_804,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_790,c_4])).

cnf(c_876,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_804])).

cnf(c_6098,plain,
    ( X0 != sK5(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4832,c_876,c_1636,c_3309,c_4096])).

cnf(c_6109,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_6098,c_425])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 2.92/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/1.00  
% 2.92/1.00  ------  iProver source info
% 2.92/1.00  
% 2.92/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.92/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/1.00  git: non_committed_changes: false
% 2.92/1.00  git: last_make_outside_of_git: false
% 2.92/1.00  
% 2.92/1.00  ------ 
% 2.92/1.00  ------ Parsing...
% 2.92/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/1.00  ------ Proving...
% 2.92/1.00  ------ Problem Properties 
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  clauses                                 15
% 2.92/1.00  conjectures                             2
% 2.92/1.00  EPR                                     0
% 2.92/1.00  Horn                                    13
% 2.92/1.00  unary                                   2
% 2.92/1.00  binary                                  8
% 2.92/1.00  lits                                    33
% 2.92/1.00  lits eq                                 7
% 2.92/1.00  fd_pure                                 0
% 2.92/1.00  fd_pseudo                               0
% 2.92/1.00  fd_cond                                 0
% 2.92/1.00  fd_pseudo_cond                          4
% 2.92/1.00  AC symbols                              0
% 2.92/1.00  
% 2.92/1.00  ------ Input Options Time Limit: Unbounded
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  ------ 
% 2.92/1.00  Current options:
% 2.92/1.00  ------ 
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  ------ Proving...
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  % SZS status Theorem for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00   Resolution empty clause
% 2.92/1.00  
% 2.92/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  fof(f5,axiom,(
% 2.92/1.00    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f13,plain,(
% 2.92/1.00    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.92/1.00    inference(ennf_transformation,[],[f5])).
% 2.92/1.00  
% 2.92/1.00  fof(f21,plain,(
% 2.92/1.00    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f22,plain,(
% 2.92/1.00    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f21])).
% 2.92/1.00  
% 2.92/1.00  fof(f40,plain,(
% 2.92/1.00    ( ! [X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X0,X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f22])).
% 2.92/1.00  
% 2.92/1.00  fof(f1,axiom,(
% 2.92/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f11,plain,(
% 2.92/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.92/1.00    inference(ennf_transformation,[],[f1])).
% 2.92/1.00  
% 2.92/1.00  fof(f16,plain,(
% 2.92/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.92/1.00    inference(nnf_transformation,[],[f11])).
% 2.92/1.00  
% 2.92/1.00  fof(f17,plain,(
% 2.92/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f18,plain,(
% 2.92/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 2.92/1.00  
% 2.92/1.00  fof(f34,plain,(
% 2.92/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f18])).
% 2.92/1.00  
% 2.92/1.00  fof(f2,axiom,(
% 2.92/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f10,plain,(
% 2.92/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.92/1.00    inference(rectify,[],[f2])).
% 2.92/1.00  
% 2.92/1.00  fof(f12,plain,(
% 2.92/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.92/1.00    inference(ennf_transformation,[],[f10])).
% 2.92/1.00  
% 2.92/1.00  fof(f19,plain,(
% 2.92/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f20,plain,(
% 2.92/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).
% 2.92/1.00  
% 2.92/1.00  fof(f37,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f20])).
% 2.92/1.00  
% 2.92/1.00  fof(f4,axiom,(
% 2.92/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f39,plain,(
% 2.92/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f4])).
% 2.92/1.00  
% 2.92/1.00  fof(f3,axiom,(
% 2.92/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f38,plain,(
% 2.92/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.92/1.00    inference(cnf_transformation,[],[f3])).
% 2.92/1.00  
% 2.92/1.00  fof(f8,conjecture,(
% 2.92/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f9,negated_conjecture,(
% 2.92/1.00    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.92/1.00    inference(negated_conjecture,[],[f8])).
% 2.92/1.00  
% 2.92/1.00  fof(f15,plain,(
% 2.92/1.00    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 2.92/1.00    inference(ennf_transformation,[],[f9])).
% 2.92/1.00  
% 2.92/1.00  fof(f30,plain,(
% 2.92/1.00    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 2.92/1.00    inference(nnf_transformation,[],[f15])).
% 2.92/1.00  
% 2.92/1.00  fof(f31,plain,(
% 2.92/1.00    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.92/1.00    inference(flattening,[],[f30])).
% 2.92/1.00  
% 2.92/1.00  fof(f32,plain,(
% 2.92/1.00    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK7,sK6) | ~r2_hidden(sK6,k1_relat_1(sK7))) & (k1_xboole_0 != k11_relat_1(sK7,sK6) | r2_hidden(sK6,k1_relat_1(sK7))) & v1_relat_1(sK7))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f33,plain,(
% 2.92/1.00    (k1_xboole_0 = k11_relat_1(sK7,sK6) | ~r2_hidden(sK6,k1_relat_1(sK7))) & (k1_xboole_0 != k11_relat_1(sK7,sK6) | r2_hidden(sK6,k1_relat_1(sK7))) & v1_relat_1(sK7)),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f31,f32])).
% 2.92/1.00  
% 2.92/1.00  fof(f49,plain,(
% 2.92/1.00    k1_xboole_0 != k11_relat_1(sK7,sK6) | r2_hidden(sK6,k1_relat_1(sK7))),
% 2.92/1.00    inference(cnf_transformation,[],[f33])).
% 2.92/1.00  
% 2.92/1.00  fof(f7,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f14,plain,(
% 2.92/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 2.92/1.00    inference(ennf_transformation,[],[f7])).
% 2.92/1.00  
% 2.92/1.00  fof(f29,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 2.92/1.00    inference(nnf_transformation,[],[f14])).
% 2.92/1.00  
% 2.92/1.00  fof(f47,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f29])).
% 2.92/1.00  
% 2.92/1.00  fof(f48,plain,(
% 2.92/1.00    v1_relat_1(sK7)),
% 2.92/1.00    inference(cnf_transformation,[],[f33])).
% 2.92/1.00  
% 2.92/1.00  fof(f6,axiom,(
% 2.92/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f23,plain,(
% 2.92/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.92/1.00    inference(nnf_transformation,[],[f6])).
% 2.92/1.00  
% 2.92/1.00  fof(f24,plain,(
% 2.92/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.92/1.00    inference(rectify,[],[f23])).
% 2.92/1.00  
% 2.92/1.00  fof(f27,plain,(
% 2.92/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f26,plain,(
% 2.92/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f25,plain,(
% 2.92/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f28,plain,(
% 2.92/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 2.92/1.00  
% 2.92/1.00  fof(f43,plain,(
% 2.92/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.92/1.00    inference(cnf_transformation,[],[f28])).
% 2.92/1.00  
% 2.92/1.00  fof(f51,plain,(
% 2.92/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.92/1.00    inference(equality_resolution,[],[f43])).
% 2.92/1.00  
% 2.92/1.00  fof(f50,plain,(
% 2.92/1.00    k1_xboole_0 = k11_relat_1(sK7,sK6) | ~r2_hidden(sK6,k1_relat_1(sK7))),
% 2.92/1.00    inference(cnf_transformation,[],[f33])).
% 2.92/1.00  
% 2.92/1.00  fof(f46,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f29])).
% 2.92/1.00  
% 2.92/1.00  fof(f42,plain,(
% 2.92/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.92/1.00    inference(cnf_transformation,[],[f28])).
% 2.92/1.00  
% 2.92/1.00  fof(f52,plain,(
% 2.92/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.92/1.00    inference(equality_resolution,[],[f42])).
% 2.92/1.00  
% 2.92/1.00  cnf(c_7,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1,plain,
% 2.92/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.92/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1225,plain,
% 2.92/1.00      ( r2_hidden(sK0(X0,X1),X0) | r2_hidden(sK2(X1),X1) | X1 = X0 ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_7,c_1]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2,plain,
% 2.92/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 2.92/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_5,plain,
% 2.92/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_238,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | X3 != X1 | k1_xboole_0 != X2 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_239,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_238]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3645,plain,
% 2.92/1.00      ( r2_hidden(sK2(X0),X0) | X0 = k3_xboole_0(X1,k1_xboole_0) ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_1225,c_239]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_426,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_425,plain,( X0 = X0 ),theory(equality) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2315,plain,
% 2.92/1.00      ( X0 != X1 | X1 = X0 ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_426,c_425]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4,plain,
% 2.92/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.92/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2665,plain,
% 2.92/1.00      ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_2315,c_4]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2675,plain,
% 2.92/1.00      ( X0 != k3_xboole_0(X1,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_2665,c_426]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3908,plain,
% 2.92/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_3645,c_2675]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_15,negated_conjecture,
% 2.92/1.00      ( r2_hidden(sK6,k1_relat_1(sK7)) | k1_xboole_0 != k11_relat_1(sK7,sK6) ),
% 2.92/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4096,plain,
% 2.92/1.00      ( r2_hidden(sK2(k11_relat_1(sK7,sK6)),k11_relat_1(sK7,sK6))
% 2.92/1.00      | r2_hidden(sK6,k1_relat_1(sK7)) ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_3908,c_15]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_12,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.92/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.92/1.00      | ~ v1_relat_1(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_16,negated_conjecture,
% 2.92/1.00      ( v1_relat_1(sK7) ),
% 2.92/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_264,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.92/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.92/1.00      | sK7 != X1 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_265,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k11_relat_1(sK7,X1)) | r2_hidden(k4_tarski(X1,X0),sK7) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_264]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_336,plain,
% 2.92/1.00      ( r2_hidden(k4_tarski(X1,X0),sK7) | ~ r2_hidden(X0,k11_relat_1(sK7,X1)) ),
% 2.92/1.00      inference(prop_impl,[status(thm)],[c_265]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_337,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k11_relat_1(sK7,X1)) | r2_hidden(k4_tarski(X1,X0),sK7) ),
% 2.92/1.00      inference(renaming,[status(thm)],[c_336]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1636,plain,
% 2.92/1.00      ( r2_hidden(k4_tarski(sK6,sK2(k11_relat_1(sK7,sK6))),sK7)
% 2.92/1.00      | ~ r2_hidden(sK2(k11_relat_1(sK7,sK6)),k11_relat_1(sK7,sK6)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_337]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_10,plain,
% 2.92/1.00      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3309,plain,
% 2.92/1.00      ( ~ r2_hidden(k4_tarski(sK6,sK2(k11_relat_1(sK7,sK6))),sK7)
% 2.92/1.00      | r2_hidden(sK6,k1_relat_1(sK7)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4155,plain,
% 2.92/1.00      ( r2_hidden(sK6,k1_relat_1(sK7)) ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_4096,c_1636,c_3309]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_14,negated_conjecture,
% 2.92/1.00      ( ~ r2_hidden(sK6,k1_relat_1(sK7)) | k1_xboole_0 = k11_relat_1(sK7,sK6) ),
% 2.92/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4166,plain,
% 2.92/1.00      ( k1_xboole_0 = k11_relat_1(sK7,sK6) ),
% 2.92/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_4155,c_14]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_427,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.92/1.00      theory(equality) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4392,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k11_relat_1(sK7,sK6))
% 2.92/1.00      | r2_hidden(X1,k1_xboole_0)
% 2.92/1.00      | X1 != X0 ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_4166,c_427]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_13,plain,
% 2.92/1.00      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.92/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.92/1.00      | ~ v1_relat_1(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_252,plain,
% 2.92/1.00      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.92/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.92/1.00      | sK7 != X1 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_253,plain,
% 2.92/1.00      ( r2_hidden(X0,k11_relat_1(sK7,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK7) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_252]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_338,plain,
% 2.92/1.00      ( ~ r2_hidden(k4_tarski(X1,X0),sK7) | r2_hidden(X0,k11_relat_1(sK7,X1)) ),
% 2.92/1.00      inference(prop_impl,[status(thm)],[c_253]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_339,plain,
% 2.92/1.00      ( r2_hidden(X0,k11_relat_1(sK7,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK7) ),
% 2.92/1.00      inference(renaming,[status(thm)],[c_338]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_11,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.92/1.00      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1958,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 2.92/1.00      | r2_hidden(sK5(sK7,X0),k11_relat_1(sK7,X0)) ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_339,c_11]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4832,plain,
% 2.92/1.00      ( r2_hidden(X0,k1_xboole_0)
% 2.92/1.00      | ~ r2_hidden(sK6,k1_relat_1(sK7))
% 2.92/1.00      | X0 != sK5(sK7,sK6) ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_4392,c_1958]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_790,plain,
% 2.92/1.00      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_804,plain,
% 2.92/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.92/1.00      inference(demodulation,[status(thm)],[c_790,c_4]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_876,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.92/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_804]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_6098,plain,
% 2.92/1.00      ( X0 != sK5(sK7,sK6) ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_4832,c_876,c_1636,c_3309,c_4096]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_6109,plain,
% 2.92/1.00      ( $false ),
% 2.92/1.00      inference(resolution,[status(thm)],[c_6098,c_425]) ).
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  ------                               Statistics
% 2.92/1.00  
% 2.92/1.00  ------ Selected
% 2.92/1.00  
% 2.92/1.00  total_time:                             0.233
% 2.92/1.00  
%------------------------------------------------------------------------------
