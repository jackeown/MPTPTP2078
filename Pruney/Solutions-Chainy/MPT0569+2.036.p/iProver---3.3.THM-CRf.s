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
% DateTime   : Thu Dec  3 11:47:33 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 183 expanded)
%              Number of clauses        :   59 (  65 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  351 ( 753 expanded)
%              Number of equality atoms :   95 ( 171 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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
    inference(rectify,[],[f1])).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,
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

fof(f41,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 != k10_relat_1(sK7,sK6) )
    & ( r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 = k10_relat_1(sK7,sK6) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f39,f40])).

fof(f65,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f26])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
        & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).

fof(f55,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_799,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_27208,plain,
    ( sK4(sK7,sK0(k2_relat_1(sK7),sK6)) = sK4(sK7,sK0(k2_relat_1(sK7),sK6)) ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_802,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_11904,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | X1 != k10_relat_1(sK7,sK6)
    | X0 != sK4(sK7,sK0(k2_relat_1(sK7),sK6)) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_17810,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | X0 != sK4(sK7,sK0(k2_relat_1(sK7),sK6))
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_11904])).

cnf(c_27207,plain,
    ( ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k1_xboole_0)
    | sK4(sK7,sK0(k2_relat_1(sK7),sK6)) != sK4(sK7,sK0(k2_relat_1(sK7),sK6))
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_17810])).

cnf(c_801,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1458,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k10_relat_1(sK7,X2),X3)
    | X1 != X3
    | X0 != k10_relat_1(sK7,X2) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1566,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK7,sK6),X0)
    | r1_xboole_0(k1_xboole_0,X1)
    | X1 != X0
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_1886,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK7,sK6),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X0)
    | X0 != k1_xboole_0
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_17064,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK7,sK6),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k10_relat_1(sK7,sK6))
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11905,plain,
    ( ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),X0)
    | ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | ~ r1_xboole_0(X0,k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_17061,plain,
    ( ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_11905])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1217,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,sK6)
    | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1225,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_293,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_1214,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_317,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(sK5(X0,X1,sK7),X1) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_1212,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_1228,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2614,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1228])).

cnf(c_3039,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r1_xboole_0(k2_relat_1(sK7),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_2614])).

cnf(c_3230,plain,
    ( k10_relat_1(sK7,X0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_3039])).

cnf(c_7775,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1217,c_3230])).

cnf(c_800,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2252,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_4450,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_5415,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK7,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4450])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_260,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_273,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_261,c_8])).

cnf(c_1345,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X0,sK0(X2,X1)),sK7)
    | ~ r2_hidden(sK0(X2,X1),X1) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_5215,plain,
    ( r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),sK0(k2_relat_1(sK7),sK6)),sK7)
    | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_3370,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1411,plain,
    ( r2_hidden(k4_tarski(sK4(X0,sK0(k2_relat_1(X0),X1)),sK0(k2_relat_1(X0),X1)),X0)
    | ~ r2_hidden(sK0(k2_relat_1(X0),X1),k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1796,plain,
    ( r2_hidden(k4_tarski(sK4(sK7,sK0(k2_relat_1(sK7),X0)),sK0(k2_relat_1(sK7),X0)),sK7)
    | ~ r2_hidden(sK0(k2_relat_1(sK7),X0),k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_2813,plain,
    ( r2_hidden(k4_tarski(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),sK0(k2_relat_1(sK7),sK6)),sK7)
    | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1887,plain,
    ( r1_xboole_0(k10_relat_1(sK7,sK6),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_155,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_407,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k2_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_155])).

cnf(c_408,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
    | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_397,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k2_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_155])).

cnf(c_398,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27208,c_27207,c_17064,c_17061,c_7775,c_5415,c_5215,c_3370,c_2813,c_1887,c_408,c_398])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.93/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/1.49  
% 7.93/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.93/1.49  
% 7.93/1.49  ------  iProver source info
% 7.93/1.49  
% 7.93/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.93/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.93/1.49  git: non_committed_changes: false
% 7.93/1.49  git: last_make_outside_of_git: false
% 7.93/1.49  
% 7.93/1.49  ------ 
% 7.93/1.49  
% 7.93/1.49  ------ Input Options
% 7.93/1.49  
% 7.93/1.49  --out_options                           all
% 7.93/1.49  --tptp_safe_out                         true
% 7.93/1.49  --problem_path                          ""
% 7.93/1.49  --include_path                          ""
% 7.93/1.49  --clausifier                            res/vclausify_rel
% 7.93/1.49  --clausifier_options                    --mode clausify
% 7.93/1.49  --stdin                                 false
% 7.93/1.49  --stats_out                             all
% 7.93/1.49  
% 7.93/1.49  ------ General Options
% 7.93/1.49  
% 7.93/1.49  --fof                                   false
% 7.93/1.49  --time_out_real                         305.
% 7.93/1.49  --time_out_virtual                      -1.
% 7.93/1.49  --symbol_type_check                     false
% 7.93/1.49  --clausify_out                          false
% 7.93/1.49  --sig_cnt_out                           false
% 7.93/1.49  --trig_cnt_out                          false
% 7.93/1.49  --trig_cnt_out_tolerance                1.
% 7.93/1.49  --trig_cnt_out_sk_spl                   false
% 7.93/1.49  --abstr_cl_out                          false
% 7.93/1.49  
% 7.93/1.49  ------ Global Options
% 7.93/1.49  
% 7.93/1.49  --schedule                              default
% 7.93/1.49  --add_important_lit                     false
% 7.93/1.49  --prop_solver_per_cl                    1000
% 7.93/1.49  --min_unsat_core                        false
% 7.93/1.49  --soft_assumptions                      false
% 7.93/1.49  --soft_lemma_size                       3
% 7.93/1.49  --prop_impl_unit_size                   0
% 7.93/1.49  --prop_impl_unit                        []
% 7.93/1.49  --share_sel_clauses                     true
% 7.93/1.49  --reset_solvers                         false
% 7.93/1.49  --bc_imp_inh                            [conj_cone]
% 7.93/1.49  --conj_cone_tolerance                   3.
% 7.93/1.49  --extra_neg_conj                        none
% 7.93/1.49  --large_theory_mode                     true
% 7.93/1.49  --prolific_symb_bound                   200
% 7.93/1.49  --lt_threshold                          2000
% 7.93/1.49  --clause_weak_htbl                      true
% 7.93/1.49  --gc_record_bc_elim                     false
% 7.93/1.49  
% 7.93/1.49  ------ Preprocessing Options
% 7.93/1.49  
% 7.93/1.49  --preprocessing_flag                    true
% 7.93/1.49  --time_out_prep_mult                    0.1
% 7.93/1.49  --splitting_mode                        input
% 7.93/1.49  --splitting_grd                         true
% 7.93/1.49  --splitting_cvd                         false
% 7.93/1.49  --splitting_cvd_svl                     false
% 7.93/1.49  --splitting_nvd                         32
% 7.93/1.49  --sub_typing                            true
% 7.93/1.49  --prep_gs_sim                           true
% 7.93/1.49  --prep_unflatten                        true
% 7.93/1.49  --prep_res_sim                          true
% 7.93/1.49  --prep_upred                            true
% 7.93/1.49  --prep_sem_filter                       exhaustive
% 7.93/1.49  --prep_sem_filter_out                   false
% 7.93/1.49  --pred_elim                             true
% 7.93/1.49  --res_sim_input                         true
% 7.93/1.49  --eq_ax_congr_red                       true
% 7.93/1.49  --pure_diseq_elim                       true
% 7.93/1.49  --brand_transform                       false
% 7.93/1.49  --non_eq_to_eq                          false
% 7.93/1.49  --prep_def_merge                        true
% 7.93/1.49  --prep_def_merge_prop_impl              false
% 7.93/1.49  --prep_def_merge_mbd                    true
% 7.93/1.49  --prep_def_merge_tr_red                 false
% 7.93/1.49  --prep_def_merge_tr_cl                  false
% 7.93/1.49  --smt_preprocessing                     true
% 7.93/1.49  --smt_ac_axioms                         fast
% 7.93/1.49  --preprocessed_out                      false
% 7.93/1.49  --preprocessed_stats                    false
% 7.93/1.49  
% 7.93/1.49  ------ Abstraction refinement Options
% 7.93/1.49  
% 7.93/1.49  --abstr_ref                             []
% 7.93/1.49  --abstr_ref_prep                        false
% 7.93/1.49  --abstr_ref_until_sat                   false
% 7.93/1.49  --abstr_ref_sig_restrict                funpre
% 7.93/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.93/1.49  --abstr_ref_under                       []
% 7.93/1.49  
% 7.93/1.49  ------ SAT Options
% 7.93/1.49  
% 7.93/1.49  --sat_mode                              false
% 7.93/1.49  --sat_fm_restart_options                ""
% 7.93/1.49  --sat_gr_def                            false
% 7.93/1.49  --sat_epr_types                         true
% 7.93/1.49  --sat_non_cyclic_types                  false
% 7.93/1.49  --sat_finite_models                     false
% 7.93/1.49  --sat_fm_lemmas                         false
% 7.93/1.49  --sat_fm_prep                           false
% 7.93/1.49  --sat_fm_uc_incr                        true
% 7.93/1.49  --sat_out_model                         small
% 7.93/1.49  --sat_out_clauses                       false
% 7.93/1.49  
% 7.93/1.49  ------ QBF Options
% 7.93/1.49  
% 7.93/1.49  --qbf_mode                              false
% 7.93/1.49  --qbf_elim_univ                         false
% 7.93/1.49  --qbf_dom_inst                          none
% 7.93/1.49  --qbf_dom_pre_inst                      false
% 7.93/1.49  --qbf_sk_in                             false
% 7.93/1.49  --qbf_pred_elim                         true
% 7.93/1.49  --qbf_split                             512
% 7.93/1.49  
% 7.93/1.49  ------ BMC1 Options
% 7.93/1.49  
% 7.93/1.49  --bmc1_incremental                      false
% 7.93/1.49  --bmc1_axioms                           reachable_all
% 7.93/1.49  --bmc1_min_bound                        0
% 7.93/1.49  --bmc1_max_bound                        -1
% 7.93/1.49  --bmc1_max_bound_default                -1
% 7.93/1.49  --bmc1_symbol_reachability              true
% 7.93/1.49  --bmc1_property_lemmas                  false
% 7.93/1.49  --bmc1_k_induction                      false
% 7.93/1.49  --bmc1_non_equiv_states                 false
% 7.93/1.49  --bmc1_deadlock                         false
% 7.93/1.49  --bmc1_ucm                              false
% 7.93/1.49  --bmc1_add_unsat_core                   none
% 7.93/1.49  --bmc1_unsat_core_children              false
% 7.93/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.93/1.49  --bmc1_out_stat                         full
% 7.93/1.49  --bmc1_ground_init                      false
% 7.93/1.49  --bmc1_pre_inst_next_state              false
% 7.93/1.49  --bmc1_pre_inst_state                   false
% 7.93/1.49  --bmc1_pre_inst_reach_state             false
% 7.93/1.49  --bmc1_out_unsat_core                   false
% 7.93/1.49  --bmc1_aig_witness_out                  false
% 7.93/1.49  --bmc1_verbose                          false
% 7.93/1.49  --bmc1_dump_clauses_tptp                false
% 7.93/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.93/1.49  --bmc1_dump_file                        -
% 7.93/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.93/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.93/1.49  --bmc1_ucm_extend_mode                  1
% 7.93/1.49  --bmc1_ucm_init_mode                    2
% 7.93/1.49  --bmc1_ucm_cone_mode                    none
% 7.93/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.93/1.49  --bmc1_ucm_relax_model                  4
% 7.93/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.93/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.93/1.49  --bmc1_ucm_layered_model                none
% 7.93/1.49  --bmc1_ucm_max_lemma_size               10
% 7.93/1.49  
% 7.93/1.49  ------ AIG Options
% 7.93/1.49  
% 7.93/1.49  --aig_mode                              false
% 7.93/1.49  
% 7.93/1.49  ------ Instantiation Options
% 7.93/1.49  
% 7.93/1.49  --instantiation_flag                    true
% 7.93/1.49  --inst_sos_flag                         false
% 7.93/1.49  --inst_sos_phase                        true
% 7.93/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.93/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.93/1.49  --inst_lit_sel_side                     num_symb
% 7.93/1.49  --inst_solver_per_active                1400
% 7.93/1.49  --inst_solver_calls_frac                1.
% 7.93/1.49  --inst_passive_queue_type               priority_queues
% 7.93/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.93/1.49  --inst_passive_queues_freq              [25;2]
% 7.93/1.49  --inst_dismatching                      true
% 7.93/1.49  --inst_eager_unprocessed_to_passive     true
% 7.93/1.49  --inst_prop_sim_given                   true
% 7.93/1.49  --inst_prop_sim_new                     false
% 7.93/1.49  --inst_subs_new                         false
% 7.93/1.49  --inst_eq_res_simp                      false
% 7.93/1.49  --inst_subs_given                       false
% 7.93/1.49  --inst_orphan_elimination               true
% 7.93/1.49  --inst_learning_loop_flag               true
% 7.93/1.49  --inst_learning_start                   3000
% 7.93/1.49  --inst_learning_factor                  2
% 7.93/1.49  --inst_start_prop_sim_after_learn       3
% 7.93/1.49  --inst_sel_renew                        solver
% 7.93/1.49  --inst_lit_activity_flag                true
% 7.93/1.49  --inst_restr_to_given                   false
% 7.93/1.49  --inst_activity_threshold               500
% 7.93/1.49  --inst_out_proof                        true
% 7.93/1.49  
% 7.93/1.49  ------ Resolution Options
% 7.93/1.49  
% 7.93/1.49  --resolution_flag                       true
% 7.93/1.49  --res_lit_sel                           adaptive
% 7.93/1.49  --res_lit_sel_side                      none
% 7.93/1.49  --res_ordering                          kbo
% 7.93/1.49  --res_to_prop_solver                    active
% 7.93/1.49  --res_prop_simpl_new                    false
% 7.93/1.49  --res_prop_simpl_given                  true
% 7.93/1.49  --res_passive_queue_type                priority_queues
% 7.93/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.93/1.49  --res_passive_queues_freq               [15;5]
% 7.93/1.49  --res_forward_subs                      full
% 7.93/1.49  --res_backward_subs                     full
% 7.93/1.49  --res_forward_subs_resolution           true
% 7.93/1.49  --res_backward_subs_resolution          true
% 7.93/1.49  --res_orphan_elimination                true
% 7.93/1.49  --res_time_limit                        2.
% 7.93/1.49  --res_out_proof                         true
% 7.93/1.49  
% 7.93/1.49  ------ Superposition Options
% 7.93/1.49  
% 7.93/1.49  --superposition_flag                    true
% 7.93/1.49  --sup_passive_queue_type                priority_queues
% 7.93/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.93/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.93/1.49  --demod_completeness_check              fast
% 7.93/1.49  --demod_use_ground                      true
% 7.93/1.49  --sup_to_prop_solver                    passive
% 7.93/1.49  --sup_prop_simpl_new                    true
% 7.93/1.49  --sup_prop_simpl_given                  true
% 7.93/1.49  --sup_fun_splitting                     false
% 7.93/1.49  --sup_smt_interval                      50000
% 7.93/1.49  
% 7.93/1.49  ------ Superposition Simplification Setup
% 7.93/1.49  
% 7.93/1.49  --sup_indices_passive                   []
% 7.93/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.93/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.93/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.93/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.93/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.93/1.49  --sup_full_bw                           [BwDemod]
% 7.93/1.49  --sup_immed_triv                        [TrivRules]
% 7.93/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.93/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.93/1.49  --sup_immed_bw_main                     []
% 7.93/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.93/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.93/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.93/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.93/1.49  
% 7.93/1.49  ------ Combination Options
% 7.93/1.49  
% 7.93/1.49  --comb_res_mult                         3
% 7.93/1.49  --comb_sup_mult                         2
% 7.93/1.49  --comb_inst_mult                        10
% 7.93/1.49  
% 7.93/1.49  ------ Debug Options
% 7.93/1.49  
% 7.93/1.49  --dbg_backtrace                         false
% 7.93/1.49  --dbg_dump_prop_clauses                 false
% 7.93/1.49  --dbg_dump_prop_clauses_file            -
% 7.93/1.49  --dbg_out_stat                          false
% 7.93/1.49  ------ Parsing...
% 7.93/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.93/1.49  
% 7.93/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.93/1.49  
% 7.93/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.93/1.49  
% 7.93/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.93/1.49  ------ Proving...
% 7.93/1.49  ------ Problem Properties 
% 7.93/1.49  
% 7.93/1.49  
% 7.93/1.49  clauses                                 17
% 7.93/1.49  conjectures                             2
% 7.93/1.49  EPR                                     2
% 7.93/1.49  Horn                                    12
% 7.93/1.49  unary                                   1
% 7.93/1.49  binary                                  12
% 7.93/1.49  lits                                    37
% 7.93/1.49  lits eq                                 5
% 7.93/1.49  fd_pure                                 0
% 7.93/1.49  fd_pseudo                               0
% 7.93/1.49  fd_cond                                 1
% 7.93/1.49  fd_pseudo_cond                          2
% 7.93/1.49  AC symbols                              0
% 7.93/1.49  
% 7.93/1.49  ------ Schedule dynamic 5 is on 
% 7.93/1.49  
% 7.93/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.93/1.49  
% 7.93/1.49  
% 7.93/1.49  ------ 
% 7.93/1.49  Current options:
% 7.93/1.49  ------ 
% 7.93/1.49  
% 7.93/1.49  ------ Input Options
% 7.93/1.49  
% 7.93/1.49  --out_options                           all
% 7.93/1.49  --tptp_safe_out                         true
% 7.93/1.49  --problem_path                          ""
% 7.93/1.49  --include_path                          ""
% 7.93/1.49  --clausifier                            res/vclausify_rel
% 7.93/1.49  --clausifier_options                    --mode clausify
% 7.93/1.49  --stdin                                 false
% 7.93/1.49  --stats_out                             all
% 7.93/1.49  
% 7.93/1.49  ------ General Options
% 7.93/1.49  
% 7.93/1.49  --fof                                   false
% 7.93/1.49  --time_out_real                         305.
% 7.93/1.49  --time_out_virtual                      -1.
% 7.93/1.49  --symbol_type_check                     false
% 7.93/1.49  --clausify_out                          false
% 7.93/1.49  --sig_cnt_out                           false
% 7.93/1.49  --trig_cnt_out                          false
% 7.93/1.49  --trig_cnt_out_tolerance                1.
% 7.93/1.49  --trig_cnt_out_sk_spl                   false
% 7.93/1.49  --abstr_cl_out                          false
% 7.93/1.49  
% 7.93/1.49  ------ Global Options
% 7.93/1.49  
% 7.93/1.49  --schedule                              default
% 7.93/1.49  --add_important_lit                     false
% 7.93/1.49  --prop_solver_per_cl                    1000
% 7.93/1.49  --min_unsat_core                        false
% 7.93/1.49  --soft_assumptions                      false
% 7.93/1.49  --soft_lemma_size                       3
% 7.93/1.49  --prop_impl_unit_size                   0
% 7.93/1.49  --prop_impl_unit                        []
% 7.93/1.49  --share_sel_clauses                     true
% 7.93/1.49  --reset_solvers                         false
% 7.93/1.49  --bc_imp_inh                            [conj_cone]
% 7.93/1.49  --conj_cone_tolerance                   3.
% 7.93/1.49  --extra_neg_conj                        none
% 7.93/1.49  --large_theory_mode                     true
% 7.93/1.49  --prolific_symb_bound                   200
% 7.93/1.49  --lt_threshold                          2000
% 7.93/1.49  --clause_weak_htbl                      true
% 7.93/1.49  --gc_record_bc_elim                     false
% 7.93/1.49  
% 7.93/1.49  ------ Preprocessing Options
% 7.93/1.49  
% 7.93/1.49  --preprocessing_flag                    true
% 7.93/1.49  --time_out_prep_mult                    0.1
% 7.93/1.49  --splitting_mode                        input
% 7.93/1.49  --splitting_grd                         true
% 7.93/1.49  --splitting_cvd                         false
% 7.93/1.49  --splitting_cvd_svl                     false
% 7.93/1.49  --splitting_nvd                         32
% 7.93/1.49  --sub_typing                            true
% 7.93/1.49  --prep_gs_sim                           true
% 7.93/1.49  --prep_unflatten                        true
% 7.93/1.49  --prep_res_sim                          true
% 7.93/1.49  --prep_upred                            true
% 7.93/1.49  --prep_sem_filter                       exhaustive
% 7.93/1.49  --prep_sem_filter_out                   false
% 7.93/1.49  --pred_elim                             true
% 7.93/1.49  --res_sim_input                         true
% 7.93/1.49  --eq_ax_congr_red                       true
% 7.93/1.49  --pure_diseq_elim                       true
% 7.93/1.49  --brand_transform                       false
% 7.93/1.49  --non_eq_to_eq                          false
% 7.93/1.49  --prep_def_merge                        true
% 7.93/1.49  --prep_def_merge_prop_impl              false
% 7.93/1.49  --prep_def_merge_mbd                    true
% 7.93/1.49  --prep_def_merge_tr_red                 false
% 7.93/1.49  --prep_def_merge_tr_cl                  false
% 7.93/1.49  --smt_preprocessing                     true
% 7.93/1.49  --smt_ac_axioms                         fast
% 7.93/1.49  --preprocessed_out                      false
% 7.93/1.49  --preprocessed_stats                    false
% 7.93/1.49  
% 7.93/1.49  ------ Abstraction refinement Options
% 7.93/1.49  
% 7.93/1.49  --abstr_ref                             []
% 7.93/1.49  --abstr_ref_prep                        false
% 7.93/1.49  --abstr_ref_until_sat                   false
% 7.93/1.49  --abstr_ref_sig_restrict                funpre
% 7.93/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.93/1.49  --abstr_ref_under                       []
% 7.93/1.49  
% 7.93/1.49  ------ SAT Options
% 7.93/1.49  
% 7.93/1.49  --sat_mode                              false
% 7.93/1.49  --sat_fm_restart_options                ""
% 7.93/1.49  --sat_gr_def                            false
% 7.93/1.49  --sat_epr_types                         true
% 7.93/1.49  --sat_non_cyclic_types                  false
% 7.93/1.49  --sat_finite_models                     false
% 7.93/1.49  --sat_fm_lemmas                         false
% 7.93/1.49  --sat_fm_prep                           false
% 7.93/1.49  --sat_fm_uc_incr                        true
% 7.93/1.49  --sat_out_model                         small
% 7.93/1.49  --sat_out_clauses                       false
% 7.93/1.49  
% 7.93/1.49  ------ QBF Options
% 7.93/1.49  
% 7.93/1.49  --qbf_mode                              false
% 7.93/1.49  --qbf_elim_univ                         false
% 7.93/1.49  --qbf_dom_inst                          none
% 7.93/1.49  --qbf_dom_pre_inst                      false
% 7.93/1.49  --qbf_sk_in                             false
% 7.93/1.49  --qbf_pred_elim                         true
% 7.93/1.49  --qbf_split                             512
% 7.93/1.49  
% 7.93/1.49  ------ BMC1 Options
% 7.93/1.49  
% 7.93/1.49  --bmc1_incremental                      false
% 7.93/1.49  --bmc1_axioms                           reachable_all
% 7.93/1.49  --bmc1_min_bound                        0
% 7.93/1.49  --bmc1_max_bound                        -1
% 7.93/1.49  --bmc1_max_bound_default                -1
% 7.93/1.49  --bmc1_symbol_reachability              true
% 7.93/1.49  --bmc1_property_lemmas                  false
% 7.93/1.49  --bmc1_k_induction                      false
% 7.93/1.49  --bmc1_non_equiv_states                 false
% 7.93/1.49  --bmc1_deadlock                         false
% 7.93/1.49  --bmc1_ucm                              false
% 7.93/1.49  --bmc1_add_unsat_core                   none
% 7.93/1.49  --bmc1_unsat_core_children              false
% 7.93/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.93/1.49  --bmc1_out_stat                         full
% 7.93/1.49  --bmc1_ground_init                      false
% 7.93/1.49  --bmc1_pre_inst_next_state              false
% 7.93/1.49  --bmc1_pre_inst_state                   false
% 7.93/1.49  --bmc1_pre_inst_reach_state             false
% 7.93/1.49  --bmc1_out_unsat_core                   false
% 7.93/1.49  --bmc1_aig_witness_out                  false
% 7.93/1.49  --bmc1_verbose                          false
% 7.93/1.49  --bmc1_dump_clauses_tptp                false
% 7.93/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.93/1.49  --bmc1_dump_file                        -
% 7.93/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.93/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.93/1.49  --bmc1_ucm_extend_mode                  1
% 7.93/1.49  --bmc1_ucm_init_mode                    2
% 7.93/1.49  --bmc1_ucm_cone_mode                    none
% 7.93/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.93/1.49  --bmc1_ucm_relax_model                  4
% 7.93/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.93/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.93/1.49  --bmc1_ucm_layered_model                none
% 7.93/1.49  --bmc1_ucm_max_lemma_size               10
% 7.93/1.49  
% 7.93/1.49  ------ AIG Options
% 7.93/1.49  
% 7.93/1.49  --aig_mode                              false
% 7.93/1.49  
% 7.93/1.49  ------ Instantiation Options
% 7.93/1.49  
% 7.93/1.49  --instantiation_flag                    true
% 7.93/1.49  --inst_sos_flag                         false
% 7.93/1.49  --inst_sos_phase                        true
% 7.93/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.93/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.93/1.49  --inst_lit_sel_side                     none
% 7.93/1.49  --inst_solver_per_active                1400
% 7.93/1.49  --inst_solver_calls_frac                1.
% 7.93/1.49  --inst_passive_queue_type               priority_queues
% 7.93/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.93/1.49  --inst_passive_queues_freq              [25;2]
% 7.93/1.49  --inst_dismatching                      true
% 7.93/1.49  --inst_eager_unprocessed_to_passive     true
% 7.93/1.49  --inst_prop_sim_given                   true
% 7.93/1.49  --inst_prop_sim_new                     false
% 7.93/1.49  --inst_subs_new                         false
% 7.93/1.49  --inst_eq_res_simp                      false
% 7.93/1.49  --inst_subs_given                       false
% 7.93/1.49  --inst_orphan_elimination               true
% 7.93/1.49  --inst_learning_loop_flag               true
% 7.93/1.49  --inst_learning_start                   3000
% 7.93/1.49  --inst_learning_factor                  2
% 7.93/1.49  --inst_start_prop_sim_after_learn       3
% 7.93/1.49  --inst_sel_renew                        solver
% 7.93/1.49  --inst_lit_activity_flag                true
% 7.93/1.49  --inst_restr_to_given                   false
% 7.93/1.49  --inst_activity_threshold               500
% 7.93/1.49  --inst_out_proof                        true
% 7.93/1.49  
% 7.93/1.49  ------ Resolution Options
% 7.93/1.49  
% 7.93/1.49  --resolution_flag                       false
% 7.93/1.49  --res_lit_sel                           adaptive
% 7.93/1.49  --res_lit_sel_side                      none
% 7.93/1.49  --res_ordering                          kbo
% 7.93/1.49  --res_to_prop_solver                    active
% 7.93/1.49  --res_prop_simpl_new                    false
% 7.93/1.49  --res_prop_simpl_given                  true
% 7.93/1.49  --res_passive_queue_type                priority_queues
% 7.93/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.93/1.49  --res_passive_queues_freq               [15;5]
% 7.93/1.49  --res_forward_subs                      full
% 7.93/1.49  --res_backward_subs                     full
% 7.93/1.49  --res_forward_subs_resolution           true
% 7.93/1.49  --res_backward_subs_resolution          true
% 7.93/1.49  --res_orphan_elimination                true
% 7.93/1.49  --res_time_limit                        2.
% 7.93/1.49  --res_out_proof                         true
% 7.93/1.49  
% 7.93/1.49  ------ Superposition Options
% 7.93/1.49  
% 7.93/1.49  --superposition_flag                    true
% 7.93/1.49  --sup_passive_queue_type                priority_queues
% 7.93/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.93/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.93/1.49  --demod_completeness_check              fast
% 7.93/1.49  --demod_use_ground                      true
% 7.93/1.49  --sup_to_prop_solver                    passive
% 7.93/1.49  --sup_prop_simpl_new                    true
% 7.93/1.49  --sup_prop_simpl_given                  true
% 7.93/1.49  --sup_fun_splitting                     false
% 7.93/1.49  --sup_smt_interval                      50000
% 7.93/1.49  
% 7.93/1.49  ------ Superposition Simplification Setup
% 7.93/1.49  
% 7.93/1.49  --sup_indices_passive                   []
% 7.93/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.93/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.93/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.93/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.93/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.93/1.49  --sup_full_bw                           [BwDemod]
% 7.93/1.49  --sup_immed_triv                        [TrivRules]
% 7.93/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.93/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.93/1.49  --sup_immed_bw_main                     []
% 7.93/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.93/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.93/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.93/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.93/1.49  
% 7.93/1.49  ------ Combination Options
% 7.93/1.49  
% 7.93/1.49  --comb_res_mult                         3
% 7.93/1.49  --comb_sup_mult                         2
% 7.93/1.49  --comb_inst_mult                        10
% 7.93/1.49  
% 7.93/1.49  ------ Debug Options
% 7.93/1.49  
% 7.93/1.49  --dbg_backtrace                         false
% 7.93/1.49  --dbg_dump_prop_clauses                 false
% 7.93/1.49  --dbg_dump_prop_clauses_file            -
% 7.93/1.49  --dbg_out_stat                          false
% 7.93/1.49  
% 7.93/1.49  
% 7.93/1.49  
% 7.93/1.49  
% 7.93/1.49  ------ Proving...
% 7.93/1.49  
% 7.93/1.49  
% 7.93/1.49  % SZS status Theorem for theBenchmark.p
% 7.93/1.49  
% 7.93/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.93/1.49  
% 7.93/1.49  fof(f1,axiom,(
% 7.93/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.93/1.49  
% 7.93/1.49  fof(f16,plain,(
% 7.93/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.93/1.49    inference(rectify,[],[f1])).
% 7.93/1.49  
% 7.93/1.49  fof(f17,plain,(
% 7.93/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.93/1.49    inference(ennf_transformation,[],[f16])).
% 7.93/1.49  
% 7.93/1.49  fof(f24,plain,(
% 7.93/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.93/1.49    introduced(choice_axiom,[])).
% 7.93/1.49  
% 7.93/1.49  fof(f25,plain,(
% 7.93/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).
% 7.93/1.49  
% 7.93/1.49  fof(f44,plain,(
% 7.93/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.93/1.49    inference(cnf_transformation,[],[f25])).
% 7.93/1.49  
% 7.93/1.49  fof(f14,conjecture,(
% 7.93/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.93/1.49  
% 7.93/1.49  fof(f15,negated_conjecture,(
% 7.93/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.93/1.49    inference(negated_conjecture,[],[f14])).
% 7.93/1.49  
% 7.93/1.49  fof(f23,plain,(
% 7.93/1.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 7.93/1.49    inference(ennf_transformation,[],[f15])).
% 7.93/1.49  
% 7.93/1.49  fof(f38,plain,(
% 7.93/1.49    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.93/1.49    inference(nnf_transformation,[],[f23])).
% 7.93/1.49  
% 7.93/1.49  fof(f39,plain,(
% 7.93/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.93/1.49    inference(flattening,[],[f38])).
% 7.93/1.49  
% 7.93/1.49  fof(f40,plain,(
% 7.93/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7))),
% 7.93/1.49    introduced(choice_axiom,[])).
% 7.93/1.49  
% 7.93/1.49  fof(f41,plain,(
% 7.93/1.49    (~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7)),
% 7.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f39,f40])).
% 7.93/1.49  
% 7.93/1.49  fof(f65,plain,(
% 7.93/1.49    r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)),
% 7.93/1.49    inference(cnf_transformation,[],[f41])).
% 7.93/1.49  
% 7.93/1.49  fof(f2,axiom,(
% 7.93/1.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.93/1.49  
% 7.93/1.49  fof(f18,plain,(
% 7.93/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.93/1.49    inference(ennf_transformation,[],[f2])).
% 7.93/1.49  
% 7.93/1.49  fof(f26,plain,(
% 7.93/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.93/1.49    introduced(choice_axiom,[])).
% 7.93/1.49  
% 7.93/1.49  fof(f27,plain,(
% 7.93/1.49    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f26])).
% 7.93/1.49  
% 7.93/1.49  fof(f45,plain,(
% 7.93/1.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.93/1.49    inference(cnf_transformation,[],[f27])).
% 7.93/1.49  
% 7.93/1.49  fof(f12,axiom,(
% 7.93/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 7.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.93/1.49  
% 7.93/1.49  fof(f20,plain,(
% 7.93/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.93/1.49    inference(ennf_transformation,[],[f12])).
% 7.93/1.49  
% 7.93/1.49  fof(f34,plain,(
% 7.93/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.93/1.49    inference(nnf_transformation,[],[f20])).
% 7.93/1.49  
% 7.93/1.49  fof(f35,plain,(
% 7.93/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.93/1.49    inference(rectify,[],[f34])).
% 7.93/1.49  
% 7.93/1.49  fof(f36,plain,(
% 7.93/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))))),
% 7.93/1.49    introduced(choice_axiom,[])).
% 7.93/1.49  
% 7.93/1.49  fof(f37,plain,(
% 7.93/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 7.93/1.49  
% 7.93/1.49  fof(f58,plain,(
% 7.93/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.93/1.49    inference(cnf_transformation,[],[f37])).
% 7.93/1.49  
% 7.93/1.49  fof(f64,plain,(
% 7.93/1.49    v1_relat_1(sK7)),
% 7.93/1.49    inference(cnf_transformation,[],[f41])).
% 7.93/1.49  
% 7.93/1.49  fof(f60,plain,(
% 7.93/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.93/1.49    inference(cnf_transformation,[],[f37])).
% 7.93/1.49  
% 7.93/1.49  fof(f61,plain,(
% 7.93/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 7.93/1.49    inference(cnf_transformation,[],[f37])).
% 7.93/1.49  
% 7.93/1.49  fof(f11,axiom,(
% 7.93/1.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.93/1.49  
% 7.93/1.49  fof(f28,plain,(
% 7.93/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.93/1.49    inference(nnf_transformation,[],[f11])).
% 7.93/1.49  
% 7.93/1.49  fof(f29,plain,(
% 7.93/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.93/1.49    inference(rectify,[],[f28])).
% 7.93/1.49  
% 7.93/1.49  fof(f32,plain,(
% 7.93/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 7.93/1.49    introduced(choice_axiom,[])).
% 7.93/1.49  
% 7.93/1.49  fof(f31,plain,(
% 7.93/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0))) )),
% 7.93/1.49    introduced(choice_axiom,[])).
% 7.93/1.49  
% 7.93/1.49  fof(f30,plain,(
% 7.93/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.93/1.49    introduced(choice_axiom,[])).
% 7.93/1.49  
% 7.93/1.49  fof(f33,plain,(
% 7.93/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).
% 7.93/1.49  
% 7.93/1.49  fof(f55,plain,(
% 7.93/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 7.93/1.49    inference(cnf_transformation,[],[f33])).
% 7.93/1.49  
% 7.93/1.49  fof(f73,plain,(
% 7.93/1.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 7.93/1.49    inference(equality_resolution,[],[f55])).
% 7.93/1.49  
% 7.93/1.49  fof(f54,plain,(
% 7.93/1.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 7.93/1.49    inference(cnf_transformation,[],[f33])).
% 7.93/1.49  
% 7.93/1.49  fof(f74,plain,(
% 7.93/1.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 7.93/1.49    inference(equality_resolution,[],[f54])).
% 7.93/1.49  
% 7.93/1.49  fof(f3,axiom,(
% 7.93/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.93/1.49  
% 7.93/1.49  fof(f46,plain,(
% 7.93/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.93/1.49    inference(cnf_transformation,[],[f3])).
% 7.93/1.49  
% 7.93/1.49  fof(f43,plain,(
% 7.93/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.93/1.49    inference(cnf_transformation,[],[f25])).
% 7.93/1.49  
% 7.93/1.49  fof(f66,plain,(
% 7.93/1.49    ~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)),
% 7.93/1.49    inference(cnf_transformation,[],[f41])).
% 7.93/1.49  
% 7.93/1.49  fof(f42,plain,(
% 7.93/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.93/1.49    inference(cnf_transformation,[],[f25])).
% 7.93/1.49  
% 7.93/1.49  cnf(c_799,plain,( X0 = X0 ),theory(equality) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_27208,plain,
% 7.93/1.49      ( sK4(sK7,sK0(k2_relat_1(sK7),sK6)) = sK4(sK7,sK0(k2_relat_1(sK7),sK6)) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_799]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_802,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.93/1.49      theory(equality) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_11904,plain,
% 7.93/1.49      ( r2_hidden(X0,X1)
% 7.93/1.49      | ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
% 7.93/1.49      | X1 != k10_relat_1(sK7,sK6)
% 7.93/1.49      | X0 != sK4(sK7,sK0(k2_relat_1(sK7),sK6)) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_802]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_17810,plain,
% 7.93/1.49      ( r2_hidden(X0,k1_xboole_0)
% 7.93/1.49      | ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
% 7.93/1.49      | X0 != sK4(sK7,sK0(k2_relat_1(sK7),sK6))
% 7.93/1.49      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_11904]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_27207,plain,
% 7.93/1.49      ( ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
% 7.93/1.49      | r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k1_xboole_0)
% 7.93/1.49      | sK4(sK7,sK0(k2_relat_1(sK7),sK6)) != sK4(sK7,sK0(k2_relat_1(sK7),sK6))
% 7.93/1.49      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_17810]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_801,plain,
% 7.93/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.93/1.49      theory(equality) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1458,plain,
% 7.93/1.49      ( r1_xboole_0(X0,X1)
% 7.93/1.49      | ~ r1_xboole_0(k10_relat_1(sK7,X2),X3)
% 7.93/1.49      | X1 != X3
% 7.93/1.49      | X0 != k10_relat_1(sK7,X2) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_801]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1566,plain,
% 7.93/1.49      ( ~ r1_xboole_0(k10_relat_1(sK7,sK6),X0)
% 7.93/1.49      | r1_xboole_0(k1_xboole_0,X1)
% 7.93/1.49      | X1 != X0
% 7.93/1.49      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_1458]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1886,plain,
% 7.93/1.49      ( ~ r1_xboole_0(k10_relat_1(sK7,sK6),k1_xboole_0)
% 7.93/1.49      | r1_xboole_0(k1_xboole_0,X0)
% 7.93/1.49      | X0 != k1_xboole_0
% 7.93/1.49      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_1566]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_17064,plain,
% 7.93/1.49      ( ~ r1_xboole_0(k10_relat_1(sK7,sK6),k1_xboole_0)
% 7.93/1.49      | r1_xboole_0(k1_xboole_0,k10_relat_1(sK7,sK6))
% 7.93/1.49      | k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.93/1.49      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_1886]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_0,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.93/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_11905,plain,
% 7.93/1.49      ( ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),X0)
% 7.93/1.49      | ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
% 7.93/1.49      | ~ r1_xboole_0(X0,k10_relat_1(sK7,sK6)) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_17061,plain,
% 7.93/1.49      ( ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
% 7.93/1.49      | ~ r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k1_xboole_0)
% 7.93/1.49      | ~ r1_xboole_0(k1_xboole_0,k10_relat_1(sK7,sK6)) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_11905]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_17,negated_conjecture,
% 7.93/1.49      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.93/1.49      | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
% 7.93/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1217,plain,
% 7.93/1.49      ( k1_xboole_0 = k10_relat_1(sK7,sK6)
% 7.93/1.49      | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
% 7.93/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_3,plain,
% 7.93/1.49      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.93/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1225,plain,
% 7.93/1.49      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 7.93/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_13,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.93/1.49      | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
% 7.93/1.49      | ~ v1_relat_1(X1) ),
% 7.93/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_18,negated_conjecture,
% 7.93/1.49      ( v1_relat_1(sK7) ),
% 7.93/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_292,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.93/1.49      | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
% 7.93/1.49      | sK7 != X1 ),
% 7.93/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_293,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
% 7.93/1.49      | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) ),
% 7.93/1.49      inference(unflattening,[status(thm)],[c_292]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1214,plain,
% 7.93/1.49      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.93/1.49      | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) = iProver_top ),
% 7.93/1.49      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_11,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.93/1.49      | r2_hidden(sK5(X0,X2,X1),X2)
% 7.93/1.49      | ~ v1_relat_1(X1) ),
% 7.93/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_316,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.93/1.49      | r2_hidden(sK5(X0,X2,X1),X2)
% 7.93/1.49      | sK7 != X1 ),
% 7.93/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_317,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
% 7.93/1.49      | r2_hidden(sK5(X0,X1,sK7),X1) ),
% 7.93/1.49      inference(unflattening,[status(thm)],[c_316]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1212,plain,
% 7.93/1.49      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.93/1.49      | r2_hidden(sK5(X0,X1,sK7),X1) = iProver_top ),
% 7.93/1.49      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1228,plain,
% 7.93/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.93/1.49      | r2_hidden(X0,X2) != iProver_top
% 7.93/1.49      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.93/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_2614,plain,
% 7.93/1.49      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.93/1.49      | r2_hidden(sK5(X0,X1,sK7),X2) != iProver_top
% 7.93/1.49      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.93/1.49      inference(superposition,[status(thm)],[c_1212,c_1228]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_3039,plain,
% 7.93/1.49      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 7.93/1.49      | r1_xboole_0(k2_relat_1(sK7),X1) != iProver_top ),
% 7.93/1.49      inference(superposition,[status(thm)],[c_1214,c_2614]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_3230,plain,
% 7.93/1.49      ( k10_relat_1(sK7,X0) = k1_xboole_0
% 7.93/1.49      | r1_xboole_0(k2_relat_1(sK7),X0) != iProver_top ),
% 7.93/1.49      inference(superposition,[status(thm)],[c_1225,c_3039]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_7775,plain,
% 7.93/1.49      ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 7.93/1.49      inference(superposition,[status(thm)],[c_1217,c_3230]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_800,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_2252,plain,
% 7.93/1.49      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_800]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_4450,plain,
% 7.93/1.49      ( X0 != k1_xboole_0
% 7.93/1.49      | k1_xboole_0 = X0
% 7.93/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_2252]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_5415,plain,
% 7.93/1.49      ( k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.93/1.49      | k1_xboole_0 = k10_relat_1(sK7,sK6)
% 7.93/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_4450]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_10,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,X1)
% 7.93/1.49      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.93/1.49      | ~ r2_hidden(X0,k2_relat_1(X3))
% 7.93/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.93/1.49      | ~ v1_relat_1(X3) ),
% 7.93/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_260,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,X1)
% 7.93/1.49      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.93/1.49      | ~ r2_hidden(X0,k2_relat_1(X3))
% 7.93/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.93/1.49      | sK7 != X3 ),
% 7.93/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_261,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,X1)
% 7.93/1.49      | r2_hidden(X2,k10_relat_1(sK7,X1))
% 7.93/1.49      | ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.93/1.49      | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
% 7.93/1.49      inference(unflattening,[status(thm)],[c_260]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_8,plain,
% 7.93/1.49      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 7.93/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_273,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,X1)
% 7.93/1.49      | r2_hidden(X2,k10_relat_1(sK7,X1))
% 7.93/1.49      | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
% 7.93/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_261,c_8]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1345,plain,
% 7.93/1.49      ( r2_hidden(X0,k10_relat_1(sK7,X1))
% 7.93/1.49      | ~ r2_hidden(k4_tarski(X0,sK0(X2,X1)),sK7)
% 7.93/1.49      | ~ r2_hidden(sK0(X2,X1),X1) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_273]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_5215,plain,
% 7.93/1.49      ( r2_hidden(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
% 7.93/1.49      | ~ r2_hidden(k4_tarski(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),sK0(k2_relat_1(sK7),sK6)),sK7)
% 7.93/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_1345]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_3370,plain,
% 7.93/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_799]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_9,plain,
% 7.93/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.93/1.49      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
% 7.93/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1411,plain,
% 7.93/1.49      ( r2_hidden(k4_tarski(sK4(X0,sK0(k2_relat_1(X0),X1)),sK0(k2_relat_1(X0),X1)),X0)
% 7.93/1.49      | ~ r2_hidden(sK0(k2_relat_1(X0),X1),k2_relat_1(X0)) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1796,plain,
% 7.93/1.49      ( r2_hidden(k4_tarski(sK4(sK7,sK0(k2_relat_1(sK7),X0)),sK0(k2_relat_1(sK7),X0)),sK7)
% 7.93/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK7),X0),k2_relat_1(sK7)) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_1411]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_2813,plain,
% 7.93/1.49      ( r2_hidden(k4_tarski(sK4(sK7,sK0(k2_relat_1(sK7),sK6)),sK0(k2_relat_1(sK7),sK6)),sK7)
% 7.93/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_1796]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_4,plain,
% 7.93/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.93/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1887,plain,
% 7.93/1.49      ( r1_xboole_0(k10_relat_1(sK7,sK6),k1_xboole_0) ),
% 7.93/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_1,plain,
% 7.93/1.49      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.93/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_16,negated_conjecture,
% 7.93/1.49      ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.93/1.49      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.93/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_155,plain,
% 7.93/1.49      ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
% 7.93/1.49      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 7.93/1.49      inference(prop_impl,[status(thm)],[c_16]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_407,plain,
% 7.93/1.49      ( r2_hidden(sK0(X0,X1),X1)
% 7.93/1.49      | k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.93/1.49      | k2_relat_1(sK7) != X0
% 7.93/1.49      | sK6 != X1 ),
% 7.93/1.49      inference(resolution_lifted,[status(thm)],[c_1,c_155]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_408,plain,
% 7.93/1.49      ( r2_hidden(sK0(k2_relat_1(sK7),sK6),sK6)
% 7.93/1.49      | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
% 7.93/1.49      inference(unflattening,[status(thm)],[c_407]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_2,plain,
% 7.93/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.93/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_397,plain,
% 7.93/1.49      ( r2_hidden(sK0(X0,X1),X0)
% 7.93/1.49      | k10_relat_1(sK7,sK6) != k1_xboole_0
% 7.93/1.49      | k2_relat_1(sK7) != X0
% 7.93/1.49      | sK6 != X1 ),
% 7.93/1.49      inference(resolution_lifted,[status(thm)],[c_2,c_155]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(c_398,plain,
% 7.93/1.49      ( r2_hidden(sK0(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 7.93/1.49      | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
% 7.93/1.49      inference(unflattening,[status(thm)],[c_397]) ).
% 7.93/1.49  
% 7.93/1.49  cnf(contradiction,plain,
% 7.93/1.49      ( $false ),
% 7.93/1.49      inference(minisat,
% 7.93/1.49                [status(thm)],
% 7.93/1.49                [c_27208,c_27207,c_17064,c_17061,c_7775,c_5415,c_5215,
% 7.93/1.49                 c_3370,c_2813,c_1887,c_408,c_398]) ).
% 7.93/1.49  
% 7.93/1.49  
% 7.93/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.93/1.49  
% 7.93/1.49  ------                               Statistics
% 7.93/1.49  
% 7.93/1.49  ------ General
% 7.93/1.49  
% 7.93/1.49  abstr_ref_over_cycles:                  0
% 7.93/1.49  abstr_ref_under_cycles:                 0
% 7.93/1.49  gc_basic_clause_elim:                   0
% 7.93/1.49  forced_gc_time:                         0
% 7.93/1.49  parsing_time:                           0.009
% 7.93/1.49  unif_index_cands_time:                  0.
% 7.93/1.49  unif_index_add_time:                    0.
% 7.93/1.49  orderings_time:                         0.
% 7.93/1.49  out_proof_time:                         0.008
% 7.93/1.49  total_time:                             0.867
% 7.93/1.49  num_of_symbols:                         48
% 7.93/1.49  num_of_terms:                           20156
% 7.93/1.49  
% 7.93/1.49  ------ Preprocessing
% 7.93/1.49  
% 7.93/1.49  num_of_splits:                          0
% 7.93/1.49  num_of_split_atoms:                     0
% 7.93/1.49  num_of_reused_defs:                     0
% 7.93/1.49  num_eq_ax_congr_red:                    59
% 7.93/1.49  num_of_sem_filtered_clauses:            1
% 7.93/1.49  num_of_subtypes:                        0
% 7.93/1.49  monotx_restored_types:                  0
% 7.93/1.49  sat_num_of_epr_types:                   0
% 7.93/1.49  sat_num_of_non_cyclic_types:            0
% 7.93/1.49  sat_guarded_non_collapsed_types:        0
% 7.93/1.49  num_pure_diseq_elim:                    0
% 7.93/1.49  simp_replaced_by:                       0
% 7.93/1.49  res_preprocessed:                       88
% 7.93/1.49  prep_upred:                             0
% 7.93/1.49  prep_unflattend:                        45
% 7.93/1.49  smt_new_axioms:                         0
% 7.93/1.49  pred_elim_cands:                        2
% 7.93/1.49  pred_elim:                              1
% 7.93/1.49  pred_elim_cl:                           1
% 7.93/1.49  pred_elim_cycles:                       3
% 7.93/1.49  merged_defs:                            8
% 7.93/1.49  merged_defs_ncl:                        0
% 7.93/1.49  bin_hyper_res:                          8
% 7.93/1.49  prep_cycles:                            4
% 7.93/1.49  pred_elim_time:                         0.005
% 7.93/1.49  splitting_time:                         0.
% 7.93/1.49  sem_filter_time:                        0.
% 7.93/1.49  monotx_time:                            0.001
% 7.93/1.49  subtype_inf_time:                       0.
% 7.93/1.49  
% 7.93/1.49  ------ Problem properties
% 7.93/1.49  
% 7.93/1.49  clauses:                                17
% 7.93/1.49  conjectures:                            2
% 7.93/1.49  epr:                                    2
% 7.93/1.49  horn:                                   12
% 7.93/1.49  ground:                                 2
% 7.93/1.49  unary:                                  1
% 7.93/1.49  binary:                                 12
% 7.93/1.49  lits:                                   37
% 7.93/1.49  lits_eq:                                5
% 7.93/1.49  fd_pure:                                0
% 7.93/1.49  fd_pseudo:                              0
% 7.93/1.49  fd_cond:                                1
% 7.93/1.49  fd_pseudo_cond:                         2
% 7.93/1.49  ac_symbols:                             0
% 7.93/1.49  
% 7.93/1.49  ------ Propositional Solver
% 7.93/1.49  
% 7.93/1.49  prop_solver_calls:                      31
% 7.93/1.49  prop_fast_solver_calls:                 931
% 7.93/1.49  smt_solver_calls:                       0
% 7.93/1.49  smt_fast_solver_calls:                  0
% 7.93/1.49  prop_num_of_clauses:                    8588
% 7.93/1.49  prop_preprocess_simplified:             16079
% 7.93/1.49  prop_fo_subsumed:                       6
% 7.93/1.49  prop_solver_time:                       0.
% 7.93/1.49  smt_solver_time:                        0.
% 7.93/1.49  smt_fast_solver_time:                   0.
% 7.93/1.49  prop_fast_solver_time:                  0.
% 7.93/1.49  prop_unsat_core_time:                   0.
% 7.93/1.49  
% 7.93/1.49  ------ QBF
% 7.93/1.49  
% 7.93/1.49  qbf_q_res:                              0
% 7.93/1.49  qbf_num_tautologies:                    0
% 7.93/1.49  qbf_prep_cycles:                        0
% 7.93/1.49  
% 7.93/1.49  ------ BMC1
% 7.93/1.49  
% 7.93/1.49  bmc1_current_bound:                     -1
% 7.93/1.49  bmc1_last_solved_bound:                 -1
% 7.93/1.49  bmc1_unsat_core_size:                   -1
% 7.93/1.49  bmc1_unsat_core_parents_size:           -1
% 7.93/1.49  bmc1_merge_next_fun:                    0
% 7.93/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.93/1.49  
% 7.93/1.49  ------ Instantiation
% 7.93/1.49  
% 7.93/1.49  inst_num_of_clauses:                    1877
% 7.93/1.49  inst_num_in_passive:                    1013
% 7.93/1.49  inst_num_in_active:                     858
% 7.93/1.49  inst_num_in_unprocessed:                5
% 7.93/1.49  inst_num_of_loops:                      1086
% 7.93/1.49  inst_num_of_learning_restarts:          0
% 7.93/1.49  inst_num_moves_active_passive:          223
% 7.93/1.49  inst_lit_activity:                      0
% 7.93/1.49  inst_lit_activity_moves:                0
% 7.93/1.49  inst_num_tautologies:                   0
% 7.93/1.49  inst_num_prop_implied:                  0
% 7.93/1.49  inst_num_existing_simplified:           0
% 7.93/1.49  inst_num_eq_res_simplified:             0
% 7.93/1.49  inst_num_child_elim:                    0
% 7.93/1.49  inst_num_of_dismatching_blockings:      3021
% 7.93/1.49  inst_num_of_non_proper_insts:           3442
% 7.93/1.49  inst_num_of_duplicates:                 0
% 7.93/1.49  inst_inst_num_from_inst_to_res:         0
% 7.93/1.49  inst_dismatching_checking_time:         0.
% 7.93/1.49  
% 7.93/1.49  ------ Resolution
% 7.93/1.49  
% 7.93/1.49  res_num_of_clauses:                     0
% 7.93/1.49  res_num_in_passive:                     0
% 7.93/1.49  res_num_in_active:                      0
% 7.93/1.49  res_num_of_loops:                       92
% 7.93/1.49  res_forward_subset_subsumed:            118
% 7.93/1.49  res_backward_subset_subsumed:           0
% 7.93/1.49  res_forward_subsumed:                   0
% 7.93/1.49  res_backward_subsumed:                  1
% 7.93/1.49  res_forward_subsumption_resolution:     1
% 7.93/1.49  res_backward_subsumption_resolution:    0
% 7.93/1.49  res_clause_to_clause_subsumption:       9044
% 7.93/1.49  res_orphan_elimination:                 0
% 7.93/1.49  res_tautology_del:                      421
% 7.93/1.49  res_num_eq_res_simplified:              0
% 7.93/1.49  res_num_sel_changes:                    0
% 7.93/1.49  res_moves_from_active_to_pass:          0
% 7.93/1.49  
% 7.93/1.49  ------ Superposition
% 7.93/1.49  
% 7.93/1.49  sup_time_total:                         0.
% 7.93/1.49  sup_time_generating:                    0.
% 7.93/1.49  sup_time_sim_full:                      0.
% 7.93/1.49  sup_time_sim_immed:                     0.
% 7.93/1.49  
% 7.93/1.49  sup_num_of_clauses:                     943
% 7.93/1.49  sup_num_in_active:                      209
% 7.93/1.49  sup_num_in_passive:                     734
% 7.93/1.49  sup_num_of_loops:                       216
% 7.93/1.49  sup_fw_superposition:                   1190
% 7.93/1.49  sup_bw_superposition:                   378
% 7.93/1.49  sup_immediate_simplified:               350
% 7.93/1.49  sup_given_eliminated:                   5
% 7.93/1.49  comparisons_done:                       0
% 7.93/1.49  comparisons_avoided:                    0
% 7.93/1.49  
% 7.93/1.49  ------ Simplifications
% 7.93/1.49  
% 7.93/1.49  
% 7.93/1.49  sim_fw_subset_subsumed:                 90
% 7.93/1.49  sim_bw_subset_subsumed:                 0
% 7.93/1.49  sim_fw_subsumed:                        73
% 7.93/1.49  sim_bw_subsumed:                        0
% 7.93/1.49  sim_fw_subsumption_res:                 0
% 7.93/1.49  sim_bw_subsumption_res:                 0
% 7.93/1.49  sim_tautology_del:                      3
% 7.93/1.49  sim_eq_tautology_del:                   10
% 7.93/1.49  sim_eq_res_simp:                        1
% 7.93/1.49  sim_fw_demodulated:                     1
% 7.93/1.49  sim_bw_demodulated:                     22
% 7.93/1.49  sim_light_normalised:                   253
% 7.93/1.49  sim_joinable_taut:                      0
% 7.93/1.49  sim_joinable_simp:                      0
% 7.93/1.49  sim_ac_normalised:                      0
% 7.93/1.49  sim_smt_subsumption:                    0
% 7.93/1.49  
%------------------------------------------------------------------------------
