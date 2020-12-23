%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0569+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:37 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 248 expanded)
%              Number of clauses        :   73 (  90 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  409 ( 934 expanded)
%              Number of equality atoms :  111 ( 218 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,
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

fof(f38,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 != k10_relat_1(sK7,sK6) )
    & ( r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 = k10_relat_1(sK7,sK6) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f36,f37])).

fof(f58,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
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
    inference(rectify,[],[f7])).

fof(f16,plain,(
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

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f33])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3,f27])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

cnf(c_864,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4028,plain,
    ( sK3(k10_relat_1(sK7,sK6)) = sK3(k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_868,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1638,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(k10_relat_1(sK7,sK6)),k10_relat_1(sK7,sK6))
    | X1 != k10_relat_1(sK7,sK6)
    | X0 != sK3(k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_4027,plain,
    ( r2_hidden(sK3(k10_relat_1(sK7,sK6)),X0)
    | ~ r2_hidden(sK3(k10_relat_1(sK7,sK6)),k10_relat_1(sK7,sK6))
    | X0 != k10_relat_1(sK7,sK6)
    | sK3(k10_relat_1(sK7,sK6)) != sK3(k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_4030,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(sK7,sK6)),k10_relat_1(sK7,sK6))
    | r2_hidden(sK3(k10_relat_1(sK7,sK6)),k1_xboole_0)
    | sK3(k10_relat_1(sK7,sK6)) != sK3(k10_relat_1(sK7,sK6))
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_4027])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1316,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,sK6)
    | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1322,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3006,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_1322])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1527,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK7,sK6))
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_286,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK3(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_287,plain,
    ( r2_hidden(sK3(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_1532,plain,
    ( r2_hidden(sK3(k10_relat_1(sK7,sK6)),k10_relat_1(sK7,sK6))
    | v1_xboole_0(k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_348,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_349,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(sK4(X0,X1,sK7),k2_relat_1(sK7)) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_1652,plain,
    ( r2_hidden(sK4(sK3(k10_relat_1(sK7,sK6)),sK6,sK7),k2_relat_1(sK7))
    | ~ r2_hidden(sK3(k10_relat_1(sK7,sK6)),k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_372,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_373,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(sK4(X0,X1,sK7),X1) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_1650,plain,
    ( r2_hidden(sK4(sK3(k10_relat_1(sK7,sK6)),sK6,sK7),sK6)
    | ~ r2_hidden(sK3(k10_relat_1(sK7,sK6)),k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_865,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1536,plain,
    ( X0 != X1
    | k10_relat_1(sK7,sK6) != X1
    | k10_relat_1(sK7,sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1659,plain,
    ( X0 != k10_relat_1(sK7,sK6)
    | k10_relat_1(sK7,sK6) = X0
    | k10_relat_1(sK7,sK6) != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_1661,plain,
    ( k10_relat_1(sK7,sK6) != k10_relat_1(sK7,sK6)
    | k10_relat_1(sK7,sK6) = k1_xboole_0
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_1660,plain,
    ( k10_relat_1(sK7,sK6) = k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1323,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1705,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | k3_xboole_0(k2_relat_1(sK7),sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1316,c_1323])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1324,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1717,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1324])).

cnf(c_1718,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1717])).

cnf(c_1724,plain,
    ( ~ r1_xboole_0(X0,sK6)
    | ~ r2_hidden(sK4(sK3(k10_relat_1(sK7,sK6)),sK6,sK7),X0)
    | ~ r2_hidden(sK4(sK3(k10_relat_1(sK7,sK6)),sK6,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2405,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | ~ r2_hidden(sK4(sK3(k10_relat_1(sK7,sK6)),sK6,sK7),k2_relat_1(sK7))
    | ~ r2_hidden(sK4(sK3(k10_relat_1(sK7,sK6)),sK6,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_3456,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3006,c_1527,c_1532,c_1652,c_1650,c_1661,c_1660,c_1718,c_2405])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3350,plain,
    ( ~ r2_hidden(sK2(sK7,sK5(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | ~ v1_xboole_0(k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_869,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2378,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k10_relat_1(sK7,sK6))
    | X2 != X0
    | k10_relat_1(sK7,sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_2380,plain,
    ( r1_xboole_0(k1_xboole_0,k10_relat_1(sK7,sK6))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_329,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_341,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_329,c_2])).

cnf(c_1495,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,sK6))
    | ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),sK6)
    | ~ r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK7),sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1863,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),sK6)
    | r2_hidden(sK2(sK7,sK5(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK2(sK7,sK5(k2_relat_1(sK7),sK6)),sK5(k2_relat_1(sK7),sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_1632,plain,
    ( ~ r1_xboole_0(X0,k10_relat_1(sK7,sK6))
    | ~ r2_hidden(sK3(k10_relat_1(sK7,sK6)),X0)
    | ~ r2_hidden(sK3(k10_relat_1(sK7,sK6)),k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1634,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k10_relat_1(sK7,sK6))
    | ~ r2_hidden(sK3(k10_relat_1(sK7,sK6)),k10_relat_1(sK7,sK6))
    | ~ r2_hidden(sK3(k10_relat_1(sK7,sK6)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_1530,plain,
    ( k10_relat_1(sK7,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1531,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK7,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1506,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | r2_hidden(k4_tarski(sK2(sK7,sK5(k2_relat_1(sK7),sK6)),sK5(k2_relat_1(sK7),sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_881,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_166,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_467,plain,
    ( r2_hidden(sK5(X0,X1),X1)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k2_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_166])).

cnf(c_468,plain,
    ( r2_hidden(sK5(k2_relat_1(sK7),sK6),sK6)
    | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_457,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k2_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_166])).

cnf(c_458,plain,
    ( r2_hidden(sK5(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_58,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_40,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4028,c_4030,c_3456,c_3350,c_2380,c_1863,c_1634,c_1532,c_1531,c_1506,c_881,c_468,c_458,c_58,c_40])).


%------------------------------------------------------------------------------
