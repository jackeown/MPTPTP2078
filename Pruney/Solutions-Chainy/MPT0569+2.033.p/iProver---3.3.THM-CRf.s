%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:32 EST 2020

% Result     : Theorem 6.69s
% Output     : CNFRefutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 519 expanded)
%              Number of clauses        :   66 ( 161 expanded)
%              Number of leaves         :   14 ( 104 expanded)
%              Depth                    :   24
%              Number of atoms          :  383 (2171 expanded)
%              Number of equality atoms :  132 ( 485 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    9 (   1 average)

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

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
        & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,
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

fof(f34,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 != k10_relat_1(sK7,sK6) )
    & ( r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 = k10_relat_1(sK7,sK6) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f32,f33])).

fof(f52,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f54,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1025,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1026,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_293,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(sK5(X0,X1,sK7),X1) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_1014,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_268,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_269,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_1016,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1018,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,sK6)
    | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1027,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3209,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1018,c_1027])).

cnf(c_3504,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_3209])).

cnf(c_3575,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_3504])).

cnf(c_3586,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_3575])).

cnf(c_3648,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_3586])).

cnf(c_3678,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_3648])).

cnf(c_3835,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_3678])).

cnf(c_3865,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_3835])).

cnf(c_4856,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6)))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_3865])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1024,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2111,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1024])).

cnf(c_2202,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_2111])).

cnf(c_2215,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2202])).

cnf(c_2217,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2215])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1028,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3585,plain,
    ( k10_relat_1(sK7,sK6) = X0
    | k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(sK0(k10_relat_1(sK7,sK6),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_3575])).

cnf(c_3603,plain,
    ( r2_hidden(sK0(k10_relat_1(sK7,sK6),X0),X0)
    | k10_relat_1(sK7,sK6) = X0
    | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3585])).

cnf(c_3605,plain,
    ( r2_hidden(sK0(k10_relat_1(sK7,sK6),k1_xboole_0),k1_xboole_0)
    | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3603])).

cnf(c_5406,plain,
    ( ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ r2_hidden(sK0(k10_relat_1(sK7,sK6),k1_xboole_0),X0)
    | ~ r2_hidden(sK0(k10_relat_1(sK7,sK6),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5408,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK0(k10_relat_1(sK7,sK6),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5406])).

cnf(c_5520,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4856,c_2217,c_3605,c_5408])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1020,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_249,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_249,c_11])).

cnf(c_1017,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK7,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_1569,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK4(sK7,X0),k10_relat_1(sK7,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_1017])).

cnf(c_5532,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK4(sK7,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5520,c_1569])).

cnf(c_16026,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5532,c_2111])).

cnf(c_16191,plain,
    ( r1_xboole_0(X0,k2_relat_1(sK7)) = iProver_top
    | r2_hidden(sK1(X0,k2_relat_1(sK7)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_16026])).

cnf(c_16278,plain,
    ( r1_xboole_0(sK6,k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_16191])).

cnf(c_1117,plain,
    ( ~ r1_xboole_0(sK6,X0)
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),X0)
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1776,plain,
    ( ~ r1_xboole_0(sK6,k2_relat_1(sK7))
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_1780,plain,
    ( r1_xboole_0(sK6,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1776])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_139,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_354,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k2_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_139])).

cnf(c_355,plain,
    ( r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6)
    | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_356,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_344,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k2_relat_1(sK7) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_139])).

cnf(c_345,plain,
    ( r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_346,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16278,c_5408,c_3605,c_2217,c_1780,c_356,c_346])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:57:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.69/1.57  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/1.57  
% 6.69/1.57  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.69/1.57  
% 6.69/1.57  ------  iProver source info
% 6.69/1.57  
% 6.69/1.57  git: date: 2020-06-30 10:37:57 +0100
% 6.69/1.57  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.69/1.57  git: non_committed_changes: false
% 6.69/1.57  git: last_make_outside_of_git: false
% 6.69/1.57  
% 6.69/1.57  ------ 
% 6.69/1.57  
% 6.69/1.57  ------ Input Options
% 6.69/1.57  
% 6.69/1.57  --out_options                           all
% 6.69/1.57  --tptp_safe_out                         true
% 6.69/1.57  --problem_path                          ""
% 6.69/1.57  --include_path                          ""
% 6.69/1.57  --clausifier                            res/vclausify_rel
% 6.69/1.57  --clausifier_options                    ""
% 6.69/1.57  --stdin                                 false
% 6.69/1.57  --stats_out                             all
% 6.69/1.57  
% 6.69/1.57  ------ General Options
% 6.69/1.57  
% 6.69/1.57  --fof                                   false
% 6.69/1.57  --time_out_real                         305.
% 6.69/1.57  --time_out_virtual                      -1.
% 6.69/1.57  --symbol_type_check                     false
% 6.69/1.57  --clausify_out                          false
% 6.69/1.57  --sig_cnt_out                           false
% 6.69/1.57  --trig_cnt_out                          false
% 6.69/1.57  --trig_cnt_out_tolerance                1.
% 6.69/1.57  --trig_cnt_out_sk_spl                   false
% 6.69/1.57  --abstr_cl_out                          false
% 6.69/1.57  
% 6.69/1.57  ------ Global Options
% 6.69/1.57  
% 6.69/1.57  --schedule                              default
% 6.69/1.57  --add_important_lit                     false
% 6.69/1.57  --prop_solver_per_cl                    1000
% 6.69/1.57  --min_unsat_core                        false
% 6.69/1.57  --soft_assumptions                      false
% 6.69/1.57  --soft_lemma_size                       3
% 6.69/1.57  --prop_impl_unit_size                   0
% 6.69/1.57  --prop_impl_unit                        []
% 6.69/1.57  --share_sel_clauses                     true
% 6.69/1.57  --reset_solvers                         false
% 6.69/1.57  --bc_imp_inh                            [conj_cone]
% 6.69/1.57  --conj_cone_tolerance                   3.
% 6.69/1.57  --extra_neg_conj                        none
% 6.69/1.57  --large_theory_mode                     true
% 6.69/1.57  --prolific_symb_bound                   200
% 6.69/1.57  --lt_threshold                          2000
% 6.69/1.57  --clause_weak_htbl                      true
% 6.69/1.57  --gc_record_bc_elim                     false
% 6.69/1.57  
% 6.69/1.57  ------ Preprocessing Options
% 6.69/1.57  
% 6.69/1.57  --preprocessing_flag                    true
% 6.69/1.57  --time_out_prep_mult                    0.1
% 6.69/1.57  --splitting_mode                        input
% 6.69/1.57  --splitting_grd                         true
% 6.69/1.57  --splitting_cvd                         false
% 6.69/1.57  --splitting_cvd_svl                     false
% 6.69/1.57  --splitting_nvd                         32
% 6.69/1.57  --sub_typing                            true
% 6.69/1.57  --prep_gs_sim                           true
% 6.69/1.57  --prep_unflatten                        true
% 6.69/1.57  --prep_res_sim                          true
% 6.69/1.57  --prep_upred                            true
% 6.69/1.57  --prep_sem_filter                       exhaustive
% 6.69/1.57  --prep_sem_filter_out                   false
% 6.69/1.57  --pred_elim                             true
% 6.69/1.57  --res_sim_input                         true
% 6.69/1.57  --eq_ax_congr_red                       true
% 6.69/1.57  --pure_diseq_elim                       true
% 6.69/1.57  --brand_transform                       false
% 6.69/1.57  --non_eq_to_eq                          false
% 6.69/1.57  --prep_def_merge                        true
% 6.69/1.57  --prep_def_merge_prop_impl              false
% 6.69/1.57  --prep_def_merge_mbd                    true
% 6.69/1.57  --prep_def_merge_tr_red                 false
% 6.69/1.57  --prep_def_merge_tr_cl                  false
% 6.69/1.57  --smt_preprocessing                     true
% 6.69/1.57  --smt_ac_axioms                         fast
% 6.69/1.57  --preprocessed_out                      false
% 6.69/1.57  --preprocessed_stats                    false
% 6.69/1.57  
% 6.69/1.57  ------ Abstraction refinement Options
% 6.69/1.57  
% 6.69/1.57  --abstr_ref                             []
% 6.69/1.57  --abstr_ref_prep                        false
% 6.69/1.57  --abstr_ref_until_sat                   false
% 6.69/1.57  --abstr_ref_sig_restrict                funpre
% 6.69/1.57  --abstr_ref_af_restrict_to_split_sk     false
% 6.69/1.57  --abstr_ref_under                       []
% 6.69/1.57  
% 6.69/1.57  ------ SAT Options
% 6.69/1.57  
% 6.69/1.57  --sat_mode                              false
% 6.69/1.57  --sat_fm_restart_options                ""
% 6.69/1.57  --sat_gr_def                            false
% 6.69/1.57  --sat_epr_types                         true
% 6.69/1.57  --sat_non_cyclic_types                  false
% 6.69/1.57  --sat_finite_models                     false
% 6.69/1.57  --sat_fm_lemmas                         false
% 6.69/1.57  --sat_fm_prep                           false
% 6.69/1.57  --sat_fm_uc_incr                        true
% 6.69/1.57  --sat_out_model                         small
% 6.69/1.57  --sat_out_clauses                       false
% 6.69/1.57  
% 6.69/1.57  ------ QBF Options
% 6.69/1.57  
% 6.69/1.57  --qbf_mode                              false
% 6.69/1.57  --qbf_elim_univ                         false
% 6.69/1.57  --qbf_dom_inst                          none
% 6.69/1.57  --qbf_dom_pre_inst                      false
% 6.69/1.57  --qbf_sk_in                             false
% 6.69/1.57  --qbf_pred_elim                         true
% 6.69/1.57  --qbf_split                             512
% 6.69/1.57  
% 6.69/1.57  ------ BMC1 Options
% 6.69/1.57  
% 6.69/1.57  --bmc1_incremental                      false
% 6.69/1.57  --bmc1_axioms                           reachable_all
% 6.69/1.57  --bmc1_min_bound                        0
% 6.69/1.57  --bmc1_max_bound                        -1
% 6.69/1.57  --bmc1_max_bound_default                -1
% 6.69/1.57  --bmc1_symbol_reachability              true
% 6.69/1.57  --bmc1_property_lemmas                  false
% 6.69/1.57  --bmc1_k_induction                      false
% 6.69/1.57  --bmc1_non_equiv_states                 false
% 6.69/1.57  --bmc1_deadlock                         false
% 6.69/1.57  --bmc1_ucm                              false
% 6.69/1.57  --bmc1_add_unsat_core                   none
% 6.69/1.57  --bmc1_unsat_core_children              false
% 6.69/1.57  --bmc1_unsat_core_extrapolate_axioms    false
% 6.69/1.57  --bmc1_out_stat                         full
% 6.69/1.57  --bmc1_ground_init                      false
% 6.69/1.57  --bmc1_pre_inst_next_state              false
% 6.69/1.57  --bmc1_pre_inst_state                   false
% 6.69/1.57  --bmc1_pre_inst_reach_state             false
% 6.69/1.57  --bmc1_out_unsat_core                   false
% 6.69/1.57  --bmc1_aig_witness_out                  false
% 6.69/1.57  --bmc1_verbose                          false
% 6.69/1.57  --bmc1_dump_clauses_tptp                false
% 6.69/1.57  --bmc1_dump_unsat_core_tptp             false
% 6.69/1.57  --bmc1_dump_file                        -
% 6.69/1.57  --bmc1_ucm_expand_uc_limit              128
% 6.69/1.57  --bmc1_ucm_n_expand_iterations          6
% 6.69/1.57  --bmc1_ucm_extend_mode                  1
% 6.69/1.57  --bmc1_ucm_init_mode                    2
% 6.69/1.57  --bmc1_ucm_cone_mode                    none
% 6.69/1.57  --bmc1_ucm_reduced_relation_type        0
% 6.69/1.57  --bmc1_ucm_relax_model                  4
% 6.69/1.57  --bmc1_ucm_full_tr_after_sat            true
% 6.69/1.57  --bmc1_ucm_expand_neg_assumptions       false
% 6.69/1.57  --bmc1_ucm_layered_model                none
% 6.69/1.57  --bmc1_ucm_max_lemma_size               10
% 6.69/1.57  
% 6.69/1.57  ------ AIG Options
% 6.69/1.57  
% 6.69/1.57  --aig_mode                              false
% 6.69/1.57  
% 6.69/1.57  ------ Instantiation Options
% 6.69/1.57  
% 6.69/1.57  --instantiation_flag                    true
% 6.69/1.57  --inst_sos_flag                         true
% 6.69/1.57  --inst_sos_phase                        true
% 6.69/1.57  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.69/1.57  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.69/1.57  --inst_lit_sel_side                     num_symb
% 6.69/1.57  --inst_solver_per_active                1400
% 6.69/1.57  --inst_solver_calls_frac                1.
% 6.69/1.57  --inst_passive_queue_type               priority_queues
% 6.69/1.57  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.69/1.57  --inst_passive_queues_freq              [25;2]
% 6.69/1.57  --inst_dismatching                      true
% 6.69/1.57  --inst_eager_unprocessed_to_passive     true
% 6.69/1.57  --inst_prop_sim_given                   true
% 6.69/1.57  --inst_prop_sim_new                     false
% 6.69/1.57  --inst_subs_new                         false
% 6.69/1.57  --inst_eq_res_simp                      false
% 6.69/1.57  --inst_subs_given                       false
% 6.69/1.57  --inst_orphan_elimination               true
% 6.69/1.57  --inst_learning_loop_flag               true
% 6.69/1.57  --inst_learning_start                   3000
% 6.69/1.57  --inst_learning_factor                  2
% 6.69/1.57  --inst_start_prop_sim_after_learn       3
% 6.69/1.57  --inst_sel_renew                        solver
% 6.69/1.57  --inst_lit_activity_flag                true
% 6.69/1.57  --inst_restr_to_given                   false
% 6.69/1.57  --inst_activity_threshold               500
% 6.69/1.57  --inst_out_proof                        true
% 6.69/1.57  
% 6.69/1.57  ------ Resolution Options
% 6.69/1.57  
% 6.69/1.57  --resolution_flag                       true
% 6.69/1.57  --res_lit_sel                           adaptive
% 6.69/1.57  --res_lit_sel_side                      none
% 6.69/1.57  --res_ordering                          kbo
% 6.69/1.57  --res_to_prop_solver                    active
% 6.69/1.57  --res_prop_simpl_new                    false
% 6.69/1.57  --res_prop_simpl_given                  true
% 6.69/1.57  --res_passive_queue_type                priority_queues
% 6.69/1.57  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.69/1.57  --res_passive_queues_freq               [15;5]
% 6.69/1.57  --res_forward_subs                      full
% 6.69/1.57  --res_backward_subs                     full
% 6.69/1.57  --res_forward_subs_resolution           true
% 6.69/1.57  --res_backward_subs_resolution          true
% 6.69/1.57  --res_orphan_elimination                true
% 6.69/1.57  --res_time_limit                        2.
% 6.69/1.57  --res_out_proof                         true
% 6.69/1.57  
% 6.69/1.57  ------ Superposition Options
% 6.69/1.57  
% 6.69/1.57  --superposition_flag                    true
% 6.69/1.57  --sup_passive_queue_type                priority_queues
% 6.69/1.57  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.69/1.57  --sup_passive_queues_freq               [8;1;4]
% 6.69/1.57  --demod_completeness_check              fast
% 6.69/1.57  --demod_use_ground                      true
% 6.69/1.57  --sup_to_prop_solver                    passive
% 6.69/1.57  --sup_prop_simpl_new                    true
% 6.69/1.57  --sup_prop_simpl_given                  true
% 6.69/1.57  --sup_fun_splitting                     true
% 6.69/1.57  --sup_smt_interval                      50000
% 6.69/1.57  
% 6.69/1.57  ------ Superposition Simplification Setup
% 6.69/1.57  
% 6.69/1.57  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.69/1.57  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.69/1.57  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.69/1.57  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.69/1.57  --sup_full_triv                         [TrivRules;PropSubs]
% 6.69/1.57  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.69/1.57  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.69/1.57  --sup_immed_triv                        [TrivRules]
% 6.69/1.57  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.69/1.57  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.69/1.57  --sup_immed_bw_main                     []
% 6.69/1.57  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.69/1.57  --sup_input_triv                        [Unflattening;TrivRules]
% 6.69/1.57  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.69/1.57  --sup_input_bw                          []
% 6.69/1.57  
% 6.69/1.57  ------ Combination Options
% 6.69/1.57  
% 6.69/1.57  --comb_res_mult                         3
% 6.69/1.57  --comb_sup_mult                         2
% 6.69/1.57  --comb_inst_mult                        10
% 6.69/1.57  
% 6.69/1.57  ------ Debug Options
% 6.69/1.57  
% 6.69/1.57  --dbg_backtrace                         false
% 6.69/1.57  --dbg_dump_prop_clauses                 false
% 6.69/1.57  --dbg_dump_prop_clauses_file            -
% 6.69/1.57  --dbg_out_stat                          false
% 6.69/1.57  ------ Parsing...
% 6.69/1.57  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.69/1.57  
% 6.69/1.57  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.69/1.57  
% 6.69/1.57  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.69/1.57  
% 6.69/1.57  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.69/1.57  ------ Proving...
% 6.69/1.57  ------ Problem Properties 
% 6.69/1.57  
% 6.69/1.57  
% 6.69/1.57  clauses                                 19
% 6.69/1.57  conjectures                             2
% 6.69/1.57  EPR                                     1
% 6.69/1.57  Horn                                    13
% 6.69/1.57  unary                                   3
% 6.69/1.57  binary                                  9
% 6.69/1.57  lits                                    42
% 6.69/1.57  lits eq                                 11
% 6.69/1.57  fd_pure                                 0
% 6.69/1.57  fd_pseudo                               0
% 6.69/1.57  fd_cond                                 1
% 6.69/1.57  fd_pseudo_cond                          4
% 6.69/1.57  AC symbols                              0
% 6.69/1.57  
% 6.69/1.57  ------ Schedule dynamic 5 is on 
% 6.69/1.57  
% 6.69/1.57  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.69/1.57  
% 6.69/1.57  
% 6.69/1.57  ------ 
% 6.69/1.57  Current options:
% 6.69/1.57  ------ 
% 6.69/1.57  
% 6.69/1.57  ------ Input Options
% 6.69/1.57  
% 6.69/1.57  --out_options                           all
% 6.69/1.57  --tptp_safe_out                         true
% 6.69/1.57  --problem_path                          ""
% 6.69/1.57  --include_path                          ""
% 6.69/1.57  --clausifier                            res/vclausify_rel
% 6.69/1.57  --clausifier_options                    ""
% 6.69/1.57  --stdin                                 false
% 6.69/1.57  --stats_out                             all
% 6.69/1.57  
% 6.69/1.57  ------ General Options
% 6.69/1.57  
% 6.69/1.57  --fof                                   false
% 6.69/1.57  --time_out_real                         305.
% 6.69/1.57  --time_out_virtual                      -1.
% 6.69/1.57  --symbol_type_check                     false
% 6.69/1.57  --clausify_out                          false
% 6.69/1.57  --sig_cnt_out                           false
% 6.69/1.57  --trig_cnt_out                          false
% 6.69/1.57  --trig_cnt_out_tolerance                1.
% 6.69/1.57  --trig_cnt_out_sk_spl                   false
% 6.69/1.57  --abstr_cl_out                          false
% 6.69/1.57  
% 6.69/1.57  ------ Global Options
% 6.69/1.57  
% 6.69/1.57  --schedule                              default
% 6.69/1.57  --add_important_lit                     false
% 6.69/1.57  --prop_solver_per_cl                    1000
% 6.69/1.57  --min_unsat_core                        false
% 6.69/1.57  --soft_assumptions                      false
% 6.69/1.57  --soft_lemma_size                       3
% 6.69/1.57  --prop_impl_unit_size                   0
% 6.69/1.57  --prop_impl_unit                        []
% 6.69/1.57  --share_sel_clauses                     true
% 6.69/1.57  --reset_solvers                         false
% 6.69/1.57  --bc_imp_inh                            [conj_cone]
% 6.69/1.57  --conj_cone_tolerance                   3.
% 6.69/1.57  --extra_neg_conj                        none
% 6.69/1.57  --large_theory_mode                     true
% 6.69/1.57  --prolific_symb_bound                   200
% 6.69/1.57  --lt_threshold                          2000
% 6.69/1.57  --clause_weak_htbl                      true
% 6.69/1.57  --gc_record_bc_elim                     false
% 6.69/1.57  
% 6.69/1.57  ------ Preprocessing Options
% 6.69/1.57  
% 6.69/1.57  --preprocessing_flag                    true
% 6.69/1.57  --time_out_prep_mult                    0.1
% 6.69/1.57  --splitting_mode                        input
% 6.69/1.57  --splitting_grd                         true
% 6.69/1.57  --splitting_cvd                         false
% 6.69/1.57  --splitting_cvd_svl                     false
% 6.69/1.57  --splitting_nvd                         32
% 6.69/1.57  --sub_typing                            true
% 6.69/1.57  --prep_gs_sim                           true
% 6.69/1.57  --prep_unflatten                        true
% 6.69/1.57  --prep_res_sim                          true
% 6.69/1.57  --prep_upred                            true
% 6.69/1.57  --prep_sem_filter                       exhaustive
% 6.69/1.57  --prep_sem_filter_out                   false
% 6.69/1.57  --pred_elim                             true
% 6.69/1.57  --res_sim_input                         true
% 6.69/1.57  --eq_ax_congr_red                       true
% 6.69/1.57  --pure_diseq_elim                       true
% 6.69/1.57  --brand_transform                       false
% 6.69/1.57  --non_eq_to_eq                          false
% 6.69/1.57  --prep_def_merge                        true
% 6.69/1.57  --prep_def_merge_prop_impl              false
% 6.69/1.57  --prep_def_merge_mbd                    true
% 6.69/1.57  --prep_def_merge_tr_red                 false
% 6.69/1.57  --prep_def_merge_tr_cl                  false
% 6.69/1.57  --smt_preprocessing                     true
% 6.69/1.57  --smt_ac_axioms                         fast
% 6.69/1.57  --preprocessed_out                      false
% 6.69/1.57  --preprocessed_stats                    false
% 6.69/1.57  
% 6.69/1.57  ------ Abstraction refinement Options
% 6.69/1.57  
% 6.69/1.57  --abstr_ref                             []
% 6.69/1.57  --abstr_ref_prep                        false
% 6.69/1.57  --abstr_ref_until_sat                   false
% 6.69/1.57  --abstr_ref_sig_restrict                funpre
% 6.69/1.57  --abstr_ref_af_restrict_to_split_sk     false
% 6.69/1.57  --abstr_ref_under                       []
% 6.69/1.57  
% 6.69/1.57  ------ SAT Options
% 6.69/1.57  
% 6.69/1.57  --sat_mode                              false
% 6.69/1.57  --sat_fm_restart_options                ""
% 6.69/1.57  --sat_gr_def                            false
% 6.69/1.57  --sat_epr_types                         true
% 6.69/1.57  --sat_non_cyclic_types                  false
% 6.69/1.57  --sat_finite_models                     false
% 6.69/1.57  --sat_fm_lemmas                         false
% 6.69/1.57  --sat_fm_prep                           false
% 6.69/1.57  --sat_fm_uc_incr                        true
% 6.69/1.57  --sat_out_model                         small
% 6.69/1.57  --sat_out_clauses                       false
% 6.69/1.57  
% 6.69/1.57  ------ QBF Options
% 6.69/1.57  
% 6.69/1.57  --qbf_mode                              false
% 6.69/1.57  --qbf_elim_univ                         false
% 6.69/1.57  --qbf_dom_inst                          none
% 6.69/1.57  --qbf_dom_pre_inst                      false
% 6.69/1.57  --qbf_sk_in                             false
% 6.69/1.57  --qbf_pred_elim                         true
% 6.69/1.57  --qbf_split                             512
% 6.69/1.57  
% 6.69/1.57  ------ BMC1 Options
% 6.69/1.57  
% 6.69/1.57  --bmc1_incremental                      false
% 6.69/1.57  --bmc1_axioms                           reachable_all
% 6.69/1.57  --bmc1_min_bound                        0
% 6.69/1.57  --bmc1_max_bound                        -1
% 6.69/1.57  --bmc1_max_bound_default                -1
% 6.69/1.57  --bmc1_symbol_reachability              true
% 6.69/1.57  --bmc1_property_lemmas                  false
% 6.69/1.57  --bmc1_k_induction                      false
% 6.69/1.57  --bmc1_non_equiv_states                 false
% 6.69/1.57  --bmc1_deadlock                         false
% 6.69/1.57  --bmc1_ucm                              false
% 6.69/1.57  --bmc1_add_unsat_core                   none
% 6.69/1.57  --bmc1_unsat_core_children              false
% 6.69/1.57  --bmc1_unsat_core_extrapolate_axioms    false
% 6.69/1.57  --bmc1_out_stat                         full
% 6.69/1.57  --bmc1_ground_init                      false
% 6.69/1.57  --bmc1_pre_inst_next_state              false
% 6.69/1.57  --bmc1_pre_inst_state                   false
% 6.69/1.57  --bmc1_pre_inst_reach_state             false
% 6.69/1.57  --bmc1_out_unsat_core                   false
% 6.69/1.57  --bmc1_aig_witness_out                  false
% 6.69/1.57  --bmc1_verbose                          false
% 6.69/1.57  --bmc1_dump_clauses_tptp                false
% 6.69/1.57  --bmc1_dump_unsat_core_tptp             false
% 6.69/1.57  --bmc1_dump_file                        -
% 6.69/1.57  --bmc1_ucm_expand_uc_limit              128
% 6.69/1.57  --bmc1_ucm_n_expand_iterations          6
% 6.69/1.57  --bmc1_ucm_extend_mode                  1
% 6.69/1.57  --bmc1_ucm_init_mode                    2
% 6.69/1.57  --bmc1_ucm_cone_mode                    none
% 6.69/1.57  --bmc1_ucm_reduced_relation_type        0
% 6.69/1.57  --bmc1_ucm_relax_model                  4
% 6.69/1.57  --bmc1_ucm_full_tr_after_sat            true
% 6.69/1.57  --bmc1_ucm_expand_neg_assumptions       false
% 6.69/1.57  --bmc1_ucm_layered_model                none
% 6.69/1.57  --bmc1_ucm_max_lemma_size               10
% 6.69/1.57  
% 6.69/1.57  ------ AIG Options
% 6.69/1.57  
% 6.69/1.57  --aig_mode                              false
% 6.69/1.57  
% 6.69/1.57  ------ Instantiation Options
% 6.69/1.57  
% 6.69/1.57  --instantiation_flag                    true
% 6.69/1.57  --inst_sos_flag                         true
% 6.69/1.57  --inst_sos_phase                        true
% 6.69/1.57  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.69/1.57  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.69/1.57  --inst_lit_sel_side                     none
% 6.69/1.57  --inst_solver_per_active                1400
% 6.69/1.57  --inst_solver_calls_frac                1.
% 6.69/1.57  --inst_passive_queue_type               priority_queues
% 6.69/1.57  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.69/1.57  --inst_passive_queues_freq              [25;2]
% 6.69/1.57  --inst_dismatching                      true
% 6.69/1.57  --inst_eager_unprocessed_to_passive     true
% 6.69/1.57  --inst_prop_sim_given                   true
% 6.69/1.57  --inst_prop_sim_new                     false
% 6.69/1.57  --inst_subs_new                         false
% 6.69/1.57  --inst_eq_res_simp                      false
% 6.69/1.57  --inst_subs_given                       false
% 6.69/1.57  --inst_orphan_elimination               true
% 6.69/1.57  --inst_learning_loop_flag               true
% 6.69/1.57  --inst_learning_start                   3000
% 6.69/1.57  --inst_learning_factor                  2
% 6.69/1.57  --inst_start_prop_sim_after_learn       3
% 6.69/1.57  --inst_sel_renew                        solver
% 6.69/1.57  --inst_lit_activity_flag                true
% 6.69/1.57  --inst_restr_to_given                   false
% 6.69/1.57  --inst_activity_threshold               500
% 6.69/1.57  --inst_out_proof                        true
% 6.69/1.57  
% 6.69/1.57  ------ Resolution Options
% 6.69/1.57  
% 6.69/1.57  --resolution_flag                       false
% 6.69/1.57  --res_lit_sel                           adaptive
% 6.69/1.57  --res_lit_sel_side                      none
% 6.69/1.57  --res_ordering                          kbo
% 6.69/1.57  --res_to_prop_solver                    active
% 6.69/1.57  --res_prop_simpl_new                    false
% 6.69/1.57  --res_prop_simpl_given                  true
% 6.69/1.57  --res_passive_queue_type                priority_queues
% 6.69/1.57  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.69/1.57  --res_passive_queues_freq               [15;5]
% 6.69/1.57  --res_forward_subs                      full
% 6.69/1.57  --res_backward_subs                     full
% 6.69/1.57  --res_forward_subs_resolution           true
% 6.69/1.57  --res_backward_subs_resolution          true
% 6.69/1.57  --res_orphan_elimination                true
% 6.69/1.57  --res_time_limit                        2.
% 6.69/1.57  --res_out_proof                         true
% 6.69/1.57  
% 6.69/1.57  ------ Superposition Options
% 6.69/1.57  
% 6.69/1.57  --superposition_flag                    true
% 6.69/1.57  --sup_passive_queue_type                priority_queues
% 6.69/1.57  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.69/1.57  --sup_passive_queues_freq               [8;1;4]
% 6.69/1.57  --demod_completeness_check              fast
% 6.69/1.57  --demod_use_ground                      true
% 6.69/1.57  --sup_to_prop_solver                    passive
% 6.69/1.57  --sup_prop_simpl_new                    true
% 6.69/1.57  --sup_prop_simpl_given                  true
% 6.69/1.57  --sup_fun_splitting                     true
% 6.69/1.57  --sup_smt_interval                      50000
% 6.69/1.57  
% 6.69/1.57  ------ Superposition Simplification Setup
% 6.69/1.57  
% 6.69/1.57  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.69/1.57  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.69/1.57  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.69/1.57  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.69/1.57  --sup_full_triv                         [TrivRules;PropSubs]
% 6.69/1.57  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.69/1.57  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.69/1.57  --sup_immed_triv                        [TrivRules]
% 6.69/1.57  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.69/1.57  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.69/1.57  --sup_immed_bw_main                     []
% 6.69/1.57  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.69/1.57  --sup_input_triv                        [Unflattening;TrivRules]
% 6.69/1.57  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.69/1.57  --sup_input_bw                          []
% 6.69/1.57  
% 6.69/1.57  ------ Combination Options
% 6.69/1.57  
% 6.69/1.57  --comb_res_mult                         3
% 6.69/1.57  --comb_sup_mult                         2
% 6.69/1.57  --comb_inst_mult                        10
% 6.69/1.57  
% 6.69/1.57  ------ Debug Options
% 6.69/1.57  
% 6.69/1.57  --dbg_backtrace                         false
% 6.69/1.57  --dbg_dump_prop_clauses                 false
% 6.69/1.57  --dbg_dump_prop_clauses_file            -
% 6.69/1.57  --dbg_out_stat                          false
% 6.69/1.57  
% 6.69/1.57  
% 6.69/1.57  
% 6.69/1.57  
% 6.69/1.57  ------ Proving...
% 6.69/1.57  
% 6.69/1.57  
% 6.69/1.57  % SZS status Theorem for theBenchmark.p
% 6.69/1.57  
% 6.69/1.57  % SZS output start CNFRefutation for theBenchmark.p
% 6.69/1.57  
% 6.69/1.57  fof(f2,axiom,(
% 6.69/1.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.69/1.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.69/1.57  
% 6.69/1.57  fof(f9,plain,(
% 6.69/1.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.69/1.57    inference(rectify,[],[f2])).
% 6.69/1.57  
% 6.69/1.57  fof(f11,plain,(
% 6.69/1.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 6.69/1.57    inference(ennf_transformation,[],[f9])).
% 6.69/1.57  
% 6.69/1.57  fof(f17,plain,(
% 6.69/1.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 6.69/1.57    introduced(choice_axiom,[])).
% 6.69/1.57  
% 6.69/1.57  fof(f18,plain,(
% 6.69/1.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 6.69/1.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f17])).
% 6.69/1.57  
% 6.69/1.57  fof(f37,plain,(
% 6.69/1.57    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 6.69/1.57    inference(cnf_transformation,[],[f18])).
% 6.69/1.57  
% 6.69/1.57  fof(f38,plain,(
% 6.69/1.57    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 6.69/1.57    inference(cnf_transformation,[],[f18])).
% 6.69/1.57  
% 6.69/1.57  fof(f6,axiom,(
% 6.69/1.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 6.69/1.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.69/1.57  
% 6.69/1.57  fof(f12,plain,(
% 6.69/1.57    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 6.69/1.57    inference(ennf_transformation,[],[f6])).
% 6.69/1.57  
% 6.69/1.57  fof(f27,plain,(
% 6.69/1.57    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 6.69/1.57    inference(nnf_transformation,[],[f12])).
% 6.69/1.57  
% 6.69/1.57  fof(f28,plain,(
% 6.69/1.57    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 6.69/1.57    inference(rectify,[],[f27])).
% 6.69/1.57  
% 6.69/1.57  fof(f29,plain,(
% 6.69/1.57    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))))),
% 6.69/1.57    introduced(choice_axiom,[])).
% 6.69/1.57  
% 6.69/1.57  fof(f30,plain,(
% 6.69/1.57    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 6.69/1.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 6.69/1.57  
% 6.69/1.57  fof(f50,plain,(
% 6.69/1.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 6.69/1.57    inference(cnf_transformation,[],[f30])).
% 6.69/1.57  
% 6.69/1.57  fof(f7,conjecture,(
% 6.69/1.57    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 6.69/1.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.69/1.57  
% 6.69/1.57  fof(f8,negated_conjecture,(
% 6.69/1.57    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 6.69/1.57    inference(negated_conjecture,[],[f7])).
% 6.69/1.57  
% 6.69/1.57  fof(f13,plain,(
% 6.69/1.57    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 6.69/1.57    inference(ennf_transformation,[],[f8])).
% 6.69/1.57  
% 6.69/1.57  fof(f31,plain,(
% 6.69/1.57    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 6.69/1.57    inference(nnf_transformation,[],[f13])).
% 6.69/1.57  
% 6.69/1.57  fof(f32,plain,(
% 6.69/1.57    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 6.69/1.57    inference(flattening,[],[f31])).
% 6.69/1.57  
% 6.69/1.57  fof(f33,plain,(
% 6.69/1.57    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7))),
% 6.69/1.57    introduced(choice_axiom,[])).
% 6.69/1.57  
% 6.69/1.57  fof(f34,plain,(
% 6.69/1.57    (~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7)),
% 6.69/1.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f32,f33])).
% 6.69/1.57  
% 6.69/1.57  fof(f52,plain,(
% 6.69/1.57    v1_relat_1(sK7)),
% 6.69/1.57    inference(cnf_transformation,[],[f34])).
% 6.69/1.57  
% 6.69/1.57  fof(f48,plain,(
% 6.69/1.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 6.69/1.57    inference(cnf_transformation,[],[f30])).
% 6.69/1.57  
% 6.69/1.57  fof(f53,plain,(
% 6.69/1.57    r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)),
% 6.69/1.57    inference(cnf_transformation,[],[f34])).
% 6.69/1.57  
% 6.69/1.57  fof(f39,plain,(
% 6.69/1.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 6.69/1.57    inference(cnf_transformation,[],[f18])).
% 6.69/1.57  
% 6.69/1.57  fof(f3,axiom,(
% 6.69/1.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.69/1.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.69/1.57  
% 6.69/1.57  fof(f19,plain,(
% 6.69/1.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.69/1.57    inference(nnf_transformation,[],[f3])).
% 6.69/1.57  
% 6.69/1.57  fof(f20,plain,(
% 6.69/1.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.69/1.57    inference(flattening,[],[f19])).
% 6.69/1.57  
% 6.69/1.57  fof(f42,plain,(
% 6.69/1.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 6.69/1.57    inference(cnf_transformation,[],[f20])).
% 6.69/1.57  
% 6.69/1.57  fof(f55,plain,(
% 6.69/1.57    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 6.69/1.57    inference(equality_resolution,[],[f42])).
% 6.69/1.57  
% 6.69/1.57  fof(f4,axiom,(
% 6.69/1.57    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 6.69/1.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.69/1.57  
% 6.69/1.57  fof(f43,plain,(
% 6.69/1.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 6.69/1.57    inference(cnf_transformation,[],[f4])).
% 6.69/1.57  
% 6.69/1.57  fof(f1,axiom,(
% 6.69/1.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 6.69/1.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.69/1.57  
% 6.69/1.57  fof(f10,plain,(
% 6.69/1.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 6.69/1.57    inference(ennf_transformation,[],[f1])).
% 6.69/1.57  
% 6.69/1.57  fof(f14,plain,(
% 6.69/1.57    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 6.69/1.57    inference(nnf_transformation,[],[f10])).
% 6.69/1.57  
% 6.69/1.57  fof(f15,plain,(
% 6.69/1.57    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 6.69/1.57    introduced(choice_axiom,[])).
% 6.69/1.57  
% 6.69/1.57  fof(f16,plain,(
% 6.69/1.57    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 6.69/1.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 6.69/1.57  
% 6.69/1.57  fof(f35,plain,(
% 6.69/1.57    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 6.69/1.57    inference(cnf_transformation,[],[f16])).
% 6.69/1.57  
% 6.69/1.57  fof(f5,axiom,(
% 6.69/1.57    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 6.69/1.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.69/1.57  
% 6.69/1.57  fof(f21,plain,(
% 6.69/1.57    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 6.69/1.57    inference(nnf_transformation,[],[f5])).
% 6.69/1.57  
% 6.69/1.57  fof(f22,plain,(
% 6.69/1.57    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.69/1.57    inference(rectify,[],[f21])).
% 6.69/1.57  
% 6.69/1.57  fof(f25,plain,(
% 6.69/1.57    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 6.69/1.57    introduced(choice_axiom,[])).
% 6.69/1.57  
% 6.69/1.57  fof(f24,plain,(
% 6.69/1.57    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0))) )),
% 6.69/1.57    introduced(choice_axiom,[])).
% 6.69/1.57  
% 6.69/1.57  fof(f23,plain,(
% 6.69/1.57    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 6.69/1.57    introduced(choice_axiom,[])).
% 6.69/1.57  
% 6.69/1.57  fof(f26,plain,(
% 6.69/1.57    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.69/1.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).
% 6.69/1.57  
% 6.69/1.57  fof(f44,plain,(
% 6.69/1.57    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 6.69/1.57    inference(cnf_transformation,[],[f26])).
% 6.69/1.57  
% 6.69/1.57  fof(f58,plain,(
% 6.69/1.57    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 6.69/1.57    inference(equality_resolution,[],[f44])).
% 6.69/1.57  
% 6.69/1.57  fof(f51,plain,(
% 6.69/1.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 6.69/1.57    inference(cnf_transformation,[],[f30])).
% 6.69/1.57  
% 6.69/1.57  fof(f45,plain,(
% 6.69/1.57    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 6.69/1.57    inference(cnf_transformation,[],[f26])).
% 6.69/1.57  
% 6.69/1.57  fof(f57,plain,(
% 6.69/1.57    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 6.69/1.57    inference(equality_resolution,[],[f45])).
% 6.69/1.57  
% 6.69/1.57  fof(f54,plain,(
% 6.69/1.57    ~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)),
% 6.69/1.57    inference(cnf_transformation,[],[f34])).
% 6.69/1.57  
% 6.69/1.57  cnf(c_4,plain,
% 6.69/1.57      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 6.69/1.57      inference(cnf_transformation,[],[f37]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1025,plain,
% 6.69/1.57      ( r1_xboole_0(X0,X1) = iProver_top
% 6.69/1.57      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3,plain,
% 6.69/1.57      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 6.69/1.57      inference(cnf_transformation,[],[f38]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1026,plain,
% 6.69/1.57      ( r1_xboole_0(X0,X1) = iProver_top
% 6.69/1.57      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_14,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 6.69/1.57      | r2_hidden(sK5(X0,X2,X1),X2)
% 6.69/1.57      | ~ v1_relat_1(X1) ),
% 6.69/1.57      inference(cnf_transformation,[],[f50]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_19,negated_conjecture,
% 6.69/1.57      ( v1_relat_1(sK7) ),
% 6.69/1.57      inference(cnf_transformation,[],[f52]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_292,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 6.69/1.57      | r2_hidden(sK5(X0,X2,X1),X2)
% 6.69/1.57      | sK7 != X1 ),
% 6.69/1.57      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_293,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
% 6.69/1.57      | r2_hidden(sK5(X0,X1,sK7),X1) ),
% 6.69/1.57      inference(unflattening,[status(thm)],[c_292]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1014,plain,
% 6.69/1.57      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 6.69/1.57      | r2_hidden(sK5(X0,X1,sK7),X1) = iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_16,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 6.69/1.57      | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
% 6.69/1.57      | ~ v1_relat_1(X1) ),
% 6.69/1.57      inference(cnf_transformation,[],[f48]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_268,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 6.69/1.57      | r2_hidden(sK5(X0,X2,X1),k2_relat_1(X1))
% 6.69/1.57      | sK7 != X1 ),
% 6.69/1.57      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_269,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
% 6.69/1.57      | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) ),
% 6.69/1.57      inference(unflattening,[status(thm)],[c_268]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1016,plain,
% 6.69/1.57      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 6.69/1.57      | r2_hidden(sK5(X0,X1,sK7),k2_relat_1(sK7)) = iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_18,negated_conjecture,
% 6.69/1.57      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 6.69/1.57      | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
% 6.69/1.57      inference(cnf_transformation,[],[f53]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1018,plain,
% 6.69/1.57      ( k1_xboole_0 = k10_relat_1(sK7,sK6)
% 6.69/1.57      | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_2,plain,
% 6.69/1.57      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 6.69/1.57      inference(cnf_transformation,[],[f39]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1027,plain,
% 6.69/1.57      ( r1_xboole_0(X0,X1) != iProver_top
% 6.69/1.57      | r2_hidden(X2,X1) != iProver_top
% 6.69/1.57      | r2_hidden(X2,X0) != iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3209,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 6.69/1.57      | r2_hidden(X0,sK6) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1018,c_1027]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3504,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 6.69/1.57      | r2_hidden(sK5(X0,X1,sK7),sK6) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1016,c_3209]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3575,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1014,c_3504]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3586,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,sK6))) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1014,c_3575]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3648,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6)))) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1014,c_3586]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3678,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6))))) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1014,c_3648]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3835,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6)))))) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1014,c_3678]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3865,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6))))))) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1014,c_3835]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_4856,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(X0,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,k10_relat_1(sK7,sK6)))))))) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1014,c_3865]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_5,plain,
% 6.69/1.57      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.69/1.57      inference(cnf_transformation,[],[f55]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_8,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 6.69/1.57      inference(cnf_transformation,[],[f43]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1024,plain,
% 6.69/1.57      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_2111,plain,
% 6.69/1.57      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_5,c_1024]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_2202,plain,
% 6.69/1.57      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1025,c_2111]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_2215,plain,
% 6.69/1.57      ( r1_xboole_0(k1_xboole_0,X0) ),
% 6.69/1.57      inference(predicate_to_equality_rev,[status(thm)],[c_2202]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_2217,plain,
% 6.69/1.57      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 6.69/1.57      inference(instantiation,[status(thm)],[c_2215]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1,plain,
% 6.69/1.57      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 6.69/1.57      inference(cnf_transformation,[],[f35]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1028,plain,
% 6.69/1.57      ( X0 = X1
% 6.69/1.57      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 6.69/1.57      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3585,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = X0
% 6.69/1.57      | k10_relat_1(sK7,sK6) = k1_xboole_0
% 6.69/1.57      | r2_hidden(sK0(k10_relat_1(sK7,sK6),X0),X0) = iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1028,c_3575]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3603,plain,
% 6.69/1.57      ( r2_hidden(sK0(k10_relat_1(sK7,sK6),X0),X0)
% 6.69/1.57      | k10_relat_1(sK7,sK6) = X0
% 6.69/1.57      | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 6.69/1.57      inference(predicate_to_equality_rev,[status(thm)],[c_3585]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_3605,plain,
% 6.69/1.57      ( r2_hidden(sK0(k10_relat_1(sK7,sK6),k1_xboole_0),k1_xboole_0)
% 6.69/1.57      | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 6.69/1.57      inference(instantiation,[status(thm)],[c_3603]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_5406,plain,
% 6.69/1.57      ( ~ r1_xboole_0(X0,k1_xboole_0)
% 6.69/1.57      | ~ r2_hidden(sK0(k10_relat_1(sK7,sK6),k1_xboole_0),X0)
% 6.69/1.57      | ~ r2_hidden(sK0(k10_relat_1(sK7,sK6),k1_xboole_0),k1_xboole_0) ),
% 6.69/1.57      inference(instantiation,[status(thm)],[c_2]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_5408,plain,
% 6.69/1.57      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 6.69/1.57      | ~ r2_hidden(sK0(k10_relat_1(sK7,sK6),k1_xboole_0),k1_xboole_0) ),
% 6.69/1.57      inference(instantiation,[status(thm)],[c_5406]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_5520,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 6.69/1.57      inference(global_propositional_subsumption,
% 6.69/1.57                [status(thm)],
% 6.69/1.57                [c_4856,c_2217,c_3605,c_5408]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_12,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 6.69/1.57      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
% 6.69/1.57      inference(cnf_transformation,[],[f58]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1020,plain,
% 6.69/1.57      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 6.69/1.57      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) = iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_13,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,X1)
% 6.69/1.57      | r2_hidden(X2,k10_relat_1(X3,X1))
% 6.69/1.57      | ~ r2_hidden(X0,k2_relat_1(X3))
% 6.69/1.57      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 6.69/1.57      | ~ v1_relat_1(X3) ),
% 6.69/1.57      inference(cnf_transformation,[],[f51]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_248,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,X1)
% 6.69/1.57      | r2_hidden(X2,k10_relat_1(X3,X1))
% 6.69/1.57      | ~ r2_hidden(X0,k2_relat_1(X3))
% 6.69/1.57      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 6.69/1.57      | sK7 != X3 ),
% 6.69/1.57      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_249,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,X1)
% 6.69/1.57      | r2_hidden(X2,k10_relat_1(sK7,X1))
% 6.69/1.57      | ~ r2_hidden(X0,k2_relat_1(sK7))
% 6.69/1.57      | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
% 6.69/1.57      inference(unflattening,[status(thm)],[c_248]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_11,plain,
% 6.69/1.57      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 6.69/1.57      inference(cnf_transformation,[],[f57]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_261,plain,
% 6.69/1.57      ( ~ r2_hidden(X0,X1)
% 6.69/1.57      | r2_hidden(X2,k10_relat_1(sK7,X1))
% 6.69/1.57      | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
% 6.69/1.57      inference(forward_subsumption_resolution,
% 6.69/1.57                [status(thm)],
% 6.69/1.57                [c_249,c_11]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1017,plain,
% 6.69/1.57      ( r2_hidden(X0,X1) != iProver_top
% 6.69/1.57      | r2_hidden(X2,k10_relat_1(sK7,X1)) = iProver_top
% 6.69/1.57      | r2_hidden(k4_tarski(X2,X0),sK7) != iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1569,plain,
% 6.69/1.57      ( r2_hidden(X0,X1) != iProver_top
% 6.69/1.57      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 6.69/1.57      | r2_hidden(sK4(sK7,X0),k10_relat_1(sK7,X1)) = iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1020,c_1017]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_5532,plain,
% 6.69/1.57      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 6.69/1.57      | r2_hidden(X0,sK6) != iProver_top
% 6.69/1.57      | r2_hidden(sK4(sK7,X0),k1_xboole_0) = iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_5520,c_1569]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_16026,plain,
% 6.69/1.57      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 6.69/1.57      | r2_hidden(X0,sK6) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_5532,c_2111]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_16191,plain,
% 6.69/1.57      ( r1_xboole_0(X0,k2_relat_1(sK7)) = iProver_top
% 6.69/1.57      | r2_hidden(sK1(X0,k2_relat_1(sK7)),sK6) != iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1026,c_16026]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_16278,plain,
% 6.69/1.57      ( r1_xboole_0(sK6,k2_relat_1(sK7)) = iProver_top ),
% 6.69/1.57      inference(superposition,[status(thm)],[c_1025,c_16191]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1117,plain,
% 6.69/1.57      ( ~ r1_xboole_0(sK6,X0)
% 6.69/1.57      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),X0)
% 6.69/1.57      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6) ),
% 6.69/1.57      inference(instantiation,[status(thm)],[c_2]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1776,plain,
% 6.69/1.57      ( ~ r1_xboole_0(sK6,k2_relat_1(sK7))
% 6.69/1.57      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 6.69/1.57      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6) ),
% 6.69/1.57      inference(instantiation,[status(thm)],[c_1117]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_1780,plain,
% 6.69/1.57      ( r1_xboole_0(sK6,k2_relat_1(sK7)) != iProver_top
% 6.69/1.57      | r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) != iProver_top
% 6.69/1.57      | r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6) != iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_1776]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_17,negated_conjecture,
% 6.69/1.57      ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
% 6.69/1.57      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 6.69/1.57      inference(cnf_transformation,[],[f54]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_139,plain,
% 6.69/1.57      ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
% 6.69/1.57      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 6.69/1.57      inference(prop_impl,[status(thm)],[c_17]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_354,plain,
% 6.69/1.57      ( r2_hidden(sK1(X0,X1),X1)
% 6.69/1.57      | k10_relat_1(sK7,sK6) != k1_xboole_0
% 6.69/1.57      | k2_relat_1(sK7) != X0
% 6.69/1.57      | sK6 != X1 ),
% 6.69/1.57      inference(resolution_lifted,[status(thm)],[c_3,c_139]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_355,plain,
% 6.69/1.57      ( r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6)
% 6.69/1.57      | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
% 6.69/1.57      inference(unflattening,[status(thm)],[c_354]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_356,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) != k1_xboole_0
% 6.69/1.57      | r2_hidden(sK1(k2_relat_1(sK7),sK6),sK6) = iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_344,plain,
% 6.69/1.57      ( r2_hidden(sK1(X0,X1),X0)
% 6.69/1.57      | k10_relat_1(sK7,sK6) != k1_xboole_0
% 6.69/1.57      | k2_relat_1(sK7) != X0
% 6.69/1.57      | sK6 != X1 ),
% 6.69/1.57      inference(resolution_lifted,[status(thm)],[c_4,c_139]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_345,plain,
% 6.69/1.57      ( r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 6.69/1.57      | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
% 6.69/1.57      inference(unflattening,[status(thm)],[c_344]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(c_346,plain,
% 6.69/1.57      ( k10_relat_1(sK7,sK6) != k1_xboole_0
% 6.69/1.57      | r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) = iProver_top ),
% 6.69/1.57      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 6.69/1.57  
% 6.69/1.57  cnf(contradiction,plain,
% 6.69/1.57      ( $false ),
% 6.69/1.57      inference(minisat,
% 6.69/1.57                [status(thm)],
% 6.69/1.57                [c_16278,c_5408,c_3605,c_2217,c_1780,c_356,c_346]) ).
% 6.69/1.57  
% 6.69/1.57  
% 6.69/1.57  % SZS output end CNFRefutation for theBenchmark.p
% 6.69/1.57  
% 6.69/1.57  ------                               Statistics
% 6.69/1.57  
% 6.69/1.57  ------ General
% 6.69/1.57  
% 6.69/1.57  abstr_ref_over_cycles:                  0
% 6.69/1.57  abstr_ref_under_cycles:                 0
% 6.69/1.57  gc_basic_clause_elim:                   0
% 6.69/1.57  forced_gc_time:                         0
% 6.69/1.57  parsing_time:                           0.008
% 6.69/1.57  unif_index_cands_time:                  0.
% 6.69/1.57  unif_index_add_time:                    0.
% 6.69/1.57  orderings_time:                         0.
% 6.69/1.57  out_proof_time:                         0.015
% 6.69/1.57  total_time:                             0.687
% 6.69/1.57  num_of_symbols:                         47
% 6.69/1.57  num_of_terms:                           19388
% 6.69/1.57  
% 6.69/1.57  ------ Preprocessing
% 6.69/1.57  
% 6.69/1.57  num_of_splits:                          0
% 6.69/1.57  num_of_split_atoms:                     0
% 6.69/1.57  num_of_reused_defs:                     0
% 6.69/1.57  num_eq_ax_congr_red:                    37
% 6.69/1.57  num_of_sem_filtered_clauses:            1
% 6.69/1.57  num_of_subtypes:                        0
% 6.69/1.57  monotx_restored_types:                  0
% 6.69/1.57  sat_num_of_epr_types:                   0
% 6.69/1.57  sat_num_of_non_cyclic_types:            0
% 6.69/1.57  sat_guarded_non_collapsed_types:        0
% 6.69/1.57  num_pure_diseq_elim:                    0
% 6.69/1.57  simp_replaced_by:                       0
% 6.69/1.57  res_preprocessed:                       96
% 6.69/1.57  prep_upred:                             0
% 6.69/1.57  prep_unflattend:                        16
% 6.69/1.57  smt_new_axioms:                         0
% 6.69/1.57  pred_elim_cands:                        2
% 6.69/1.57  pred_elim:                              1
% 6.69/1.57  pred_elim_cl:                           1
% 6.69/1.57  pred_elim_cycles:                       3
% 6.69/1.57  merged_defs:                            8
% 6.69/1.57  merged_defs_ncl:                        0
% 6.69/1.57  bin_hyper_res:                          8
% 6.69/1.57  prep_cycles:                            4
% 6.69/1.57  pred_elim_time:                         0.004
% 6.69/1.57  splitting_time:                         0.
% 6.69/1.57  sem_filter_time:                        0.
% 6.69/1.57  monotx_time:                            0.
% 6.69/1.57  subtype_inf_time:                       0.
% 6.69/1.57  
% 6.69/1.57  ------ Problem properties
% 6.69/1.57  
% 6.69/1.57  clauses:                                19
% 6.69/1.57  conjectures:                            2
% 6.69/1.57  epr:                                    1
% 6.69/1.57  horn:                                   13
% 6.69/1.57  ground:                                 2
% 6.69/1.57  unary:                                  3
% 6.69/1.57  binary:                                 9
% 6.69/1.57  lits:                                   42
% 6.69/1.57  lits_eq:                                11
% 6.69/1.57  fd_pure:                                0
% 6.69/1.57  fd_pseudo:                              0
% 6.69/1.57  fd_cond:                                1
% 6.69/1.57  fd_pseudo_cond:                         4
% 6.69/1.57  ac_symbols:                             0
% 6.69/1.57  
% 6.69/1.57  ------ Propositional Solver
% 6.69/1.57  
% 6.69/1.57  prop_solver_calls:                      31
% 6.69/1.57  prop_fast_solver_calls:                 1021
% 6.69/1.57  smt_solver_calls:                       0
% 6.69/1.57  smt_fast_solver_calls:                  0
% 6.69/1.57  prop_num_of_clauses:                    8197
% 6.69/1.57  prop_preprocess_simplified:             12722
% 6.69/1.57  prop_fo_subsumed:                       7
% 6.69/1.57  prop_solver_time:                       0.
% 6.69/1.57  smt_solver_time:                        0.
% 6.69/1.57  smt_fast_solver_time:                   0.
% 6.69/1.57  prop_fast_solver_time:                  0.
% 6.69/1.57  prop_unsat_core_time:                   0.001
% 6.69/1.57  
% 6.69/1.57  ------ QBF
% 6.69/1.57  
% 6.69/1.57  qbf_q_res:                              0
% 6.69/1.57  qbf_num_tautologies:                    0
% 6.69/1.57  qbf_prep_cycles:                        0
% 6.69/1.57  
% 6.69/1.57  ------ BMC1
% 6.69/1.57  
% 6.69/1.57  bmc1_current_bound:                     -1
% 6.69/1.57  bmc1_last_solved_bound:                 -1
% 6.69/1.57  bmc1_unsat_core_size:                   -1
% 6.69/1.57  bmc1_unsat_core_parents_size:           -1
% 6.69/1.57  bmc1_merge_next_fun:                    0
% 6.69/1.57  bmc1_unsat_core_clauses_time:           0.
% 6.69/1.57  
% 6.69/1.57  ------ Instantiation
% 6.69/1.57  
% 6.69/1.57  inst_num_of_clauses:                    1607
% 6.69/1.57  inst_num_in_passive:                    627
% 6.69/1.57  inst_num_in_active:                     633
% 6.69/1.57  inst_num_in_unprocessed:                347
% 6.69/1.57  inst_num_of_loops:                      980
% 6.69/1.57  inst_num_of_learning_restarts:          0
% 6.69/1.57  inst_num_moves_active_passive:          345
% 6.69/1.57  inst_lit_activity:                      0
% 6.69/1.57  inst_lit_activity_moves:                0
% 6.69/1.57  inst_num_tautologies:                   0
% 6.69/1.57  inst_num_prop_implied:                  0
% 6.69/1.57  inst_num_existing_simplified:           0
% 6.69/1.57  inst_num_eq_res_simplified:             0
% 6.69/1.57  inst_num_child_elim:                    0
% 6.69/1.57  inst_num_of_dismatching_blockings:      565
% 6.69/1.57  inst_num_of_non_proper_insts:           1894
% 6.69/1.57  inst_num_of_duplicates:                 0
% 6.69/1.57  inst_inst_num_from_inst_to_res:         0
% 6.69/1.57  inst_dismatching_checking_time:         0.
% 6.69/1.57  
% 6.69/1.57  ------ Resolution
% 6.69/1.57  
% 6.69/1.57  res_num_of_clauses:                     0
% 6.69/1.57  res_num_in_passive:                     0
% 6.69/1.57  res_num_in_active:                      0
% 6.69/1.57  res_num_of_loops:                       100
% 6.69/1.57  res_forward_subset_subsumed:            99
% 6.69/1.57  res_backward_subset_subsumed:           0
% 6.69/1.57  res_forward_subsumed:                   0
% 6.69/1.57  res_backward_subsumed:                  0
% 6.69/1.57  res_forward_subsumption_resolution:     1
% 6.69/1.57  res_backward_subsumption_resolution:    0
% 6.69/1.57  res_clause_to_clause_subsumption:       2194
% 6.69/1.57  res_orphan_elimination:                 0
% 6.69/1.57  res_tautology_del:                      139
% 6.69/1.57  res_num_eq_res_simplified:              0
% 6.69/1.57  res_num_sel_changes:                    0
% 6.69/1.57  res_moves_from_active_to_pass:          0
% 6.69/1.57  
% 6.69/1.57  ------ Superposition
% 6.69/1.57  
% 6.69/1.57  sup_time_total:                         0.
% 6.69/1.57  sup_time_generating:                    0.
% 6.69/1.57  sup_time_sim_full:                      0.
% 6.69/1.57  sup_time_sim_immed:                     0.
% 6.69/1.57  
% 6.69/1.57  sup_num_of_clauses:                     858
% 6.69/1.57  sup_num_in_active:                      183
% 6.69/1.57  sup_num_in_passive:                     675
% 6.69/1.57  sup_num_of_loops:                       194
% 6.69/1.57  sup_fw_superposition:                   879
% 6.69/1.57  sup_bw_superposition:                   616
% 6.69/1.57  sup_immediate_simplified:               357
% 6.69/1.57  sup_given_eliminated:                   0
% 6.69/1.57  comparisons_done:                       0
% 6.69/1.57  comparisons_avoided:                    0
% 6.69/1.57  
% 6.69/1.57  ------ Simplifications
% 6.69/1.57  
% 6.69/1.57  
% 6.69/1.57  sim_fw_subset_subsumed:                 117
% 6.69/1.57  sim_bw_subset_subsumed:                 40
% 6.69/1.57  sim_fw_subsumed:                        38
% 6.69/1.57  sim_bw_subsumed:                        17
% 6.69/1.57  sim_fw_subsumption_res:                 0
% 6.69/1.57  sim_bw_subsumption_res:                 0
% 6.69/1.57  sim_tautology_del:                      5
% 6.69/1.57  sim_eq_tautology_del:                   45
% 6.69/1.57  sim_eq_res_simp:                        1
% 6.69/1.57  sim_fw_demodulated:                     59
% 6.69/1.57  sim_bw_demodulated:                     38
% 6.69/1.57  sim_light_normalised:                   304
% 6.69/1.57  sim_joinable_taut:                      0
% 6.69/1.57  sim_joinable_simp:                      0
% 6.69/1.57  sim_ac_normalised:                      0
% 6.69/1.57  sim_smt_subsumption:                    0
% 6.69/1.57  
%------------------------------------------------------------------------------
