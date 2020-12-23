%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0569+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:37 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 341 expanded)
%              Number of clauses        :  105 ( 152 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :   20
%              Number of atoms          :  546 (1211 expanded)
%              Number of equality atoms :  209 ( 382 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
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

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

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

fof(f67,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
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

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f8])).

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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f29,f28,f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_53366,plain,
    ( ~ r2_hidden(sK3(sK7,sK5(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | ~ v1_xboole_0(k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1769,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1))
    | ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),X1)
    | ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK7),sK6)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13039,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),X0)
    | ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | r2_hidden(sK3(sK7,sK5(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,X0))
    | ~ r2_hidden(k4_tarski(sK3(sK7,sK5(k2_relat_1(sK7),sK6)),sK5(k2_relat_1(sK7),sK6)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_25687,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),sK6)
    | r2_hidden(sK3(sK7,sK5(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK3(sK7,sK5(k2_relat_1(sK7),sK6)),sK5(k2_relat_1(sK7),sK6)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_13039])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_896,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,sK6)
    | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_909,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1385,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | k3_xboole_0(k2_relat_1(sK7),sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_896,c_909])).

cnf(c_20,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_901,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK5(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_915,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1885,plain,
    ( r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK5(X0,k3_xboole_0(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_915])).

cnf(c_6638,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r1_xboole_0(X0,k3_xboole_0(k2_relat_1(sK7),sK6)) = iProver_top
    | r2_hidden(sK5(X0,k1_xboole_0),k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1385,c_1885])).

cnf(c_18,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_43,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_57,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_302,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_321,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_908,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_899,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1194,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_908,c_899])).

cnf(c_1223,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1194,c_908])).

cnf(c_1224,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1223])).

cnf(c_309,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1185,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1302,plain,
    ( v1_xboole_0(k2_relat_1(X0))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k2_relat_1(X0) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_1304,plain,
    ( k2_relat_1(X0) != o_0_0_xboole_0
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_1306,plain,
    ( k2_relat_1(k1_xboole_0) != o_0_0_xboole_0
    | v1_xboole_0(k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1303,plain,
    ( r2_hidden(k4_tarski(sK2(X0,o_0_0_xboole_0),sK1(X0,o_0_0_xboole_0)),X0)
    | r2_hidden(sK1(X0,o_0_0_xboole_0),o_0_0_xboole_0)
    | k2_relat_1(X0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1309,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0,o_0_0_xboole_0),sK1(k1_xboole_0,o_0_0_xboole_0)),k1_xboole_0)
    | r2_hidden(sK1(k1_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | k2_relat_1(k1_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_1450,plain,
    ( k10_relat_1(sK7,sK6) = k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_1553,plain,
    ( ~ v1_xboole_0(k2_relat_1(X0))
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1556,plain,
    ( k1_xboole_0 = k2_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1553])).

cnf(c_1558,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | v1_xboole_0(k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1556])).

cnf(c_303,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1604,plain,
    ( X0 != X1
    | X0 = k3_xboole_0(X2,X3)
    | k3_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_1982,plain,
    ( k3_xboole_0(X0,X1) != X2
    | k2_relat_1(X3) != X2
    | k2_relat_1(X3) = k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_1984,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1982])).

cnf(c_2059,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,o_0_0_xboole_0),sK1(X0,o_0_0_xboole_0)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2066,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_xboole_0,o_0_0_xboole_0),sK1(k1_xboole_0,o_0_0_xboole_0)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2059])).

cnf(c_306,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_2667,plain,
    ( X0 != X1
    | X2 != k2_relat_1(X1)
    | k2_relat_1(X0) = X2 ),
    inference(resolution,[status(thm)],[c_303,c_306])).

cnf(c_2668,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2667])).

cnf(c_3309,plain,
    ( ~ r2_hidden(sK1(X0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3316,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3309])).

cnf(c_1561,plain,
    ( X0 != X1
    | X0 = k2_relat_1(X2)
    | k2_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_1983,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | X0 = k2_relat_1(X3)
    | k2_relat_1(X3) != k3_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_3572,plain,
    ( k10_relat_1(sK7,sK6) != k3_xboole_0(X0,X1)
    | k10_relat_1(sK7,sK6) = k2_relat_1(X2)
    | k2_relat_1(X2) != k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_3574,plain,
    ( k10_relat_1(sK7,sK6) != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k10_relat_1(sK7,sK6) = k2_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3572])).

cnf(c_1322,plain,
    ( X0 != X1
    | k10_relat_1(sK7,sK6) != X1
    | k10_relat_1(sK7,sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_3573,plain,
    ( X0 != k2_relat_1(X1)
    | k10_relat_1(sK7,sK6) = X0
    | k10_relat_1(sK7,sK6) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_3575,plain,
    ( k10_relat_1(sK7,sK6) != k2_relat_1(k1_xboole_0)
    | k10_relat_1(sK7,sK6) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3573])).

cnf(c_2535,plain,
    ( X0 != k10_relat_1(sK7,sK6)
    | k10_relat_1(sK7,sK6) = X0
    | k10_relat_1(sK7,sK6) != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_4019,plain,
    ( k10_relat_1(sK7,sK6) != k10_relat_1(sK7,sK6)
    | k10_relat_1(sK7,sK6) = k3_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_2535])).

cnf(c_4023,plain,
    ( k10_relat_1(sK7,sK6) != k10_relat_1(sK7,sK6)
    | k10_relat_1(sK7,sK6) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_4019])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_919,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_905,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_903,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_907,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1380,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r1_xboole_0(sK6,k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_907])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_902,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2611,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_902])).

cnf(c_4058,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_903,c_2611])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4676,plain,
    ( r2_hidden(sK4(X0,X1,sK7),sK6) != iProver_top
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4058,c_27])).

cnf(c_4677,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4676])).

cnf(c_4685,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_4677])).

cnf(c_4929,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top
    | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4685,c_27])).

cnf(c_4930,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK7,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4929])).

cnf(c_4939,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | k3_xboole_0(X0,X1) = k10_relat_1(sK7,sK6)
    | r2_hidden(sK0(X0,X1,k10_relat_1(sK7,sK6)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_919,c_4930])).

cnf(c_5008,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k10_relat_1(sK7,sK6)
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k10_relat_1(sK7,sK6)),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4939])).

cnf(c_7140,plain,
    ( ~ r2_hidden(sK0(X0,X1,k10_relat_1(sK7,sK6)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_7146,plain,
    ( r2_hidden(sK0(X0,X1,k10_relat_1(sK7,sK6)),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7140])).

cnf(c_7148,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0,k10_relat_1(sK7,sK6)),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7146])).

cnf(c_7446,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6638,c_43,c_12,c_57,c_321,c_1223,c_1224,c_1306,c_1309,c_1450,c_1558,c_1984,c_2066,c_2668,c_3316,c_3574,c_3575,c_4023,c_5008,c_7148])).

cnf(c_2665,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_303,c_302])).

cnf(c_3518,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2665,c_25])).

cnf(c_3530,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | X0 != k1_xboole_0
    | k10_relat_1(sK7,sK6) = X0 ),
    inference(resolution,[status(thm)],[c_3518,c_303])).

cnf(c_2663,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | X0 != k10_relat_1(sK7,sK6)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_303,c_25])).

cnf(c_3662,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(resolution,[status(thm)],[c_3530,c_2663])).

cnf(c_1220,plain,
    ( k10_relat_1(sK7,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_1221,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK7,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_3737,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3662,c_321,c_1221])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1766,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | r2_hidden(k4_tarski(sK3(sK7,sK5(k2_relat_1(sK7),sK6)),sK5(k2_relat_1(sK7),sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1417,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k10_relat_1(sK7,sK6))
    | k10_relat_1(sK7,sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1419,plain,
    ( v1_xboole_0(k10_relat_1(sK7,sK6))
    | ~ v1_xboole_0(k1_xboole_0)
    | k10_relat_1(sK7,sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_21,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1154,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | r2_hidden(sK5(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1151,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | r2_hidden(sK5(k2_relat_1(sK7),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_24,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53366,c_25687,c_7446,c_3737,c_1766,c_1419,c_1224,c_1154,c_1151,c_24,c_26])).


%------------------------------------------------------------------------------
