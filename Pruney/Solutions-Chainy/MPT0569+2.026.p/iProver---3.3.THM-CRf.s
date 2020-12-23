%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:31 EST 2020

% Result     : Theorem 11.59s
% Output     : CNFRefutation 11.59s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 409 expanded)
%              Number of clauses        :   96 ( 150 expanded)
%              Number of leaves         :   19 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  446 (1410 expanded)
%              Number of equality atoms :  168 ( 438 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

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
   => ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 != k10_relat_1(sK6,sK5) )
      & ( r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 = k10_relat_1(sK6,sK5) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 != k10_relat_1(sK6,sK5) )
    & ( r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 = k10_relat_1(sK6,sK5) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f32])).

fof(f52,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f41])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f35,f41])).

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

fof(f11,plain,(
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

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f50,f41])).

fof(f51,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

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
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f24,f23,f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f14])).

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
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

cnf(c_964,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_23141,plain,
    ( sK3(sK6,sK0(k2_relat_1(sK6),sK5)) = sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_969,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5785,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | X1 != k10_relat_1(sK6,sK5)
    | X0 != sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_23140,plain,
    ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
    | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | X0 != k10_relat_1(sK6,sK5)
    | sK3(sK6,sK0(k2_relat_1(sK6),sK5)) != sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_5785])).

cnf(c_23143,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k1_xboole_0)
    | sK3(sK6,sK0(k2_relat_1(sK6),sK5)) != sK3(sK6,sK0(k2_relat_1(sK6),sK5))
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_23140])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1414,plain,
    ( k1_xboole_0 = k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1425,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1616,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k2_relat_1(sK6),sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1414,c_1425])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1426,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2495,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_1426])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1423,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1422,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1424,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1774,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1424])).

cnf(c_3456,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1774])).

cnf(c_4434,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r1_xboole_0(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2495,c_3456])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_53,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_323,plain,
    ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_324,plain,
    ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X0))) = k10_relat_1(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_325,plain,
    ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) = k10_relat_1(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_983,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_965,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2173,plain,
    ( k2_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_2174,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2173])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1418,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1421,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1420,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1651,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1420])).

cnf(c_2178,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_1651])).

cnf(c_2182,plain,
    ( r2_hidden(sK1(k1_xboole_0,X0),X0)
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2178])).

cnf(c_2184,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_3025,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3027,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3025])).

cnf(c_3297,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_965,c_964])).

cnf(c_4184,plain,
    ( k10_relat_1(sK6,X0) = k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X0))) ),
    inference(resolution,[status(thm)],[c_3297,c_324])).

cnf(c_4321,plain,
    ( X0 != k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X1)))
    | k10_relat_1(sK6,X1) = X0 ),
    inference(resolution,[status(thm)],[c_4184,c_965])).

cnf(c_4322,plain,
    ( k10_relat_1(sK6,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_4321])).

cnf(c_2496,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | k10_relat_1(sK6,k1_xboole_0) = k10_relat_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_1616,c_324])).

cnf(c_16,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1415,plain,
    ( k1_xboole_0 != k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8460,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | k10_relat_1(sK6,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2496,c_1415])).

cnf(c_1665,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_4100,plain,
    ( r2_hidden(sK1(k1_xboole_0,X0),X0)
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_1665,c_8])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_311,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_312,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(sK4(X0,X1,sK6),X1) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_4104,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1665,c_312])).

cnf(c_12307,plain,
    ( k2_relat_1(k1_xboole_0) = k10_relat_1(sK6,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4100,c_4104])).

cnf(c_1931,plain,
    ( X0 != X1
    | k10_relat_1(X2,X3) != X1
    | k10_relat_1(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_2580,plain,
    ( X0 != k10_relat_1(X1,X2)
    | k10_relat_1(X3,X4) = X0
    | k10_relat_1(X3,X4) != k10_relat_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1931])).

cnf(c_5090,plain,
    ( k10_relat_1(X0,X1) != k10_relat_1(X2,X3)
    | k10_relat_1(X0,X1) = k2_relat_1(X4)
    | k2_relat_1(X4) != k10_relat_1(X2,X3) ),
    inference(instantiation,[status(thm)],[c_2580])).

cnf(c_11217,plain,
    ( k10_relat_1(X0,X1) != k10_relat_1(sK6,X2)
    | k10_relat_1(X0,X1) = k2_relat_1(X3)
    | k2_relat_1(X3) != k10_relat_1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_5090])).

cnf(c_13093,plain,
    ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X0))) != k10_relat_1(sK6,X0)
    | k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X0))) = k2_relat_1(X1)
    | k2_relat_1(X1) != k10_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_11217])).

cnf(c_13094,plain,
    ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) != k10_relat_1(sK6,k1_xboole_0)
    | k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) = k2_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k10_relat_1(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13093])).

cnf(c_5065,plain,
    ( X0 != X1
    | X0 = k10_relat_1(X2,X3)
    | k10_relat_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_15490,plain,
    ( X0 = k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X1)))
    | X0 != k2_relat_1(X2)
    | k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X1))) != k2_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_5065])).

cnf(c_15493,plain,
    ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0)))
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_15490])).

cnf(c_21693,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4434,c_53,c_325,c_983,c_2174,c_2184,c_2495,c_3027,c_4322,c_8460,c_12307,c_13094,c_15493])).

cnf(c_5798,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
    | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | ~ r1_xboole_0(k10_relat_1(sK6,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5800,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k1_xboole_0)
    | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5798])).

cnf(c_966,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3328,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_966,c_964])).

cnf(c_4176,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3297,c_17])).

cnf(c_4862,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | ~ r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_3328,c_4176])).

cnf(c_4864,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4862])).

cnf(c_1579,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),X0)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | ~ r1_xboole_0(k2_relat_1(sK6),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3143,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | ~ r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_268,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_280,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_268,c_9])).

cnf(c_1550,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_3072,plain,
    ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_1612,plain,
    ( k10_relat_1(sK6,sK5) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_1613,plain,
    ( k10_relat_1(sK6,sK5) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK6,sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1584,plain,
    ( r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_154,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_460,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | k10_relat_1(sK6,sK5) != k1_xboole_0
    | k2_relat_1(sK6) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_154])).

cnf(c_461,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_450,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k10_relat_1(sK6,sK5) != k1_xboole_0
    | k2_relat_1(sK6) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_154])).

cnf(c_451,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23141,c_23143,c_21693,c_5800,c_4864,c_3143,c_3072,c_1613,c_1584,c_983,c_461,c_451,c_53])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.59/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/2.00  
% 11.59/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.59/2.00  
% 11.59/2.00  ------  iProver source info
% 11.59/2.00  
% 11.59/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.59/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.59/2.00  git: non_committed_changes: false
% 11.59/2.00  git: last_make_outside_of_git: false
% 11.59/2.00  
% 11.59/2.00  ------ 
% 11.59/2.00  ------ Parsing...
% 11.59/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.59/2.00  
% 11.59/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.59/2.00  
% 11.59/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.59/2.00  
% 11.59/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.59/2.00  ------ Proving...
% 11.59/2.00  ------ Problem Properties 
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  clauses                                 18
% 11.59/2.00  conjectures                             2
% 11.59/2.00  EPR                                     2
% 11.59/2.00  Horn                                    14
% 11.59/2.00  unary                                   2
% 11.59/2.00  binary                                  12
% 11.59/2.00  lits                                    38
% 11.59/2.00  lits eq                                 7
% 11.59/2.00  fd_pure                                 0
% 11.59/2.00  fd_pseudo                               0
% 11.59/2.00  fd_cond                                 0
% 11.59/2.00  fd_pseudo_cond                          2
% 11.59/2.00  AC symbols                              0
% 11.59/2.00  
% 11.59/2.00  ------ Input Options Time Limit: Unbounded
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  ------ 
% 11.59/2.00  Current options:
% 11.59/2.00  ------ 
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  ------ Proving...
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  % SZS status Theorem for theBenchmark.p
% 11.59/2.00  
% 11.59/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.59/2.00  
% 11.59/2.00  fof(f9,conjecture,(
% 11.59/2.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f10,negated_conjecture,(
% 11.59/2.00    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 11.59/2.00    inference(negated_conjecture,[],[f9])).
% 11.59/2.00  
% 11.59/2.00  fof(f16,plain,(
% 11.59/2.00    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 11.59/2.00    inference(ennf_transformation,[],[f10])).
% 11.59/2.00  
% 11.59/2.00  fof(f30,plain,(
% 11.59/2.00    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 11.59/2.00    inference(nnf_transformation,[],[f16])).
% 11.59/2.00  
% 11.59/2.00  fof(f31,plain,(
% 11.59/2.00    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 11.59/2.00    inference(flattening,[],[f30])).
% 11.59/2.00  
% 11.59/2.00  fof(f32,plain,(
% 11.59/2.00    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6))),
% 11.59/2.00    introduced(choice_axiom,[])).
% 11.59/2.00  
% 11.59/2.00  fof(f33,plain,(
% 11.59/2.00    (~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6)),
% 11.59/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f32])).
% 11.59/2.00  
% 11.59/2.00  fof(f52,plain,(
% 11.59/2.00    r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)),
% 11.59/2.00    inference(cnf_transformation,[],[f33])).
% 11.59/2.00  
% 11.59/2.00  fof(f1,axiom,(
% 11.59/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f17,plain,(
% 11.59/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.59/2.00    inference(nnf_transformation,[],[f1])).
% 11.59/2.00  
% 11.59/2.00  fof(f34,plain,(
% 11.59/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f17])).
% 11.59/2.00  
% 11.59/2.00  fof(f5,axiom,(
% 11.59/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f41,plain,(
% 11.59/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.59/2.00    inference(cnf_transformation,[],[f5])).
% 11.59/2.00  
% 11.59/2.00  fof(f55,plain,(
% 11.59/2.00    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.59/2.00    inference(definition_unfolding,[],[f34,f41])).
% 11.59/2.00  
% 11.59/2.00  fof(f35,plain,(
% 11.59/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.59/2.00    inference(cnf_transformation,[],[f17])).
% 11.59/2.00  
% 11.59/2.00  fof(f54,plain,(
% 11.59/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.59/2.00    inference(definition_unfolding,[],[f35,f41])).
% 11.59/2.00  
% 11.59/2.00  fof(f2,axiom,(
% 11.59/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f11,plain,(
% 11.59/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.59/2.00    inference(rectify,[],[f2])).
% 11.59/2.00  
% 11.59/2.00  fof(f12,plain,(
% 11.59/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.59/2.00    inference(ennf_transformation,[],[f11])).
% 11.59/2.00  
% 11.59/2.00  fof(f18,plain,(
% 11.59/2.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.59/2.00    introduced(choice_axiom,[])).
% 11.59/2.00  
% 11.59/2.00  fof(f19,plain,(
% 11.59/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.59/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f18])).
% 11.59/2.00  
% 11.59/2.00  fof(f37,plain,(
% 11.59/2.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f19])).
% 11.59/2.00  
% 11.59/2.00  fof(f36,plain,(
% 11.59/2.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f19])).
% 11.59/2.00  
% 11.59/2.00  fof(f38,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f19])).
% 11.59/2.00  
% 11.59/2.00  fof(f3,axiom,(
% 11.59/2.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f39,plain,(
% 11.59/2.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f3])).
% 11.59/2.00  
% 11.59/2.00  fof(f8,axiom,(
% 11.59/2.00    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f15,plain,(
% 11.59/2.00    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.59/2.00    inference(ennf_transformation,[],[f8])).
% 11.59/2.00  
% 11.59/2.00  fof(f50,plain,(
% 11.59/2.00    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f15])).
% 11.59/2.00  
% 11.59/2.00  fof(f56,plain,(
% 11.59/2.00    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 11.59/2.00    inference(definition_unfolding,[],[f50,f41])).
% 11.59/2.00  
% 11.59/2.00  fof(f51,plain,(
% 11.59/2.00    v1_relat_1(sK6)),
% 11.59/2.00    inference(cnf_transformation,[],[f33])).
% 11.59/2.00  
% 11.59/2.00  fof(f6,axiom,(
% 11.59/2.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f20,plain,(
% 11.59/2.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 11.59/2.00    inference(nnf_transformation,[],[f6])).
% 11.59/2.00  
% 11.59/2.00  fof(f21,plain,(
% 11.59/2.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 11.59/2.00    inference(rectify,[],[f20])).
% 11.59/2.00  
% 11.59/2.00  fof(f24,plain,(
% 11.59/2.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 11.59/2.00    introduced(choice_axiom,[])).
% 11.59/2.00  
% 11.59/2.00  fof(f23,plain,(
% 11.59/2.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 11.59/2.00    introduced(choice_axiom,[])).
% 11.59/2.00  
% 11.59/2.00  fof(f22,plain,(
% 11.59/2.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 11.59/2.00    introduced(choice_axiom,[])).
% 11.59/2.00  
% 11.59/2.00  fof(f25,plain,(
% 11.59/2.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 11.59/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f24,f23,f22])).
% 11.59/2.00  
% 11.59/2.00  fof(f44,plain,(
% 11.59/2.00    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f25])).
% 11.59/2.00  
% 11.59/2.00  fof(f4,axiom,(
% 11.59/2.00    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f13,plain,(
% 11.59/2.00    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 11.59/2.00    inference(ennf_transformation,[],[f4])).
% 11.59/2.00  
% 11.59/2.00  fof(f40,plain,(
% 11.59/2.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f13])).
% 11.59/2.00  
% 11.59/2.00  fof(f53,plain,(
% 11.59/2.00    ~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)),
% 11.59/2.00    inference(cnf_transformation,[],[f33])).
% 11.59/2.00  
% 11.59/2.00  fof(f7,axiom,(
% 11.59/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 11.59/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.59/2.00  
% 11.59/2.00  fof(f14,plain,(
% 11.59/2.00    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 11.59/2.00    inference(ennf_transformation,[],[f7])).
% 11.59/2.00  
% 11.59/2.00  fof(f26,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 11.59/2.00    inference(nnf_transformation,[],[f14])).
% 11.59/2.00  
% 11.59/2.00  fof(f27,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 11.59/2.00    inference(rectify,[],[f26])).
% 11.59/2.00  
% 11.59/2.00  fof(f28,plain,(
% 11.59/2.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 11.59/2.00    introduced(choice_axiom,[])).
% 11.59/2.00  
% 11.59/2.00  fof(f29,plain,(
% 11.59/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 11.59/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 11.59/2.00  
% 11.59/2.00  fof(f48,plain,(
% 11.59/2.00    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f29])).
% 11.59/2.00  
% 11.59/2.00  fof(f49,plain,(
% 11.59/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 11.59/2.00    inference(cnf_transformation,[],[f29])).
% 11.59/2.00  
% 11.59/2.00  fof(f43,plain,(
% 11.59/2.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 11.59/2.00    inference(cnf_transformation,[],[f25])).
% 11.59/2.00  
% 11.59/2.00  fof(f57,plain,(
% 11.59/2.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 11.59/2.00    inference(equality_resolution,[],[f43])).
% 11.59/2.00  
% 11.59/2.00  fof(f42,plain,(
% 11.59/2.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 11.59/2.00    inference(cnf_transformation,[],[f25])).
% 11.59/2.00  
% 11.59/2.00  fof(f58,plain,(
% 11.59/2.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 11.59/2.00    inference(equality_resolution,[],[f42])).
% 11.59/2.00  
% 11.59/2.00  cnf(c_964,plain,( X0 = X0 ),theory(equality) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_23141,plain,
% 11.59/2.00      ( sK3(sK6,sK0(k2_relat_1(sK6),sK5)) = sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_964]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_969,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.59/2.00      theory(equality) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_5785,plain,
% 11.59/2.00      ( r2_hidden(X0,X1)
% 11.59/2.00      | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 11.59/2.00      | X1 != k10_relat_1(sK6,sK5)
% 11.59/2.00      | X0 != sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_969]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_23140,plain,
% 11.59/2.00      ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
% 11.59/2.00      | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 11.59/2.00      | X0 != k10_relat_1(sK6,sK5)
% 11.59/2.00      | sK3(sK6,sK0(k2_relat_1(sK6),sK5)) != sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_5785]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_23143,plain,
% 11.59/2.00      ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 11.59/2.00      | r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k1_xboole_0)
% 11.59/2.00      | sK3(sK6,sK0(k2_relat_1(sK6),sK5)) != sK3(sK6,sK0(k2_relat_1(sK6),sK5))
% 11.59/2.00      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_23140]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_17,negated_conjecture,
% 11.59/2.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 11.59/2.00      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 11.59/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1414,plain,
% 11.59/2.00      ( k1_xboole_0 = k10_relat_1(sK6,sK5)
% 11.59/2.00      | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1,plain,
% 11.59/2.00      ( ~ r1_xboole_0(X0,X1)
% 11.59/2.00      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 11.59/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1425,plain,
% 11.59/2.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 11.59/2.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1616,plain,
% 11.59/2.00      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 11.59/2.00      | k1_setfam_1(k2_tarski(k2_relat_1(sK6),sK5)) = k1_xboole_0 ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1414,c_1425]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_0,plain,
% 11.59/2.00      ( r1_xboole_0(X0,X1)
% 11.59/2.00      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 11.59/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1426,plain,
% 11.59/2.00      ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
% 11.59/2.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2495,plain,
% 11.59/2.00      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 11.59/2.00      | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1616,c_1426]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3,plain,
% 11.59/2.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f37]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1423,plain,
% 11.59/2.00      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 11.59/2.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4,plain,
% 11.59/2.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f36]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1422,plain,
% 11.59/2.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.59/2.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1424,plain,
% 11.59/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.59/2.00      | r2_hidden(X0,X2) != iProver_top
% 11.59/2.00      | r1_xboole_0(X2,X1) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1774,plain,
% 11.59/2.00      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 11.59/2.00      | r1_xboole_0(X2,X0) != iProver_top
% 11.59/2.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1422,c_1424]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3456,plain,
% 11.59/2.00      ( r1_xboole_0(X0,X1) != iProver_top
% 11.59/2.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1423,c_1774]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4434,plain,
% 11.59/2.00      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 11.59/2.00      | r1_xboole_0(sK5,k2_relat_1(sK6)) = iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_2495,c_3456]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_5,plain,
% 11.59/2.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.59/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_53,plain,
% 11.59/2.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_15,plain,
% 11.59/2.00      ( ~ v1_relat_1(X0)
% 11.59/2.00      | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_18,negated_conjecture,
% 11.59/2.00      ( v1_relat_1(sK6) ),
% 11.59/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_323,plain,
% 11.59/2.00      ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 11.59/2.00      | sK6 != X0 ),
% 11.59/2.00      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_324,plain,
% 11.59/2.00      ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X0))) = k10_relat_1(sK6,X0) ),
% 11.59/2.00      inference(unflattening,[status(thm)],[c_323]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_325,plain,
% 11.59/2.00      ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) = k10_relat_1(sK6,k1_xboole_0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_324]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_983,plain,
% 11.59/2.00      ( k1_xboole_0 = k1_xboole_0 ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_964]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_965,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2173,plain,
% 11.59/2.00      ( k2_relat_1(X0) != X1
% 11.59/2.00      | k1_xboole_0 != X1
% 11.59/2.00      | k1_xboole_0 = k2_relat_1(X0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_965]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2174,plain,
% 11.59/2.00      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 11.59/2.00      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 11.59/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_2173]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_8,plain,
% 11.59/2.00      ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
% 11.59/2.00      | r2_hidden(sK1(X0,X1),X1)
% 11.59/2.00      | k2_relat_1(X0) = X1 ),
% 11.59/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1418,plain,
% 11.59/2.00      ( k2_relat_1(X0) = X1
% 11.59/2.00      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) = iProver_top
% 11.59/2.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1421,plain,
% 11.59/2.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_6,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k1_tarski(X0),X1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1420,plain,
% 11.59/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.59/2.00      | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1651,plain,
% 11.59/2.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1421,c_1420]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2178,plain,
% 11.59/2.00      ( k2_relat_1(k1_xboole_0) = X0
% 11.59/2.00      | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1418,c_1651]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2182,plain,
% 11.59/2.00      ( r2_hidden(sK1(k1_xboole_0,X0),X0)
% 11.59/2.00      | k2_relat_1(k1_xboole_0) = X0 ),
% 11.59/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2178]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2184,plain,
% 11.59/2.00      ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 11.59/2.00      | k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_2182]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3025,plain,
% 11.59/2.00      ( ~ r2_hidden(sK1(X0,X1),X1)
% 11.59/2.00      | ~ r2_hidden(sK1(X0,X1),X2)
% 11.59/2.00      | ~ r1_xboole_0(X1,X2) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3027,plain,
% 11.59/2.00      ( ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 11.59/2.00      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_3025]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3297,plain,
% 11.59/2.00      ( X0 != X1 | X1 = X0 ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_965,c_964]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4184,plain,
% 11.59/2.00      ( k10_relat_1(sK6,X0) = k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X0))) ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_3297,c_324]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4321,plain,
% 11.59/2.00      ( X0 != k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X1)))
% 11.59/2.00      | k10_relat_1(sK6,X1) = X0 ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_4184,c_965]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4322,plain,
% 11.59/2.00      ( k10_relat_1(sK6,k1_xboole_0) = k1_xboole_0
% 11.59/2.00      | k1_xboole_0 != k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_4321]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2496,plain,
% 11.59/2.00      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 11.59/2.00      | k10_relat_1(sK6,k1_xboole_0) = k10_relat_1(sK6,sK5) ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_1616,c_324]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_16,negated_conjecture,
% 11.59/2.00      ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
% 11.59/2.00      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 11.59/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1415,plain,
% 11.59/2.00      ( k1_xboole_0 != k10_relat_1(sK6,sK5)
% 11.59/2.00      | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 11.59/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_8460,plain,
% 11.59/2.00      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 11.59/2.00      | k10_relat_1(sK6,k1_xboole_0) != k1_xboole_0
% 11.59/2.00      | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 11.59/2.00      inference(superposition,[status(thm)],[c_2496,c_1415]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1665,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4100,plain,
% 11.59/2.00      ( r2_hidden(sK1(k1_xboole_0,X0),X0)
% 11.59/2.00      | k2_relat_1(k1_xboole_0) = X0 ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_1665,c_8]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_12,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 11.59/2.00      | r2_hidden(sK4(X0,X2,X1),X2)
% 11.59/2.00      | ~ v1_relat_1(X1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_311,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 11.59/2.00      | r2_hidden(sK4(X0,X2,X1),X2)
% 11.59/2.00      | sK6 != X1 ),
% 11.59/2.00      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_312,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
% 11.59/2.00      | r2_hidden(sK4(X0,X1,sK6),X1) ),
% 11.59/2.00      inference(unflattening,[status(thm)],[c_311]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4104,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,k1_xboole_0)) ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_1665,c_312]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_12307,plain,
% 11.59/2.00      ( k2_relat_1(k1_xboole_0) = k10_relat_1(sK6,k1_xboole_0) ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_4100,c_4104]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1931,plain,
% 11.59/2.00      ( X0 != X1 | k10_relat_1(X2,X3) != X1 | k10_relat_1(X2,X3) = X0 ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_965]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_2580,plain,
% 11.59/2.00      ( X0 != k10_relat_1(X1,X2)
% 11.59/2.00      | k10_relat_1(X3,X4) = X0
% 11.59/2.00      | k10_relat_1(X3,X4) != k10_relat_1(X1,X2) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_1931]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_5090,plain,
% 11.59/2.00      ( k10_relat_1(X0,X1) != k10_relat_1(X2,X3)
% 11.59/2.00      | k10_relat_1(X0,X1) = k2_relat_1(X4)
% 11.59/2.00      | k2_relat_1(X4) != k10_relat_1(X2,X3) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_2580]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_11217,plain,
% 11.59/2.00      ( k10_relat_1(X0,X1) != k10_relat_1(sK6,X2)
% 11.59/2.00      | k10_relat_1(X0,X1) = k2_relat_1(X3)
% 11.59/2.00      | k2_relat_1(X3) != k10_relat_1(sK6,X2) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_5090]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_13093,plain,
% 11.59/2.00      ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X0))) != k10_relat_1(sK6,X0)
% 11.59/2.00      | k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X0))) = k2_relat_1(X1)
% 11.59/2.00      | k2_relat_1(X1) != k10_relat_1(sK6,X0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_11217]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_13094,plain,
% 11.59/2.00      ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) != k10_relat_1(sK6,k1_xboole_0)
% 11.59/2.00      | k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) = k2_relat_1(k1_xboole_0)
% 11.59/2.00      | k2_relat_1(k1_xboole_0) != k10_relat_1(sK6,k1_xboole_0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_13093]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_5065,plain,
% 11.59/2.00      ( X0 != X1 | X0 = k10_relat_1(X2,X3) | k10_relat_1(X2,X3) != X1 ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_965]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_15490,plain,
% 11.59/2.00      ( X0 = k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X1)))
% 11.59/2.00      | X0 != k2_relat_1(X2)
% 11.59/2.00      | k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),X1))) != k2_relat_1(X2) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_5065]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_15493,plain,
% 11.59/2.00      ( k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0))) != k2_relat_1(k1_xboole_0)
% 11.59/2.00      | k1_xboole_0 = k10_relat_1(sK6,k1_setfam_1(k2_tarski(k2_relat_1(sK6),k1_xboole_0)))
% 11.59/2.00      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_15490]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_21693,plain,
% 11.59/2.00      ( k10_relat_1(sK6,sK5) = k1_xboole_0 ),
% 11.59/2.00      inference(global_propositional_subsumption,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_4434,c_53,c_325,c_983,c_2174,c_2184,c_2495,c_3027,
% 11.59/2.00                 c_4322,c_8460,c_12307,c_13094,c_15493]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_5798,plain,
% 11.59/2.00      ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
% 11.59/2.00      | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 11.59/2.00      | ~ r1_xboole_0(k10_relat_1(sK6,sK5),X0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_5800,plain,
% 11.59/2.00      ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 11.59/2.00      | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k1_xboole_0)
% 11.59/2.00      | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k1_xboole_0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_5798]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_966,plain,
% 11.59/2.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.59/2.00      theory(equality) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3328,plain,
% 11.59/2.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_966,c_964]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4176,plain,
% 11.59/2.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 11.59/2.00      | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_3297,c_17]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4862,plain,
% 11.59/2.00      ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
% 11.59/2.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 11.59/2.00      | ~ r1_xboole_0(k1_xboole_0,X0) ),
% 11.59/2.00      inference(resolution,[status(thm)],[c_3328,c_4176]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_4864,plain,
% 11.59/2.00      ( r1_xboole_0(k10_relat_1(sK6,sK5),k1_xboole_0)
% 11.59/2.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 11.59/2.00      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_4862]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1579,plain,
% 11.59/2.00      ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),X0)
% 11.59/2.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 11.59/2.00      | ~ r1_xboole_0(k2_relat_1(sK6),X0) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3143,plain,
% 11.59/2.00      ( ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 11.59/2.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 11.59/2.00      | ~ r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_1579]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_11,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,X1)
% 11.59/2.00      | r2_hidden(X2,k10_relat_1(X3,X1))
% 11.59/2.00      | ~ r2_hidden(X0,k2_relat_1(X3))
% 11.59/2.00      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 11.59/2.00      | ~ v1_relat_1(X3) ),
% 11.59/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_267,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,X1)
% 11.59/2.00      | r2_hidden(X2,k10_relat_1(X3,X1))
% 11.59/2.00      | ~ r2_hidden(X0,k2_relat_1(X3))
% 11.59/2.00      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 11.59/2.00      | sK6 != X3 ),
% 11.59/2.00      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_268,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,X1)
% 11.59/2.00      | r2_hidden(X2,k10_relat_1(sK6,X1))
% 11.59/2.00      | ~ r2_hidden(X0,k2_relat_1(sK6))
% 11.59/2.00      | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
% 11.59/2.00      inference(unflattening,[status(thm)],[c_267]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_9,plain,
% 11.59/2.00      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_280,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,X1)
% 11.59/2.00      | r2_hidden(X2,k10_relat_1(sK6,X1))
% 11.59/2.00      | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
% 11.59/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_268,c_9]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1550,plain,
% 11.59/2.00      ( r2_hidden(X0,k10_relat_1(sK6,sK5))
% 11.59/2.00      | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK6),sK5)),sK6)
% 11.59/2.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_280]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_3072,plain,
% 11.59/2.00      ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 11.59/2.00      | ~ r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
% 11.59/2.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_1550]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1612,plain,
% 11.59/2.00      ( k10_relat_1(sK6,sK5) != X0
% 11.59/2.00      | k1_xboole_0 != X0
% 11.59/2.00      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_965]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1613,plain,
% 11.59/2.00      ( k10_relat_1(sK6,sK5) != k1_xboole_0
% 11.59/2.00      | k1_xboole_0 = k10_relat_1(sK6,sK5)
% 11.59/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_1612]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_10,plain,
% 11.59/2.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.59/2.00      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 11.59/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_1584,plain,
% 11.59/2.00      ( r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
% 11.59/2.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) ),
% 11.59/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_154,plain,
% 11.59/2.00      ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
% 11.59/2.00      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 11.59/2.00      inference(prop_impl,[status(thm)],[c_16]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_460,plain,
% 11.59/2.00      ( r2_hidden(sK0(X0,X1),X1)
% 11.59/2.00      | k10_relat_1(sK6,sK5) != k1_xboole_0
% 11.59/2.00      | k2_relat_1(sK6) != X0
% 11.59/2.00      | sK5 != X1 ),
% 11.59/2.00      inference(resolution_lifted,[status(thm)],[c_3,c_154]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_461,plain,
% 11.59/2.00      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 11.59/2.00      | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
% 11.59/2.00      inference(unflattening,[status(thm)],[c_460]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_450,plain,
% 11.59/2.00      ( r2_hidden(sK0(X0,X1),X0)
% 11.59/2.00      | k10_relat_1(sK6,sK5) != k1_xboole_0
% 11.59/2.00      | k2_relat_1(sK6) != X0
% 11.59/2.00      | sK5 != X1 ),
% 11.59/2.00      inference(resolution_lifted,[status(thm)],[c_4,c_154]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(c_451,plain,
% 11.59/2.00      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 11.59/2.00      | k10_relat_1(sK6,sK5) != k1_xboole_0 ),
% 11.59/2.00      inference(unflattening,[status(thm)],[c_450]) ).
% 11.59/2.00  
% 11.59/2.00  cnf(contradiction,plain,
% 11.59/2.00      ( $false ),
% 11.59/2.00      inference(minisat,
% 11.59/2.00                [status(thm)],
% 11.59/2.00                [c_23141,c_23143,c_21693,c_5800,c_4864,c_3143,c_3072,
% 11.59/2.00                 c_1613,c_1584,c_983,c_461,c_451,c_53]) ).
% 11.59/2.00  
% 11.59/2.00  
% 11.59/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.59/2.00  
% 11.59/2.00  ------                               Statistics
% 11.59/2.00  
% 11.59/2.00  ------ Selected
% 11.59/2.00  
% 11.59/2.00  total_time:                             1.024
% 11.59/2.00  
%------------------------------------------------------------------------------
