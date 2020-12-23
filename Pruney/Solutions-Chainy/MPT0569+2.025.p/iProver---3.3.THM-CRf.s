%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:31 EST 2020

% Result     : Theorem 15.25s
% Output     : CNFRefutation 15.25s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 400 expanded)
%              Number of clauses        :   58 ( 123 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   20
%              Number of atoms          :  415 (1369 expanded)
%              Number of equality atoms :  108 ( 477 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f25])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
        & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 != k10_relat_1(sK7,sK6) )
    & ( r1_xboole_0(k2_relat_1(sK7),sK6)
      | k1_xboole_0 = k10_relat_1(sK7,sK6) )
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f39])).

fof(f65,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f64,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f62,f53])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_60385,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0)
    | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_setfam_1(k2_tarski(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_60387,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),k1_xboole_0)
    | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_setfam_1(k2_tarski(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_60385])).

cnf(c_282,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_47260,plain,
    ( sK4(sK7,sK1(k2_relat_1(sK7),sK6)) = sK4(sK7,sK1(k2_relat_1(sK7),sK6)) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_286,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_16181,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
    | X1 != k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6)))
    | X0 != sK4(sK7,sK1(k2_relat_1(sK7),sK6)) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_47259,plain,
    ( r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),X0)
    | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
    | X0 != k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6)))
    | sK4(sK7,sK1(k2_relat_1(sK7),sK6)) != sK4(sK7,sK1(k2_relat_1(sK7),sK6)) ),
    inference(instantiation,[status(thm)],[c_16181])).

cnf(c_47262,plain,
    ( ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
    | r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_xboole_0)
    | sK4(sK7,sK1(k2_relat_1(sK7),sK6)) != sK4(sK7,sK1(k2_relat_1(sK7),sK6))
    | k1_xboole_0 != k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
    inference(instantiation,[status(thm)],[c_47259])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_16186,plain,
    ( ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),X0)
    | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
    | r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_setfam_1(k2_tarski(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_16188,plain,
    ( ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
    | r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_setfam_1(k2_tarski(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),k1_xboole_0)))
    | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16186])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4069,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK7),sK6)),sK7)
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),X1)
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_5663,plain,
    ( r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,X0))
    | ~ r2_hidden(k4_tarski(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),sK1(k2_relat_1(sK7),sK6)),sK7)
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),X0)
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4069])).

cnf(c_14817,plain,
    ( r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
    | ~ r2_hidden(k4_tarski(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),sK1(k2_relat_1(sK7),sK6)),sK7)
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6)))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_5663])).

cnf(c_283,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_23,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2189,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | X0 != k10_relat_1(sK7,sK6)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_283,c_23])).

cnf(c_22,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
    | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_301,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1142,plain,
    ( k10_relat_1(sK7,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_1143,plain,
    ( k10_relat_1(sK7,sK6) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK7,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_828,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,sK6)
    | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_843,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1149,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_828,c_843])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_827,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_831,plain,
    ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1251,plain,
    ( k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),X0))) = k10_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_827,c_831])).

cnf(c_1630,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0
    | k10_relat_1(sK7,k1_xboole_0) = k10_relat_1(sK7,sK6) ),
    inference(superposition,[status(thm)],[c_1149,c_1251])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_830,plain,
    ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1119,plain,
    ( k10_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_827,c_830])).

cnf(c_1633,plain,
    ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1630,c_1119])).

cnf(c_2529,plain,
    ( X0 != k10_relat_1(sK7,sK6)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2189,c_22,c_301,c_1143,c_1633])).

cnf(c_2539,plain,
    ( ~ v1_relat_1(sK7)
    | k1_xboole_0 = k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
    inference(resolution,[status(thm)],[c_2529,c_20])).

cnf(c_2822,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2539,c_24])).

cnf(c_3302,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_286,c_2822])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_842,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1868,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_842])).

cnf(c_1869,plain,
    ( ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1868])).

cnf(c_4152,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
    | X1 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3302,c_11,c_1869])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1374,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_4186,plain,
    ( r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0)
    | X1 != sK1(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0) ),
    inference(resolution,[status(thm)],[c_4152,c_1374])).

cnf(c_4689,plain,
    ( r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0) ),
    inference(resolution,[status(thm)],[c_4186,c_282])).

cnf(c_4691,plain,
    ( r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4689])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4066,plain,
    ( r2_hidden(k4_tarski(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),sK1(k2_relat_1(sK7),sK6)),sK7)
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2654,plain,
    ( r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
    | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1064,plain,
    ( r1_xboole_0(k2_relat_1(sK7),sK6)
    | r2_hidden(sK1(k2_relat_1(sK7),sK6),k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60387,c_47260,c_47262,c_16188,c_14817,c_4691,c_4066,c_2654,c_2539,c_1633,c_1143,c_1064,c_301,c_22,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:05:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.33  % Running in FOF mode
% 15.25/2.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.25/2.47  
% 15.25/2.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.25/2.47  
% 15.25/2.47  ------  iProver source info
% 15.25/2.47  
% 15.25/2.47  git: date: 2020-06-30 10:37:57 +0100
% 15.25/2.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.25/2.47  git: non_committed_changes: false
% 15.25/2.47  git: last_make_outside_of_git: false
% 15.25/2.47  
% 15.25/2.47  ------ 
% 15.25/2.47  ------ Parsing...
% 15.25/2.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.25/2.47  
% 15.25/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.25/2.47  
% 15.25/2.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.25/2.47  
% 15.25/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.25/2.47  ------ Proving...
% 15.25/2.47  ------ Problem Properties 
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  clauses                                 25
% 15.25/2.47  conjectures                             3
% 15.25/2.47  EPR                                     2
% 15.25/2.47  Horn                                    20
% 15.25/2.47  unary                                   3
% 15.25/2.47  binary                                  12
% 15.25/2.47  lits                                    60
% 15.25/2.47  lits eq                                 12
% 15.25/2.47  fd_pure                                 0
% 15.25/2.47  fd_pseudo                               0
% 15.25/2.47  fd_cond                                 0
% 15.25/2.47  fd_pseudo_cond                          5
% 15.25/2.47  AC symbols                              0
% 15.25/2.47  
% 15.25/2.47  ------ Input Options Time Limit: Unbounded
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  ------ 
% 15.25/2.47  Current options:
% 15.25/2.47  ------ 
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  ------ Proving...
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  % SZS status Theorem for theBenchmark.p
% 15.25/2.47  
% 15.25/2.47  % SZS output start CNFRefutation for theBenchmark.p
% 15.25/2.47  
% 15.25/2.47  fof(f3,axiom,(
% 15.25/2.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f13,plain,(
% 15.25/2.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.25/2.47    inference(rectify,[],[f3])).
% 15.25/2.47  
% 15.25/2.47  fof(f14,plain,(
% 15.25/2.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.25/2.47    inference(ennf_transformation,[],[f13])).
% 15.25/2.47  
% 15.25/2.47  fof(f25,plain,(
% 15.25/2.47    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f26,plain,(
% 15.25/2.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.25/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f25])).
% 15.25/2.47  
% 15.25/2.47  fof(f50,plain,(
% 15.25/2.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f26])).
% 15.25/2.47  
% 15.25/2.47  fof(f6,axiom,(
% 15.25/2.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f53,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.25/2.47    inference(cnf_transformation,[],[f6])).
% 15.25/2.47  
% 15.25/2.47  fof(f75,plain,(
% 15.25/2.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 15.25/2.47    inference(definition_unfolding,[],[f50,f53])).
% 15.25/2.47  
% 15.25/2.47  fof(f1,axiom,(
% 15.25/2.47    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f19,plain,(
% 15.25/2.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.25/2.47    inference(nnf_transformation,[],[f1])).
% 15.25/2.47  
% 15.25/2.47  fof(f20,plain,(
% 15.25/2.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.25/2.47    inference(flattening,[],[f19])).
% 15.25/2.47  
% 15.25/2.47  fof(f21,plain,(
% 15.25/2.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.25/2.47    inference(rectify,[],[f20])).
% 15.25/2.47  
% 15.25/2.47  fof(f22,plain,(
% 15.25/2.47    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f23,plain,(
% 15.25/2.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.25/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 15.25/2.47  
% 15.25/2.47  fof(f43,plain,(
% 15.25/2.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 15.25/2.47    inference(cnf_transformation,[],[f23])).
% 15.25/2.47  
% 15.25/2.47  fof(f70,plain,(
% 15.25/2.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 15.25/2.47    inference(definition_unfolding,[],[f43,f53])).
% 15.25/2.47  
% 15.25/2.47  fof(f79,plain,(
% 15.25/2.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 15.25/2.47    inference(equality_resolution,[],[f70])).
% 15.25/2.47  
% 15.25/2.47  fof(f8,axiom,(
% 15.25/2.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f15,plain,(
% 15.25/2.47    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 15.25/2.47    inference(ennf_transformation,[],[f8])).
% 15.25/2.47  
% 15.25/2.47  fof(f33,plain,(
% 15.25/2.47    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 15.25/2.47    inference(nnf_transformation,[],[f15])).
% 15.25/2.47  
% 15.25/2.47  fof(f34,plain,(
% 15.25/2.47    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 15.25/2.47    inference(rectify,[],[f33])).
% 15.25/2.47  
% 15.25/2.47  fof(f35,plain,(
% 15.25/2.47    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))))),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f36,plain,(
% 15.25/2.47    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 15.25/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 15.25/2.47  
% 15.25/2.47  fof(f61,plain,(
% 15.25/2.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f36])).
% 15.25/2.47  
% 15.25/2.47  fof(f11,conjecture,(
% 15.25/2.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f12,negated_conjecture,(
% 15.25/2.47    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 15.25/2.47    inference(negated_conjecture,[],[f11])).
% 15.25/2.47  
% 15.25/2.47  fof(f18,plain,(
% 15.25/2.47    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 15.25/2.47    inference(ennf_transformation,[],[f12])).
% 15.25/2.47  
% 15.25/2.47  fof(f37,plain,(
% 15.25/2.47    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 15.25/2.47    inference(nnf_transformation,[],[f18])).
% 15.25/2.47  
% 15.25/2.47  fof(f38,plain,(
% 15.25/2.47    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 15.25/2.47    inference(flattening,[],[f37])).
% 15.25/2.47  
% 15.25/2.47  fof(f39,plain,(
% 15.25/2.47    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7))),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f40,plain,(
% 15.25/2.47    (~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)) & (r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)) & v1_relat_1(sK7)),
% 15.25/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f39])).
% 15.25/2.47  
% 15.25/2.47  fof(f65,plain,(
% 15.25/2.47    r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 = k10_relat_1(sK7,sK6)),
% 15.25/2.47    inference(cnf_transformation,[],[f40])).
% 15.25/2.47  
% 15.25/2.47  fof(f66,plain,(
% 15.25/2.47    ~r1_xboole_0(k2_relat_1(sK7),sK6) | k1_xboole_0 != k10_relat_1(sK7,sK6)),
% 15.25/2.47    inference(cnf_transformation,[],[f40])).
% 15.25/2.47  
% 15.25/2.47  fof(f2,axiom,(
% 15.25/2.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f24,plain,(
% 15.25/2.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.25/2.47    inference(nnf_transformation,[],[f2])).
% 15.25/2.47  
% 15.25/2.47  fof(f47,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f24])).
% 15.25/2.47  
% 15.25/2.47  fof(f74,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 15.25/2.47    inference(definition_unfolding,[],[f47,f53])).
% 15.25/2.47  
% 15.25/2.47  fof(f64,plain,(
% 15.25/2.47    v1_relat_1(sK7)),
% 15.25/2.47    inference(cnf_transformation,[],[f40])).
% 15.25/2.47  
% 15.25/2.47  fof(f9,axiom,(
% 15.25/2.47    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f16,plain,(
% 15.25/2.47    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.25/2.47    inference(ennf_transformation,[],[f9])).
% 15.25/2.47  
% 15.25/2.47  fof(f62,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f16])).
% 15.25/2.47  
% 15.25/2.47  fof(f78,plain,(
% 15.25/2.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 15.25/2.47    inference(definition_unfolding,[],[f62,f53])).
% 15.25/2.47  
% 15.25/2.47  fof(f10,axiom,(
% 15.25/2.47    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f17,plain,(
% 15.25/2.47    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 15.25/2.47    inference(ennf_transformation,[],[f10])).
% 15.25/2.47  
% 15.25/2.47  fof(f63,plain,(
% 15.25/2.47    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f17])).
% 15.25/2.47  
% 15.25/2.47  fof(f5,axiom,(
% 15.25/2.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f52,plain,(
% 15.25/2.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f5])).
% 15.25/2.47  
% 15.25/2.47  fof(f4,axiom,(
% 15.25/2.47    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f51,plain,(
% 15.25/2.47    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.25/2.47    inference(cnf_transformation,[],[f4])).
% 15.25/2.47  
% 15.25/2.47  fof(f77,plain,(
% 15.25/2.47    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 15.25/2.47    inference(definition_unfolding,[],[f51,f53])).
% 15.25/2.47  
% 15.25/2.47  fof(f41,plain,(
% 15.25/2.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.25/2.47    inference(cnf_transformation,[],[f23])).
% 15.25/2.47  
% 15.25/2.47  fof(f72,plain,(
% 15.25/2.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 15.25/2.47    inference(definition_unfolding,[],[f41,f53])).
% 15.25/2.47  
% 15.25/2.47  fof(f81,plain,(
% 15.25/2.47    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 15.25/2.47    inference(equality_resolution,[],[f72])).
% 15.25/2.47  
% 15.25/2.47  fof(f49,plain,(
% 15.25/2.47    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 15.25/2.47    inference(cnf_transformation,[],[f26])).
% 15.25/2.47  
% 15.25/2.47  fof(f76,plain,(
% 15.25/2.47    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 15.25/2.47    inference(definition_unfolding,[],[f49,f53])).
% 15.25/2.47  
% 15.25/2.47  fof(f7,axiom,(
% 15.25/2.47    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 15.25/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.25/2.47  
% 15.25/2.47  fof(f27,plain,(
% 15.25/2.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 15.25/2.47    inference(nnf_transformation,[],[f7])).
% 15.25/2.47  
% 15.25/2.47  fof(f28,plain,(
% 15.25/2.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.25/2.47    inference(rectify,[],[f27])).
% 15.25/2.47  
% 15.25/2.47  fof(f31,plain,(
% 15.25/2.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f30,plain,(
% 15.25/2.47    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0))) )),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f29,plain,(
% 15.25/2.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 15.25/2.47    introduced(choice_axiom,[])).
% 15.25/2.47  
% 15.25/2.47  fof(f32,plain,(
% 15.25/2.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.25/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 15.25/2.47  
% 15.25/2.47  fof(f54,plain,(
% 15.25/2.47    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 15.25/2.47    inference(cnf_transformation,[],[f32])).
% 15.25/2.47  
% 15.25/2.47  fof(f83,plain,(
% 15.25/2.47    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 15.25/2.47    inference(equality_resolution,[],[f54])).
% 15.25/2.47  
% 15.25/2.47  cnf(c_8,plain,
% 15.25/2.47      ( ~ r1_xboole_0(X0,X1)
% 15.25/2.47      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 15.25/2.47      inference(cnf_transformation,[],[f75]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_60385,plain,
% 15.25/2.47      ( ~ r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0)
% 15.25/2.47      | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_setfam_1(k2_tarski(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0))) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_8]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_60387,plain,
% 15.25/2.47      ( ~ r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),k1_xboole_0)
% 15.25/2.47      | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_setfam_1(k2_tarski(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),k1_xboole_0))) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_60385]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_282,plain,( X0 = X0 ),theory(equality) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_47260,plain,
% 15.25/2.47      ( sK4(sK7,sK1(k2_relat_1(sK7),sK6)) = sK4(sK7,sK1(k2_relat_1(sK7),sK6)) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_282]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_286,plain,
% 15.25/2.47      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.25/2.47      theory(equality) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_16181,plain,
% 15.25/2.47      ( r2_hidden(X0,X1)
% 15.25/2.47      | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
% 15.25/2.47      | X1 != k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6)))
% 15.25/2.47      | X0 != sK4(sK7,sK1(k2_relat_1(sK7),sK6)) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_286]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_47259,plain,
% 15.25/2.47      ( r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),X0)
% 15.25/2.47      | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
% 15.25/2.47      | X0 != k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6)))
% 15.25/2.47      | sK4(sK7,sK1(k2_relat_1(sK7),sK6)) != sK4(sK7,sK1(k2_relat_1(sK7),sK6)) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_16181]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_47262,plain,
% 15.25/2.47      ( ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
% 15.25/2.47      | r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_xboole_0)
% 15.25/2.47      | sK4(sK7,sK1(k2_relat_1(sK7),sK6)) != sK4(sK7,sK1(k2_relat_1(sK7),sK6))
% 15.25/2.47      | k1_xboole_0 != k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_47259]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_3,plain,
% 15.25/2.47      ( ~ r2_hidden(X0,X1)
% 15.25/2.47      | ~ r2_hidden(X0,X2)
% 15.25/2.47      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 15.25/2.47      inference(cnf_transformation,[],[f79]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_16186,plain,
% 15.25/2.47      ( ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),X0)
% 15.25/2.47      | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
% 15.25/2.47      | r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_setfam_1(k2_tarski(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0))) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_3]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_16188,plain,
% 15.25/2.47      ( ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
% 15.25/2.47      | r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_setfam_1(k2_tarski(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),k1_xboole_0)))
% 15.25/2.47      | ~ r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k1_xboole_0) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_16186]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_16,plain,
% 15.25/2.47      ( ~ r2_hidden(X0,X1)
% 15.25/2.47      | r2_hidden(X2,k10_relat_1(X3,X1))
% 15.25/2.47      | ~ r2_hidden(X0,k2_relat_1(X3))
% 15.25/2.47      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 15.25/2.47      | ~ v1_relat_1(X3) ),
% 15.25/2.47      inference(cnf_transformation,[],[f61]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_4069,plain,
% 15.25/2.47      ( r2_hidden(X0,k10_relat_1(sK7,X1))
% 15.25/2.47      | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK7),sK6)),sK7)
% 15.25/2.47      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),X1)
% 15.25/2.47      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 15.25/2.47      | ~ v1_relat_1(sK7) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_16]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_5663,plain,
% 15.25/2.47      ( r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,X0))
% 15.25/2.47      | ~ r2_hidden(k4_tarski(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),sK1(k2_relat_1(sK7),sK6)),sK7)
% 15.25/2.47      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),X0)
% 15.25/2.47      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 15.25/2.47      | ~ v1_relat_1(sK7) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_4069]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_14817,plain,
% 15.25/2.47      ( r2_hidden(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
% 15.25/2.47      | ~ r2_hidden(k4_tarski(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),sK1(k2_relat_1(sK7),sK6)),sK7)
% 15.25/2.47      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 15.25/2.47      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6)))
% 15.25/2.47      | ~ v1_relat_1(sK7) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_5663]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_283,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_23,negated_conjecture,
% 15.25/2.47      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 15.25/2.47      | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
% 15.25/2.47      inference(cnf_transformation,[],[f65]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_2189,plain,
% 15.25/2.47      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 15.25/2.47      | X0 != k10_relat_1(sK7,sK6)
% 15.25/2.47      | k1_xboole_0 = X0 ),
% 15.25/2.47      inference(resolution,[status(thm)],[c_283,c_23]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_22,negated_conjecture,
% 15.25/2.47      ( ~ r1_xboole_0(k2_relat_1(sK7),sK6)
% 15.25/2.47      | k1_xboole_0 != k10_relat_1(sK7,sK6) ),
% 15.25/2.47      inference(cnf_transformation,[],[f66]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_301,plain,
% 15.25/2.47      ( k1_xboole_0 = k1_xboole_0 ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_282]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1142,plain,
% 15.25/2.47      ( k10_relat_1(sK7,sK6) != X0
% 15.25/2.47      | k1_xboole_0 != X0
% 15.25/2.47      | k1_xboole_0 = k10_relat_1(sK7,sK6) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_283]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1143,plain,
% 15.25/2.47      ( k10_relat_1(sK7,sK6) != k1_xboole_0
% 15.25/2.47      | k1_xboole_0 = k10_relat_1(sK7,sK6)
% 15.25/2.47      | k1_xboole_0 != k1_xboole_0 ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_1142]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_828,plain,
% 15.25/2.47      ( k1_xboole_0 = k10_relat_1(sK7,sK6)
% 15.25/2.47      | r1_xboole_0(k2_relat_1(sK7),sK6) = iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_7,plain,
% 15.25/2.47      ( ~ r1_xboole_0(X0,X1)
% 15.25/2.47      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 15.25/2.47      inference(cnf_transformation,[],[f74]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_843,plain,
% 15.25/2.47      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 15.25/2.47      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1149,plain,
% 15.25/2.47      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 15.25/2.47      | k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6)) = k1_xboole_0 ),
% 15.25/2.47      inference(superposition,[status(thm)],[c_828,c_843]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_24,negated_conjecture,
% 15.25/2.47      ( v1_relat_1(sK7) ),
% 15.25/2.47      inference(cnf_transformation,[],[f64]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_827,plain,
% 15.25/2.47      ( v1_relat_1(sK7) = iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_20,plain,
% 15.25/2.47      ( ~ v1_relat_1(X0)
% 15.25/2.47      | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 15.25/2.47      inference(cnf_transformation,[],[f78]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_831,plain,
% 15.25/2.47      ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 15.25/2.47      | v1_relat_1(X0) != iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1251,plain,
% 15.25/2.47      ( k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),X0))) = k10_relat_1(sK7,X0) ),
% 15.25/2.47      inference(superposition,[status(thm)],[c_827,c_831]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1630,plain,
% 15.25/2.47      ( k10_relat_1(sK7,sK6) = k1_xboole_0
% 15.25/2.47      | k10_relat_1(sK7,k1_xboole_0) = k10_relat_1(sK7,sK6) ),
% 15.25/2.47      inference(superposition,[status(thm)],[c_1149,c_1251]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_21,plain,
% 15.25/2.47      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.25/2.47      inference(cnf_transformation,[],[f63]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_830,plain,
% 15.25/2.47      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 15.25/2.47      | v1_relat_1(X0) != iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1119,plain,
% 15.25/2.47      ( k10_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 15.25/2.47      inference(superposition,[status(thm)],[c_827,c_830]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1633,plain,
% 15.25/2.47      ( k10_relat_1(sK7,sK6) = k1_xboole_0 ),
% 15.25/2.47      inference(light_normalisation,[status(thm)],[c_1630,c_1119]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_2529,plain,
% 15.25/2.47      ( X0 != k10_relat_1(sK7,sK6) | k1_xboole_0 = X0 ),
% 15.25/2.47      inference(global_propositional_subsumption,
% 15.25/2.47                [status(thm)],
% 15.25/2.47                [c_2189,c_22,c_301,c_1143,c_1633]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_2539,plain,
% 15.25/2.47      ( ~ v1_relat_1(sK7)
% 15.25/2.47      | k1_xboole_0 = k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
% 15.25/2.47      inference(resolution,[status(thm)],[c_2529,c_20]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_2822,plain,
% 15.25/2.47      ( k1_xboole_0 = k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
% 15.25/2.47      inference(global_propositional_subsumption,
% 15.25/2.47                [status(thm)],
% 15.25/2.47                [c_2539,c_24]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_3302,plain,
% 15.25/2.47      ( ~ r2_hidden(X0,k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
% 15.25/2.47      | r2_hidden(X1,k1_xboole_0)
% 15.25/2.47      | X1 != X0 ),
% 15.25/2.47      inference(resolution,[status(thm)],[c_286,c_2822]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_11,plain,
% 15.25/2.47      ( r1_xboole_0(X0,k1_xboole_0) ),
% 15.25/2.47      inference(cnf_transformation,[],[f52]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_10,plain,
% 15.25/2.47      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.25/2.47      inference(cnf_transformation,[],[f77]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_842,plain,
% 15.25/2.47      ( r1_xboole_0(X0,X1) != iProver_top
% 15.25/2.47      | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
% 15.25/2.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1868,plain,
% 15.25/2.47      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 15.25/2.47      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 15.25/2.47      inference(superposition,[status(thm)],[c_10,c_842]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1869,plain,
% 15.25/2.47      ( ~ r1_xboole_0(X0,k1_xboole_0) | ~ r2_hidden(X1,k1_xboole_0) ),
% 15.25/2.47      inference(predicate_to_equality_rev,[status(thm)],[c_1868]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_4152,plain,
% 15.25/2.47      ( ~ r2_hidden(X0,k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))))
% 15.25/2.47      | X1 != X0 ),
% 15.25/2.47      inference(global_propositional_subsumption,
% 15.25/2.47                [status(thm)],
% 15.25/2.47                [c_3302,c_11,c_1869]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_5,plain,
% 15.25/2.47      ( r2_hidden(X0,X1)
% 15.25/2.47      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 15.25/2.47      inference(cnf_transformation,[],[f81]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_9,plain,
% 15.25/2.47      ( r1_xboole_0(X0,X1)
% 15.25/2.47      | r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ),
% 15.25/2.47      inference(cnf_transformation,[],[f76]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1374,plain,
% 15.25/2.47      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 15.25/2.47      inference(resolution,[status(thm)],[c_5,c_9]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_4186,plain,
% 15.25/2.47      ( r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0)
% 15.25/2.47      | X1 != sK1(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0) ),
% 15.25/2.47      inference(resolution,[status(thm)],[c_4152,c_1374]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_4689,plain,
% 15.25/2.47      ( r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),X0) ),
% 15.25/2.47      inference(resolution,[status(thm)],[c_4186,c_282]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_4691,plain,
% 15.25/2.47      ( r1_xboole_0(k10_relat_1(sK7,k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))),k1_xboole_0) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_4689]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_15,plain,
% 15.25/2.47      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.25/2.47      | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
% 15.25/2.47      inference(cnf_transformation,[],[f83]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_4066,plain,
% 15.25/2.47      ( r2_hidden(k4_tarski(sK4(sK7,sK1(k2_relat_1(sK7),sK6)),sK1(k2_relat_1(sK7),sK6)),sK7)
% 15.25/2.47      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7)) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_15]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_2654,plain,
% 15.25/2.47      ( r2_hidden(sK1(k2_relat_1(sK7),sK6),k2_relat_1(sK7))
% 15.25/2.47      | ~ r2_hidden(sK1(k2_relat_1(sK7),sK6),k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_5]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(c_1064,plain,
% 15.25/2.47      ( r1_xboole_0(k2_relat_1(sK7),sK6)
% 15.25/2.47      | r2_hidden(sK1(k2_relat_1(sK7),sK6),k1_setfam_1(k2_tarski(k2_relat_1(sK7),sK6))) ),
% 15.25/2.47      inference(instantiation,[status(thm)],[c_9]) ).
% 15.25/2.47  
% 15.25/2.47  cnf(contradiction,plain,
% 15.25/2.47      ( $false ),
% 15.25/2.47      inference(minisat,
% 15.25/2.47                [status(thm)],
% 15.25/2.47                [c_60387,c_47260,c_47262,c_16188,c_14817,c_4691,c_4066,
% 15.25/2.47                 c_2654,c_2539,c_1633,c_1143,c_1064,c_301,c_22,c_24]) ).
% 15.25/2.47  
% 15.25/2.47  
% 15.25/2.47  % SZS output end CNFRefutation for theBenchmark.p
% 15.25/2.47  
% 15.25/2.47  ------                               Statistics
% 15.25/2.47  
% 15.25/2.47  ------ Selected
% 15.25/2.47  
% 15.25/2.47  total_time:                             1.734
% 15.25/2.47  
%------------------------------------------------------------------------------
