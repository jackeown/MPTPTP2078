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
% DateTime   : Thu Dec  3 11:47:32 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 356 expanded)
%              Number of clauses        :   71 ( 120 expanded)
%              Number of leaves         :   20 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  382 (1185 expanded)
%              Number of equality atoms :  142 ( 476 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

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
   => ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 != k10_relat_1(sK6,sK5) )
      & ( r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 = k10_relat_1(sK6,sK5) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 != k10_relat_1(sK6,sK5) )
    & ( r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 = k10_relat_1(sK6,sK5) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f39])).

fof(f66,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f19])).

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
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f46])).

fof(f68,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f12])).

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
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2766,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | X1 != k10_relat_1(sK6,sK5)
    | X0 != sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_7290,plain,
    ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
    | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | X0 != k10_relat_1(sK6,sK5)
    | sK3(sK6,sK0(k2_relat_1(sK6),sK5)) != sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_2766])).

cnf(c_7292,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k1_xboole_0)
    | sK3(sK6,sK0(k2_relat_1(sK6),sK5)) != sK3(sK6,sK0(k2_relat_1(sK6),sK5))
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_7290])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_700,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_716,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_706,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_712,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1014,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_712])).

cnf(c_2572,plain,
    ( r2_hidden(X0,k10_relat_1(X1,k1_xboole_0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_1014])).

cnf(c_3234,plain,
    ( r1_xboole_0(X0,k10_relat_1(X1,k1_xboole_0)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_2572])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_713,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3279,plain,
    ( k4_xboole_0(X0,k10_relat_1(X1,k1_xboole_0)) = X0
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3234,c_713])).

cnf(c_3417,plain,
    ( k4_xboole_0(X0,k10_relat_1(sK6,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_700,c_3279])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_726,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_3422,plain,
    ( k10_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3417,c_726])).

cnf(c_22,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2899,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
    | r2_hidden(X1,k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_246,c_22])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_943,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5,c_4])).

cnf(c_1241,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_0,c_943])).

cnf(c_1020,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1014])).

cnf(c_1498,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1241,c_1020])).

cnf(c_3029,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | X1 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2899,c_1498])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3049,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | X1 != sK0(k10_relat_1(sK6,sK5),X0) ),
    inference(resolution,[status(thm)],[c_3029,c_2])).

cnf(c_3289,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(resolution,[status(thm)],[c_3049,c_4])).

cnf(c_3291,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_3289])).

cnf(c_2771,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
    | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | ~ r1_xboole_0(k10_relat_1(sK6,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2773,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k1_xboole_0)
    | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_243,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2740,plain,
    ( sK3(sK6,sK0(k2_relat_1(sK6),sK5)) = sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_974,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),X1)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1320,plain,
    ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,X0))
    | ~ r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),X0)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_1990,plain,
    ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_701,plain,
    ( k1_xboole_0 = k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1360,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | k4_xboole_0(k2_relat_1(sK6),sK5) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_701,c_713])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_703,plain,
    ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1089,plain,
    ( k10_relat_1(sK6,k4_xboole_0(k2_relat_1(sK6),k4_xboole_0(k2_relat_1(sK6),X0))) = k10_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_700,c_703])).

cnf(c_1491,plain,
    ( k10_relat_1(sK6,k4_xboole_0(k2_relat_1(sK6),k2_relat_1(sK6))) = k10_relat_1(sK6,sK5)
    | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1360,c_1089])).

cnf(c_1492,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | k10_relat_1(sK6,k1_xboole_0) = k10_relat_1(sK6,sK5) ),
    inference(demodulation,[status(thm)],[c_1491,c_726])).

cnf(c_21,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_702,plain,
    ( k1_xboole_0 != k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1495,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | k10_relat_1(sK6,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1492,c_702])).

cnf(c_26,plain,
    ( k1_xboole_0 != k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_58,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_59,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_244,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1520,plain,
    ( k10_relat_1(sK6,sK5) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_1521,plain,
    ( k10_relat_1(sK6,sK5) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK6,sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_1525,plain,
    ( k10_relat_1(sK6,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1495,c_26,c_58,c_59,c_1521])).

cnf(c_1527,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k10_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1525])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_971,plain,
    ( r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
    | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_897,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_894,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_25,plain,
    ( k1_xboole_0 = k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7292,c_3422,c_3291,c_2773,c_2740,c_1990,c_1527,c_1525,c_971,c_897,c_894,c_25,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.79/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/1.00  
% 3.79/1.00  ------  iProver source info
% 3.79/1.00  
% 3.79/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.79/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/1.00  git: non_committed_changes: false
% 3.79/1.00  git: last_make_outside_of_git: false
% 3.79/1.00  
% 3.79/1.00  ------ 
% 3.79/1.00  ------ Parsing...
% 3.79/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/1.00  
% 3.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/1.00  ------ Proving...
% 3.79/1.00  ------ Problem Properties 
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  clauses                                 24
% 3.79/1.00  conjectures                             3
% 3.79/1.00  EPR                                     2
% 3.79/1.00  Horn                                    19
% 3.79/1.00  unary                                   7
% 3.79/1.00  binary                                  9
% 3.79/1.00  lits                                    51
% 3.79/1.00  lits eq                                 15
% 3.79/1.00  fd_pure                                 0
% 3.79/1.00  fd_pseudo                               0
% 3.79/1.00  fd_cond                                 1
% 3.79/1.00  fd_pseudo_cond                          2
% 3.79/1.00  AC symbols                              0
% 3.79/1.00  
% 3.79/1.00  ------ Input Options Time Limit: Unbounded
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  ------ 
% 3.79/1.00  Current options:
% 3.79/1.00  ------ 
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  ------ Proving...
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  % SZS status Theorem for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  fof(f15,conjecture,(
% 3.79/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f16,negated_conjecture,(
% 3.79/1.00    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.79/1.00    inference(negated_conjecture,[],[f15])).
% 3.79/1.00  
% 3.79/1.00  fof(f21,plain,(
% 3.79/1.00    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.79/1.00    inference(ennf_transformation,[],[f16])).
% 3.79/1.00  
% 3.79/1.00  fof(f37,plain,(
% 3.79/1.00    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.79/1.00    inference(nnf_transformation,[],[f21])).
% 3.79/1.00  
% 3.79/1.00  fof(f38,plain,(
% 3.79/1.00    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.79/1.00    inference(flattening,[],[f37])).
% 3.79/1.00  
% 3.79/1.00  fof(f39,plain,(
% 3.79/1.00    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f40,plain,(
% 3.79/1.00    (~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6)),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f39])).
% 3.79/1.00  
% 3.79/1.00  fof(f66,plain,(
% 3.79/1.00    v1_relat_1(sK6)),
% 3.79/1.00    inference(cnf_transformation,[],[f40])).
% 3.79/1.00  
% 3.79/1.00  fof(f1,axiom,(
% 3.79/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f17,plain,(
% 3.79/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.79/1.00    inference(rectify,[],[f1])).
% 3.79/1.00  
% 3.79/1.00  fof(f18,plain,(
% 3.79/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.79/1.00    inference(ennf_transformation,[],[f17])).
% 3.79/1.00  
% 3.79/1.00  fof(f22,plain,(
% 3.79/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f23,plain,(
% 3.79/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).
% 3.79/1.00  
% 3.79/1.00  fof(f42,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f23])).
% 3.79/1.00  
% 3.79/1.00  fof(f13,axiom,(
% 3.79/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f19,plain,(
% 3.79/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.79/1.00    inference(ennf_transformation,[],[f13])).
% 3.79/1.00  
% 3.79/1.00  fof(f33,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.79/1.00    inference(nnf_transformation,[],[f19])).
% 3.79/1.00  
% 3.79/1.00  fof(f34,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.79/1.00    inference(rectify,[],[f33])).
% 3.79/1.00  
% 3.79/1.00  fof(f35,plain,(
% 3.79/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f36,plain,(
% 3.79/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 3.79/1.00  
% 3.79/1.00  fof(f63,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f36])).
% 3.79/1.00  
% 3.79/1.00  fof(f9,axiom,(
% 3.79/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f25,plain,(
% 3.79/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.79/1.00    inference(nnf_transformation,[],[f9])).
% 3.79/1.00  
% 3.79/1.00  fof(f26,plain,(
% 3.79/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.79/1.00    inference(flattening,[],[f25])).
% 3.79/1.00  
% 3.79/1.00  fof(f54,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.79/1.00    inference(cnf_transformation,[],[f26])).
% 3.79/1.00  
% 3.79/1.00  fof(f74,plain,(
% 3.79/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.79/1.00    inference(equality_resolution,[],[f54])).
% 3.79/1.00  
% 3.79/1.00  fof(f10,axiom,(
% 3.79/1.00    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f55,plain,(
% 3.79/1.00    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.79/1.00    inference(cnf_transformation,[],[f10])).
% 3.79/1.00  
% 3.79/1.00  fof(f5,axiom,(
% 3.79/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f24,plain,(
% 3.79/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.79/1.00    inference(nnf_transformation,[],[f5])).
% 3.79/1.00  
% 3.79/1.00  fof(f47,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f24])).
% 3.79/1.00  
% 3.79/1.00  fof(f2,axiom,(
% 3.79/1.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f44,plain,(
% 3.79/1.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f2])).
% 3.79/1.00  
% 3.79/1.00  fof(f4,axiom,(
% 3.79/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f46,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.79/1.00    inference(cnf_transformation,[],[f4])).
% 3.79/1.00  
% 3.79/1.00  fof(f71,plain,(
% 3.79/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.79/1.00    inference(definition_unfolding,[],[f44,f46])).
% 3.79/1.00  
% 3.79/1.00  fof(f3,axiom,(
% 3.79/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f45,plain,(
% 3.79/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.79/1.00    inference(cnf_transformation,[],[f3])).
% 3.79/1.00  
% 3.79/1.00  fof(f67,plain,(
% 3.79/1.00    r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)),
% 3.79/1.00    inference(cnf_transformation,[],[f40])).
% 3.79/1.00  
% 3.79/1.00  fof(f43,plain,(
% 3.79/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f23])).
% 3.79/1.00  
% 3.79/1.00  fof(f48,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.79/1.00    inference(cnf_transformation,[],[f24])).
% 3.79/1.00  
% 3.79/1.00  fof(f41,plain,(
% 3.79/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f23])).
% 3.79/1.00  
% 3.79/1.00  fof(f64,plain,(
% 3.79/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f36])).
% 3.79/1.00  
% 3.79/1.00  fof(f14,axiom,(
% 3.79/1.00    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f20,plain,(
% 3.79/1.00    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.79/1.00    inference(ennf_transformation,[],[f14])).
% 3.79/1.00  
% 3.79/1.00  fof(f65,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f20])).
% 3.79/1.00  
% 3.79/1.00  fof(f73,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 3.79/1.00    inference(definition_unfolding,[],[f65,f46])).
% 3.79/1.00  
% 3.79/1.00  fof(f68,plain,(
% 3.79/1.00    ~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)),
% 3.79/1.00    inference(cnf_transformation,[],[f40])).
% 3.79/1.00  
% 3.79/1.00  fof(f52,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.79/1.00    inference(cnf_transformation,[],[f26])).
% 3.79/1.00  
% 3.79/1.00  fof(f53,plain,(
% 3.79/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.79/1.00    inference(cnf_transformation,[],[f26])).
% 3.79/1.00  
% 3.79/1.00  fof(f75,plain,(
% 3.79/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.79/1.00    inference(equality_resolution,[],[f53])).
% 3.79/1.00  
% 3.79/1.00  fof(f12,axiom,(
% 3.79/1.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.00  
% 3.79/1.00  fof(f27,plain,(
% 3.79/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.79/1.00    inference(nnf_transformation,[],[f12])).
% 3.79/1.00  
% 3.79/1.00  fof(f28,plain,(
% 3.79/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.79/1.00    inference(rectify,[],[f27])).
% 3.79/1.00  
% 3.79/1.00  fof(f31,plain,(
% 3.79/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f30,plain,(
% 3.79/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f29,plain,(
% 3.79/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.79/1.00    introduced(choice_axiom,[])).
% 3.79/1.00  
% 3.79/1.00  fof(f32,plain,(
% 3.79/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).
% 3.79/1.00  
% 3.79/1.00  fof(f57,plain,(
% 3.79/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.79/1.00    inference(cnf_transformation,[],[f32])).
% 3.79/1.00  
% 3.79/1.00  fof(f77,plain,(
% 3.79/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.79/1.00    inference(equality_resolution,[],[f57])).
% 3.79/1.00  
% 3.79/1.00  cnf(c_246,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.79/1.00      theory(equality) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2766,plain,
% 3.79/1.00      ( r2_hidden(X0,X1)
% 3.79/1.00      | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 3.79/1.00      | X1 != k10_relat_1(sK6,sK5)
% 3.79/1.00      | X0 != sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_246]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7290,plain,
% 3.79/1.00      ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
% 3.79/1.00      | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 3.79/1.00      | X0 != k10_relat_1(sK6,sK5)
% 3.79/1.00      | sK3(sK6,sK0(k2_relat_1(sK6),sK5)) != sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2766]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7292,plain,
% 3.79/1.00      ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 3.79/1.00      | r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k1_xboole_0)
% 3.79/1.00      | sK3(sK6,sK0(k2_relat_1(sK6),sK5)) != sK3(sK6,sK0(k2_relat_1(sK6),sK5))
% 3.79/1.00      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_7290]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_23,negated_conjecture,
% 3.79/1.00      ( v1_relat_1(sK6) ),
% 3.79/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_700,plain,
% 3.79/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1,plain,
% 3.79/1.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_716,plain,
% 3.79/1.00      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.79/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_17,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.79/1.00      | r2_hidden(sK4(X0,X2,X1),X2)
% 3.79/1.00      | ~ v1_relat_1(X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_706,plain,
% 3.79/1.00      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.79/1.00      | r2_hidden(sK4(X0,X2,X1),X2) = iProver_top
% 3.79/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_7,plain,
% 3.79/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_10,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.79/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_712,plain,
% 3.79/1.00      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1014,plain,
% 3.79/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_7,c_712]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2572,plain,
% 3.79/1.00      ( r2_hidden(X0,k10_relat_1(X1,k1_xboole_0)) != iProver_top
% 3.79/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_706,c_1014]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3234,plain,
% 3.79/1.00      ( r1_xboole_0(X0,k10_relat_1(X1,k1_xboole_0)) = iProver_top
% 3.79/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_716,c_2572]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_6,plain,
% 3.79/1.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_713,plain,
% 3.79/1.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3279,plain,
% 3.79/1.00      ( k4_xboole_0(X0,k10_relat_1(X1,k1_xboole_0)) = X0
% 3.79/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_3234,c_713]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3417,plain,
% 3.79/1.00      ( k4_xboole_0(X0,k10_relat_1(sK6,k1_xboole_0)) = X0 ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_700,c_3279]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3,plain,
% 3.79/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_4,plain,
% 3.79/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_726,plain,
% 3.79/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.79/1.00      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3422,plain,
% 3.79/1.00      ( k10_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_3417,c_726]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_22,negated_conjecture,
% 3.79/1.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 3.79/1.00      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 3.79/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2899,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
% 3.79/1.00      | r2_hidden(X1,k1_xboole_0)
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 3.79/1.00      | X1 != X0 ),
% 3.79/1.00      inference(resolution,[status(thm)],[c_246,c_22]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_0,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_5,plain,
% 3.79/1.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_943,plain,
% 3.79/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.79/1.00      inference(resolution,[status(thm)],[c_5,c_4]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1241,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.79/1.00      inference(resolution,[status(thm)],[c_0,c_943]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1020,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.79/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1014]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1498,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_1241,c_1020]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3029,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 3.79/1.00      | X1 != X0 ),
% 3.79/1.00      inference(forward_subsumption_resolution,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_2899,c_1498]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2,plain,
% 3.79/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3049,plain,
% 3.79/1.00      ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 3.79/1.00      | X1 != sK0(k10_relat_1(sK6,sK5),X0) ),
% 3.79/1.00      inference(resolution,[status(thm)],[c_3029,c_2]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3289,plain,
% 3.79/1.00      ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 3.79/1.00      inference(resolution,[status(thm)],[c_3049,c_4]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_3291,plain,
% 3.79/1.00      ( r1_xboole_0(k10_relat_1(sK6,sK5),k1_xboole_0)
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_3289]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2771,plain,
% 3.79/1.00      ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),X0)
% 3.79/1.00      | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 3.79/1.00      | ~ r1_xboole_0(k10_relat_1(sK6,sK5),X0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2773,plain,
% 3.79/1.00      ( ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 3.79/1.00      | ~ r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k1_xboole_0)
% 3.79/1.00      | ~ r1_xboole_0(k10_relat_1(sK6,sK5),k1_xboole_0) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2771]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_243,plain,( X0 = X0 ),theory(equality) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_2740,plain,
% 3.79/1.00      ( sK3(sK6,sK0(k2_relat_1(sK6),sK5)) = sK3(sK6,sK0(k2_relat_1(sK6),sK5)) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_243]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_16,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,X1)
% 3.79/1.00      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.79/1.00      | ~ r2_hidden(X0,k2_relat_1(X3))
% 3.79/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.79/1.00      | ~ v1_relat_1(X3) ),
% 3.79/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_974,plain,
% 3.79/1.00      ( r2_hidden(X0,k10_relat_1(sK6,X1))
% 3.79/1.00      | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK6),sK5)),sK6)
% 3.79/1.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),X1)
% 3.79/1.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 3.79/1.00      | ~ v1_relat_1(sK6) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1320,plain,
% 3.79/1.00      ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,X0))
% 3.79/1.00      | ~ r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
% 3.79/1.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),X0)
% 3.79/1.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 3.79/1.00      | ~ v1_relat_1(sK6) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_974]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1990,plain,
% 3.79/1.00      ( r2_hidden(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),k10_relat_1(sK6,sK5))
% 3.79/1.00      | ~ r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
% 3.79/1.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 3.79/1.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 3.79/1.00      | ~ v1_relat_1(sK6) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1320]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_701,plain,
% 3.79/1.00      ( k1_xboole_0 = k10_relat_1(sK6,sK5)
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1360,plain,
% 3.79/1.00      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 3.79/1.00      | k4_xboole_0(k2_relat_1(sK6),sK5) = k2_relat_1(sK6) ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_701,c_713]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_20,plain,
% 3.79/1.00      ( ~ v1_relat_1(X0)
% 3.79/1.00      | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_703,plain,
% 3.79/1.00      ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 3.79/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1089,plain,
% 3.79/1.00      ( k10_relat_1(sK6,k4_xboole_0(k2_relat_1(sK6),k4_xboole_0(k2_relat_1(sK6),X0))) = k10_relat_1(sK6,X0) ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_700,c_703]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1491,plain,
% 3.79/1.00      ( k10_relat_1(sK6,k4_xboole_0(k2_relat_1(sK6),k2_relat_1(sK6))) = k10_relat_1(sK6,sK5)
% 3.79/1.00      | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_1360,c_1089]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1492,plain,
% 3.79/1.00      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 3.79/1.00      | k10_relat_1(sK6,k1_xboole_0) = k10_relat_1(sK6,sK5) ),
% 3.79/1.00      inference(demodulation,[status(thm)],[c_1491,c_726]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_21,negated_conjecture,
% 3.79/1.00      ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
% 3.79/1.00      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 3.79/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_702,plain,
% 3.79/1.00      ( k1_xboole_0 != k10_relat_1(sK6,sK5)
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1495,plain,
% 3.79/1.00      ( k10_relat_1(sK6,sK5) = k1_xboole_0
% 3.79/1.00      | k10_relat_1(sK6,k1_xboole_0) != k1_xboole_0
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 3.79/1.00      inference(superposition,[status(thm)],[c_1492,c_702]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_26,plain,
% 3.79/1.00      ( k1_xboole_0 != k10_relat_1(sK6,sK5)
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_9,plain,
% 3.79/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.79/1.00      | k1_xboole_0 = X1
% 3.79/1.00      | k1_xboole_0 = X0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_58,plain,
% 3.79/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.79/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_8,plain,
% 3.79/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.79/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_59,plain,
% 3.79/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_244,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1520,plain,
% 3.79/1.00      ( k10_relat_1(sK6,sK5) != X0
% 3.79/1.00      | k1_xboole_0 != X0
% 3.79/1.00      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_244]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1521,plain,
% 3.79/1.00      ( k10_relat_1(sK6,sK5) != k1_xboole_0
% 3.79/1.00      | k1_xboole_0 = k10_relat_1(sK6,sK5)
% 3.79/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1520]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1525,plain,
% 3.79/1.00      ( k10_relat_1(sK6,k1_xboole_0) != k1_xboole_0
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
% 3.79/1.00      inference(global_propositional_subsumption,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_1495,c_26,c_58,c_59,c_1521]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_1527,plain,
% 3.79/1.00      ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
% 3.79/1.00      | k10_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.79/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1525]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_15,plain,
% 3.79/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.79/1.00      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 3.79/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_971,plain,
% 3.79/1.00      ( r2_hidden(k4_tarski(sK3(sK6,sK0(k2_relat_1(sK6),sK5)),sK0(k2_relat_1(sK6),sK5)),sK6)
% 3.79/1.00      | ~ r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_897,plain,
% 3.79/1.00      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6))
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_894,plain,
% 3.79/1.00      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5)
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 3.79/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(c_25,plain,
% 3.79/1.00      ( k1_xboole_0 = k10_relat_1(sK6,sK5)
% 3.79/1.00      | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.79/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.79/1.00  
% 3.79/1.00  cnf(contradiction,plain,
% 3.79/1.00      ( $false ),
% 3.79/1.00      inference(minisat,
% 3.79/1.00                [status(thm)],
% 3.79/1.00                [c_7292,c_3422,c_3291,c_2773,c_2740,c_1990,c_1527,c_1525,
% 3.79/1.00                 c_971,c_897,c_894,c_25,c_23]) ).
% 3.79/1.00  
% 3.79/1.00  
% 3.79/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/1.00  
% 3.79/1.00  ------                               Statistics
% 3.79/1.00  
% 3.79/1.00  ------ Selected
% 3.79/1.00  
% 3.79/1.00  total_time:                             0.322
% 3.79/1.00  
%------------------------------------------------------------------------------
